package saml

import (
	"bytes"
	"compress/flate"
	"crypto"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/xml"
	"errors"
	"fmt"
	"html/template"
	"net/http"
	"net/url"
	"regexp"
	"time"

	"github.com/beevik/etree"
	dsig "github.com/russellhaering/goxmldsig"
	"github.com/russellhaering/goxmldsig/etreeutils"

	"github.com/vereignag/saml/xmlenc"
)

// NameIDFormat is the format of the id
type NameIDFormat string

// Element returns an XML element representation of n.
func (n NameIDFormat) Element() *etree.Element {
	el := etree.NewElement("")
	el.SetText(string(n))
	return el
}

// Name ID formats
const (
	UnspecifiedNameIDFormat  NameIDFormat = "urn:oasis:names:tc:SAML:1.1:nameid-format:unspecified"
	TransientNameIDFormat    NameIDFormat = "urn:oasis:names:tc:SAML:2.0:nameid-format:transient"
	EmailAddressNameIDFormat NameIDFormat = "urn:oasis:names:tc:SAML:1.1:nameid-format:emailAddress"
	PersistentNameIDFormat   NameIDFormat = "urn:oasis:names:tc:SAML:2.0:nameid-format:persistent"
)

// SignatureVerifier verifies a signature
//
// Can be implemented in order to override ServiceProvider's default
// way of verifying signatures.
type SignatureVerifier interface {
	VerifySignature(validationContext *dsig.ValidationContext, el *etree.Element) error
}

// ServiceProvider implements SAML Service provider.
//
// In SAML, service providers delegate responsibility for identifying
// clients to an identity provider. If you are writing an application
// that uses passwords (or whatever) stored somewhere else, then you
// are service provider.
//
// See the example directory for an example of a web application using
// the service provider interface.
type ServiceProvider struct {
	// Entity ID is optional - if not specified then MetadataURL will be used
	EntityID string

	// Key is the RSA private key we use to sign requests.
	Key crypto.PrivateKey

	// Certificate is the RSA public part of Key.
	Certificate   *x509.Certificate
	Intermediates []*x509.Certificate

	// MetadataURL is the full URL to the metadata endpoint on this host,
	// i.e. https://example.com/saml/metadata
	MetadataURL url.URL

	// AcsURL is the full URL to the SAML Assertion Customer Service endpoint
	// on this host, i.e. https://example.com/saml/acs
	AcsURL url.URL

	// SloURL is the full URL to the SAML Single Logout endpoint on this host.
	// i.e. https://example.com/saml/slo
	SloURL url.URL

	// IDPMetadata is the metadata from the identity provider.
	IDPMetadata *EntityDescriptor

	// AuthnNameIDFormat is the format used in the NameIDPolicy for
	// authentication requests
	AuthnNameIDFormat NameIDFormat

	// MetadataValidDuration is a duration used to calculate validUntil
	// attribute in the metadata endpoint
	MetadataValidDuration time.Duration

	// ForceAuthn allows you to force re-authentication of users even if the user
	// has a SSO session at the IdP.
	ForceAuthn *bool

	// AllowIdpInitiated
	AllowIDPInitiated bool

	// SignatureVerifier, if non-nil, allows you to implement an alternative way
	// to verify signatures.
	SignatureVerifier SignatureVerifier

	// Used to determine if service provider should sign requests. If not set defaults to IDP WantAuthnRequestsSigned
	SignRequests *bool

	// Private key we use to sign requests. If not set defaults to Key
	SigningKey crypto.PrivateKey

	// Certificate for the "signing" key descriptor in metadata. If not set defaults to Certificate
	SigningCertificate *x509.Certificate

	// Signing algorithm. If not set defaults to http://www.w3.org/2000/09/xmldsig#rsa-sha1, value of dsig.RSASHA1SignatureMethod
	SigningAlgorithm string //TODO rename??

	// Signing canonicalizer. If not set defaults to canonicalization algorithm http://www.w3.org/2001/10/xml-exc-c14n#, value of dsig.MakeC14N10ExclusiveCanonicalizerWithPrefixList("")
	SigningCanonicalizer dsig.Canonicalizer

	// Private key we use to decrypt responses. If not set defaults to Key
	EncryptionKey crypto.PrivateKey

	// Certificate for the "encryption" key descriptor in metadata. If not set defaults to Certificate
	EncryptionCertificate *x509.Certificate
}

// MaxIssueDelay is the longest allowed time between when a SAML assertion is
// issued by the IDP and the time it is received by ParseResponse. This is used
// to prevent old responses from being replayed (while allowing for some clock
// drift between the SP and IDP).
var MaxIssueDelay = time.Second * 90

// MaxClockSkew allows for leeway for clock skew between the IDP and SP when
// validating assertions. It defaults to 180 seconds (matches shibboleth).
var MaxClockSkew = time.Second * 180

// DefaultValidDuration is how long we assert that the SP metadata is valid.
const DefaultValidDuration = time.Hour * 24 * 2

// DefaultCacheDuration is how long we ask the IDP to cache the SP metadata.
const DefaultCacheDuration = time.Hour * 24 * 1

// Metadata returns the service provider metadata
func (sp *ServiceProvider) Metadata() *EntityDescriptor {
	validDuration := DefaultValidDuration
	if sp.MetadataValidDuration > 0 {
		validDuration = sp.MetadataValidDuration
	}

	authnRequestsSigned := false
	if sp.SignRequests != nil {
		authnRequestsSigned = *sp.SignRequests
	} else {
		for idpIdx := range sp.IDPMetadata.IDPSSODescriptors {
			if sp.ShouldSignRequest(&sp.IDPMetadata.IDPSSODescriptors[idpIdx]) {
				authnRequestsSigned = true
				break
			}
		}
	}

	wantAssertionsSigned := true
	validUntil := TimeNow().Add(validDuration)

	var keyDescriptors []KeyDescriptor
	signingCertificate := sp.signingCertificate()
	encryptionCertificate := sp.encryptionCertificate()
	if signingCertificate != nil || encryptionCertificate != nil {
		var intermediatesBytes []byte
		for _, intermediate := range sp.Intermediates {
			intermediatesBytes = append(intermediatesBytes, intermediate.Raw...)
		}
		if signingCertificate != nil {
			certBytes := append(signingCertificate.Raw, intermediatesBytes...)
			keyDescriptors = append(keyDescriptors, KeyDescriptor{
				Use: "signing",
				KeyInfo: KeyInfo{
					Certificate: base64.StdEncoding.EncodeToString(certBytes),
				},
			})
		}
		if encryptionCertificate != nil {
			certBytes := append(encryptionCertificate.Raw, intermediatesBytes...)
			keyDescriptors = append(keyDescriptors, KeyDescriptor{
				Use: "encryption",
				KeyInfo: KeyInfo{
					Certificate: base64.StdEncoding.EncodeToString(certBytes),
				},
				EncryptionMethods: []EncryptionMethod{
					{Algorithm: "http://www.w3.org/2001/04/xmlenc#aes128-cbc"},
					{Algorithm: "http://www.w3.org/2001/04/xmlenc#aes192-cbc"},
					{Algorithm: "http://www.w3.org/2001/04/xmlenc#aes256-cbc"},
					{Algorithm: "http://www.w3.org/2001/04/xmlenc#rsa-oaep-mgf1p"},
				},
			})
		}
	}

	return &EntityDescriptor{
		EntityID:   firstSet(sp.EntityID, sp.MetadataURL.String()),
		ValidUntil: validUntil,

		SPSSODescriptors: []SPSSODescriptor{
			{
				SSODescriptor: SSODescriptor{
					RoleDescriptor: RoleDescriptor{
						ProtocolSupportEnumeration: "urn:oasis:names:tc:SAML:2.0:protocol",
						KeyDescriptors:             keyDescriptors,
						ValidUntil:                 &validUntil,
					},
					SingleLogoutServices: []Endpoint{
						{
							Binding:          HTTPPostBinding,
							Location:         sp.SloURL.String(),
							ResponseLocation: sp.SloURL.String(),
						},
					},
				},
				AuthnRequestsSigned:  &authnRequestsSigned,
				WantAssertionsSigned: &wantAssertionsSigned,

				AssertionConsumerServices: []IndexedEndpoint{
					{
						Binding:  HTTPPostBinding,
						Location: sp.AcsURL.String(),
						Index:    1,
					},
				},
			},
		},
	}
}

// MakeRedirectAuthenticationRequest creates a SAML authentication request using
// the HTTP-Redirect binding. It returns a URL that we will redirect the user to
// in order to start the auth process.
func (sp *ServiceProvider) MakeRedirectAuthenticationRequest(relayState string) (*url.URL, error) {
	idpSSODescriptor, idpURL := sp.GetSSOBindingLocation(HTTPRedirectBinding)
	req, err := sp.MakeAuthenticationRequest(idpURL)
	if err != nil {
		return nil, err
	}
	redirectURL := req.Redirect(relayState)
	if sp.ShouldSignRequest(idpSSODescriptor) {
		err = sp.SignRedirectRequestURL(redirectURL)
		if err != nil {
			return nil, err
		}
	}
	return redirectURL, nil
}

// Redirect returns a URL suitable for using the redirect binding with the request
func (req *AuthnRequest) Redirect(relayState string) *url.URL {
	w := &bytes.Buffer{}
	w1 := base64.NewEncoder(base64.StdEncoding, w)
	w2, _ := flate.NewWriter(w1, flate.BestCompression)
	doc := etree.NewDocument()
	doc.SetRoot(req.Element())
	if _, err := doc.WriteTo(w2); err != nil {
		panic(err)
	}
	w2.Close()
	w1.Close()

	rv, _ := url.Parse(req.Destination)

	query := rv.Query()
	query.Set("SAMLRequest", string(w.Bytes()))
	if relayState != "" {
		query.Set("RelayState", relayState)
	}
	rv.RawQuery = query.Encode()

	return rv
}

// GetSSOBindingLocation returns URL for the IDP's Single Sign On Service binding
// of the specified type (HTTPRedirectBinding or HTTPPostBinding)
func (sp *ServiceProvider) GetSSOBindingLocation(binding string) (*IDPSSODescriptor, string) {
	for idpIdx, idpSSODescriptor := range sp.IDPMetadata.IDPSSODescriptors {
		for _, singleSignOnService := range idpSSODescriptor.SingleSignOnServices {
			if singleSignOnService.Binding == binding {
				return &sp.IDPMetadata.IDPSSODescriptors[idpIdx], singleSignOnService.Location
			}
		}
	}
	return nil, ""
}

// GetSLOBindingLocation returns URL for the IDP's Single Log Out Service binding
// of the specified type (HTTPRedirectBinding or HTTPPostBinding)
func (sp *ServiceProvider) GetSLOBindingLocation(binding string) (*IDPSSODescriptor, string) {
	for idpIdx, idpSSODescriptor := range sp.IDPMetadata.IDPSSODescriptors {
		for _, singleLogoutService := range idpSSODescriptor.SingleLogoutServices {
			if singleLogoutService.Binding == binding {
				return &sp.IDPMetadata.IDPSSODescriptors[idpIdx], singleLogoutService.Location
			}
		}
	}
	return nil, ""
}

// getIDPSigningCerts returns the certificates which we can use to verify things
// signed by the IDP in PEM format, or nil if no such certificate is found.
func (sp *ServiceProvider) getIDPSigningCerts() ([]*x509.Certificate, error) {
	var certStrs []string
	for _, idpSSODescriptor := range sp.IDPMetadata.IDPSSODescriptors {
		for _, keyDescriptor := range idpSSODescriptor.KeyDescriptors {
			if keyDescriptor.Use == "signing" {
				certStrs = append(certStrs, keyDescriptor.KeyInfo.Certificate)
			}
		}
	}

	// If there are no explicitly signing certs, just return the first
	// non-empty cert we find.
	if len(certStrs) == 0 {
		for _, idpSSODescriptor := range sp.IDPMetadata.IDPSSODescriptors {
			for _, keyDescriptor := range idpSSODescriptor.KeyDescriptors {
				if keyDescriptor.Use == "" && keyDescriptor.KeyInfo.Certificate != "" {
					certStrs = append(certStrs, keyDescriptor.KeyInfo.Certificate)
					break
				}
			}
		}
	}

	if len(certStrs) == 0 {
		return nil, errors.New("cannot find any signing certificate in the IDP SSO descriptor")
	}

	var certs []*x509.Certificate

	// cleanup whitespace
	regex := regexp.MustCompile(`\s+`)
	for _, certStr := range certStrs {
		certStr = regex.ReplaceAllString(certStr, "")
		certBytes, err := base64.StdEncoding.DecodeString(certStr)
		if err != nil {
			return nil, fmt.Errorf("cannot parse certificate: %s", err)
		}

		parsedCert, err := x509.ParseCertificate(certBytes)
		if err != nil {
			return nil, err
		}
		certs = append(certs, parsedCert)
	}

	return certs, nil
}

// MakeAuthenticationRequest produces a new AuthnRequest object for idpURL.
func (sp *ServiceProvider) MakeAuthenticationRequest(idpURL string) (*AuthnRequest, error) {

	allowCreate := true
	nameIDFormat := sp.nameIDFormat()
	req := AuthnRequest{
		AssertionConsumerServiceURL: sp.AcsURL.String(),
		Destination:                 idpURL,
		ProtocolBinding:             HTTPPostBinding, // default binding for the response
		ID:                          fmt.Sprintf("id-%x", randomBytes(20)),
		IssueInstant:                TimeNow(),
		Version:                     "2.0",
		Issuer: &Issuer{
			Format: "urn:oasis:names:tc:SAML:2.0:nameid-format:entity",
			Value:  firstSet(sp.EntityID, sp.MetadataURL.String()),
		},
		NameIDPolicy: &NameIDPolicy{
			AllowCreate: &allowCreate,
			// TODO(ross): figure out exactly policy we need
			// urn:mace:shibboleth:1.0:nameIdentifier
			// urn:oasis:names:tc:SAML:2.0:nameid-format:transient
			Format: &nameIDFormat,
		},
		ForceAuthn: sp.ForceAuthn,
	}
	return &req, nil
}

// MakePostAuthenticationRequest creates a SAML authentication request using
// the HTTP-POST binding. It returns HTML text representing an HTML form that
// can be sent presented to a browser to initiate the login process.
func (sp *ServiceProvider) MakePostAuthenticationRequest(relayState string) ([]byte, error) {
	idpSSODescriptor, idpURL := sp.GetSSOBindingLocation(HTTPPostBinding)
	req, err := sp.MakeAuthenticationRequest(idpURL)
	if err != nil {
		return nil, err
	}
	if sp.ShouldSignRequest(idpSSODescriptor) {
		err = sp.SignPostAuthnRequest(req)
		if err != nil {
			return nil, err
		}
	}
	return req.Post(relayState), nil
}

func (req *AuthnRequest) PostTemplateData(relayState string) *RequestTemplateData {
	doc := etree.NewDocument()
	doc.SetRoot(req.Element())
	reqBuf, err := doc.WriteToBytes()
	if err != nil {
		panic(err)
	}

	encodedReqBuf := base64.StdEncoding.EncodeToString(reqBuf)

	return &RequestTemplateData{
		URL:         req.Destination,
		SAMLRequest: encodedReqBuf,
		RelayState:  relayState,
	}
}

// Post returns an HTML form suitable for using the HTTP-POST binding with the request
func (req *AuthnRequest) Post(relayState string) []byte {
	td := req.PostTemplateData(relayState)
	rv, err := td.ExecuteTemplate(DefaultRequestTemplate)
	if err != nil {
		panic(err)
	}
	return rv
}

// AssertionAttributes is a list of AssertionAttribute
type AssertionAttributes []AssertionAttribute

// Get returns the assertion attribute whose Name or FriendlyName
// matches name, or nil if no matching attribute is found.
func (aa AssertionAttributes) Get(name string) *AssertionAttribute {
	for _, attr := range aa {
		if attr.Name == name {
			return &attr
		}
		if attr.FriendlyName == name {
			return &attr
		}
	}
	return nil
}

// AssertionAttribute represents an attribute of the user extracted from
// a SAML Assertion.
type AssertionAttribute struct {
	FriendlyName string
	Name         string
	Value        string
}

// InvalidResponseError is the error produced by ParseResponse when it fails.
// The underlying error is in PrivateErr. Response is the response as it was
// known at the time validation failed. Now is the time that was used to validate
// time-dependent parts of the assertion.
type InvalidResponseError struct {
	PrivateErr error
	Response   string
	Now        time.Time
}

func (ivr *InvalidResponseError) Error() string {
	return fmt.Sprintf("Authentication failed")
}

// ErrBadStatus is returned when the assertion provided is valid but the
// status code is not "urn:oasis:names:tc:SAML:2.0:status:Success".
type ErrBadStatus struct {
	Status string
}

func (e ErrBadStatus) Error() string {
	return e.Status
}

func responseIsSigned(response *etree.Document) (bool, error) {
	signatureElement, err := findChild(response.Root(), "http://www.w3.org/2000/09/xmldsig#", "Signature")
	if err != nil {
		return false, err
	}
	return signatureElement != nil, nil
}

// validateDestination validates the Destination attribute.
// If the response is signed, the Destination is required to be present.
func (sp *ServiceProvider) validateDestination(response []byte, responseDom *Response) error {
	responseXML := etree.NewDocument()
	err := responseXML.ReadFromBytes(response)
	if err != nil {
		return err
	}

	signed, err := responseIsSigned(responseXML)
	if err != nil {
		return err
	}

	// Compare if the response is signed OR the Destination is provided.
	// (Even if the response is not signed, if the Destination is set it must match.)
	if signed || responseDom.Destination != "" {
		if responseDom.Destination != sp.AcsURL.String() {
			return fmt.Errorf("`Destination` does not match AcsURL (expected %q, actual %q)", sp.AcsURL.String(), responseDom.Destination)
		}
	}

	return nil
}

// ParseResponse extracts the SAML IDP response received in req, validates
// it, and returns the verified assertion.
func (sp *ServiceProvider) ParseResponse(req *http.Request, possibleRequestIDs []string) (*Assertion, error) {
	_, resp, _, err := sp.ParseResponseExt(req, possibleRequestIDs)
	if err != nil {
		return nil, err
	}
	return resp.Assertion, nil
}

// ParseResponse extracts the SAML IDP response received in req, validates
// it, and returns the extracted response XML string, response object, along with decrypted assertion XML string (if it was encrypted in the first place).
func (sp *ServiceProvider) ParseResponseExt(req *http.Request, possibleRequestIDs []string) (string, *Response, string, error) {
	now := TimeNow()
	retErr := &InvalidResponseError{
		Now:      now,
		Response: req.PostForm.Get("SAMLResponse"),
	}

	rawResponseBuf, err := base64.StdEncoding.DecodeString(req.PostForm.Get("SAMLResponse"))
	if err != nil {
		retErr.PrivateErr = fmt.Errorf("cannot parse base64: %s", err)
		return "", nil, "", retErr
	}
	responseXMLString := string(rawResponseBuf)
	retErr.Response = responseXMLString

	resp, decryptedAssertion, err := sp.ParseXMLResponseExt(rawResponseBuf, possibleRequestIDs)
	if err != nil {
		retErr.PrivateErr = err
		return "", nil, "", retErr
	}

	return responseXMLString, resp, decryptedAssertion, nil
}

// ParseXMLResponse validates the SAML IDP response and
// returns the verified assertion.
//
// This function handles decrypting the message, verifying the digital
// signature on the assertion, and verifying that the specified conditions
// and properties are met.
//
// If the function fails it will return an InvalidResponseError whose
// properties are useful in describing which part of the parsing process
// failed. However, to discourage inadvertent disclosure the diagnostic
// information, the Error() method returns a static string.
func (sp *ServiceProvider) ParseXMLResponse(decodedResponseXML []byte, possibleRequestIDs []string) (*Assertion, error) {
	resp, _, err := sp.ParseXMLResponseExt(decodedResponseXML, possibleRequestIDs)
	if err != nil {
		return nil, err
	}
	return resp.Assertion, nil
}

// ParseXMLResponse validates the SAML IDP response and
// returns the response object, along with decrypted assertion XML string (if it was encrypted in the first place).
//
// This function handles decrypting the message, verifying the digital
// signature on the assertion, and verifying that the specified conditions
// and properties are met.
//
// If the function fails it will return an InvalidResponseError whose
// properties are useful in describing which part of the parsing process
// failed. However, to discourage inadvertent disclosure the diagnostic
// information, the Error() method returns a static string.
func (sp *ServiceProvider) ParseXMLResponseExt(decodedResponseXML []byte, possibleRequestIDs []string) (*Response, string, error) {
	now := TimeNow()
	var err error
	retErr := &InvalidResponseError{
		Now:      now,
		Response: string(decodedResponseXML),
	}

	// do some validation first before we decrypt
	resp := &Response{}
	if err := xml.Unmarshal([]byte(decodedResponseXML), resp); err != nil {
		retErr.PrivateErr = fmt.Errorf("cannot unmarshal response: %s", err)
		return nil, "", retErr
	}

	if err := sp.validateDestination(decodedResponseXML, resp); err != nil {
		retErr.PrivateErr = err
		return nil, "", retErr
	}

	requestIDvalid := false

	if sp.AllowIDPInitiated {
		requestIDvalid = true
	} else {
		for _, possibleRequestID := range possibleRequestIDs {
			if resp.InResponseTo == possibleRequestID {
				requestIDvalid = true
			}
		}
	}

	if !requestIDvalid {
		retErr.PrivateErr = fmt.Errorf("`InResponseTo` does not match any of the possible request IDs (expected %v)", possibleRequestIDs)
		return nil, "", retErr
	}

	if resp.IssueInstant.Add(MaxIssueDelay).Before(now) {
		retErr.PrivateErr = fmt.Errorf("response IssueInstant expired at %s", resp.IssueInstant.Add(MaxIssueDelay))
		return nil, "", retErr
	}
	if resp.Issuer.Value != sp.IDPMetadata.EntityID {
		retErr.PrivateErr = fmt.Errorf("response Issuer does not match the IDP metadata (expected %q)", sp.IDPMetadata.EntityID)
		return nil, "", retErr
	}
	if resp.Status.StatusCode.Value != StatusSuccess {
		retErr.PrivateErr = ErrBadStatus{Status: resp.Status.StatusCode.Value}
		return nil, "", retErr
	}

	var assertion *Assertion
	var decryptedAssertion string
	if resp.EncryptedAssertion == nil {

		doc := etree.NewDocument()
		if err := doc.ReadFromBytes(decodedResponseXML); err != nil {
			retErr.PrivateErr = err
			return nil, "", retErr
		}

		// TODO(ross): verify that the namespace is urn:oasis:names:tc:SAML:2.0:protocol
		responseEl := doc.Root()
		if responseEl.Tag != "Response" {
			retErr.PrivateErr = fmt.Errorf("expected to find a response object, not %s", doc.Root().Tag)
			return nil, "", retErr
		}

		if err = sp.validateSigned(responseEl); err != nil {
			retErr.PrivateErr = err
			return nil, "", retErr
		}

		assertion = resp.Assertion
	}

	// decrypt the response
	if resp.EncryptedAssertion != nil {
		var key interface{} = sp.encryptionKey()
		if key == nil {
			retErr.PrivateErr = errors.New("no encryption key set")
			return nil, "", retErr
		}

		doc := etree.NewDocument()
		if err := doc.ReadFromBytes(decodedResponseXML); err != nil {
			retErr.PrivateErr = err
			return nil, "", retErr
		}

		keyEl := doc.FindElement("//EncryptedAssertion/EncryptedKey")
		if keyEl != nil {
			key, err = xmlenc.Decrypt(key, keyEl)
			if err != nil {
				retErr.PrivateErr = fmt.Errorf("failed to decrypt key from response: %s", err)
				return nil, "", retErr
			}
		}

		el := doc.FindElement("//EncryptedAssertion/EncryptedData")
		plaintextAssertion, err := xmlenc.Decrypt(key, el)
		if err != nil {
			retErr.PrivateErr = fmt.Errorf("failed to decrypt response: %s", err)
			return nil, "", retErr
		}

		decryptedAssertion = string(plaintextAssertion)
		retErr.Response = decryptedAssertion

		doc = etree.NewDocument()
		if err := doc.ReadFromBytes(plaintextAssertion); err != nil {
			retErr.PrivateErr = fmt.Errorf("cannot parse plaintext response %v", err)
			return nil, "", retErr
		}

		if err := sp.validateSigned(doc.Root()); err != nil {
			retErr.PrivateErr = err
			return nil, "", retErr
		}

		assertion = &Assertion{}
		if err := xml.Unmarshal(plaintextAssertion, assertion); err != nil {
			retErr.PrivateErr = err
			return nil, "", retErr
		}

		resp.Assertion = assertion
	}

	if err := sp.validateAssertion(assertion, possibleRequestIDs, now); err != nil {
		retErr.PrivateErr = fmt.Errorf("assertion invalid: %s", err)
		return nil, "", retErr
	}

	return resp, decryptedAssertion, nil
}

// validateAssertion checks that the conditions specified in assertion match
// the requirements to accept. If validation fails, it returns an error describing
// the failure. (The digital signature on the assertion is not checked -- this
// should be done before calling this function).
func (sp *ServiceProvider) validateAssertion(assertion *Assertion, possibleRequestIDs []string, now time.Time) error {
	if assertion.IssueInstant.Add(MaxIssueDelay).Before(now) {
		return fmt.Errorf("expired on %s", assertion.IssueInstant.Add(MaxIssueDelay))
	}
	if assertion.Issuer.Value != sp.IDPMetadata.EntityID {
		return fmt.Errorf("issuer is not %q", sp.IDPMetadata.EntityID)
	}
	for _, subjectConfirmation := range assertion.Subject.SubjectConfirmations {
		requestIDvalid := false
		for _, possibleRequestID := range possibleRequestIDs {
			if subjectConfirmation.SubjectConfirmationData.InResponseTo == possibleRequestID {
				requestIDvalid = true
				break
			}
		}
		if !requestIDvalid {
			return fmt.Errorf("assertion SubjectConfirmation one of the possible request IDs (%v)", possibleRequestIDs)
		}
		if subjectConfirmation.SubjectConfirmationData.Recipient != sp.AcsURL.String() {
			return fmt.Errorf("assertion SubjectConfirmation Recipient is not %s", sp.AcsURL.String())
		}
		if subjectConfirmation.SubjectConfirmationData.NotOnOrAfter.Add(MaxClockSkew).Before(now) {
			return fmt.Errorf("assertion SubjectConfirmationData is expired")
		}
	}
	if assertion.Conditions.NotBefore.Add(-MaxClockSkew).After(now) {
		return fmt.Errorf("assertion Conditions is not yet valid")
	}
	if assertion.Conditions.NotOnOrAfter.Add(MaxClockSkew).Before(now) {
		return fmt.Errorf("assertion Conditions is expired")
	}

	audienceRestrictionsValid := len(assertion.Conditions.AudienceRestrictions) == 0
	audience := firstSet(sp.EntityID, sp.MetadataURL.String())
	for _, audienceRestriction := range assertion.Conditions.AudienceRestrictions {
		if audienceRestriction.Audience.Value == audience {
			audienceRestrictionsValid = true
		}
	}
	if !audienceRestrictionsValid {
		return fmt.Errorf("assertion Conditions AudienceRestriction does not contain %q", audience)
	}
	return nil
}

func findChild(parentEl *etree.Element, childNS string, childTag string) (*etree.Element, error) {
	for _, childEl := range parentEl.ChildElements() {
		if childEl.Tag != childTag {
			continue
		}

		ctx, err := etreeutils.NSBuildParentContext(childEl)
		if err != nil {
			return nil, err
		}
		ctx, err = ctx.SubContext(childEl)
		if err != nil {
			return nil, err
		}

		ns, err := ctx.LookupPrefix(childEl.Space)
		if err != nil {
			return nil, fmt.Errorf("[%s]:%s cannot find prefix %s: %v", childNS, childTag, childEl.Space, err)
		}
		if ns != childNS {
			continue
		}

		return childEl, nil
	}
	return nil, nil
}

// validateSigned returns a nil error iff each of the signatures on the Response and Assertion elements
// are valid and there is at least one signature.
func (sp *ServiceProvider) validateSigned(responseEl *etree.Element) error {
	haveSignature := false

	// Some SAML responses have the signature on the Response object, and some on the Assertion
	// object, and some on both. We will require that at least one signature be present and that
	// all signatures be valid
	sigEl, err := findChild(responseEl, "http://www.w3.org/2000/09/xmldsig#", "Signature")
	if err != nil {
		return err
	}
	if sigEl != nil {
		if err = sp.validateSignature(responseEl); err != nil {
			return fmt.Errorf("cannot validate signature on Response: %v", err)
		}
		haveSignature = true
	}

	assertionEl, err := findChild(responseEl, "urn:oasis:names:tc:SAML:2.0:assertion", "Assertion")
	if err != nil {
		return err
	}
	if assertionEl != nil {
		sigEl, err := findChild(assertionEl, "http://www.w3.org/2000/09/xmldsig#", "Signature")
		if err != nil {
			return err
		}
		if sigEl != nil {
			if err = sp.validateSignature(assertionEl); err != nil {
				return fmt.Errorf("cannot validate signature on Response: %v", err)
			}
			haveSignature = true
		}
	}

	if !haveSignature {
		return errors.New("either the Response or Assertion must be signed")
	}
	return nil
}

func (sp *ServiceProvider) validationContext() (*dsig.ValidationContext, error) {
	certs, err := sp.getIDPSigningCerts()
	if err != nil {
		return nil, err
	}

	certificateStore := dsig.MemoryX509CertificateStore{
		Roots: certs,
	}

	validationContext := dsig.NewDefaultValidationContext(&certificateStore)
	validationContext.IdAttribute = "ID"
	if Clock != nil {
		validationContext.Clock = Clock
	}

	return validationContext, nil
}

// validateSignature returns nill iff the Signature embedded in the element is valid
func (sp *ServiceProvider) validateSignature(el *etree.Element) error {
	validationContext, err := sp.validationContext()
	if err != nil {
		return err
	}

	// Some SAML responses contain a RSAKeyValue element. One of two things is happening here:
	//
	// (1) We're getting something signed by a key we already know about -- the public key
	//     of the signing cert provided in the metadata.
	// (2) We're getting something signed by a key we *don't* know about, and which we have
	//     no ability to verify.
	//
	// The best course of action is to just remove the KeyInfo so that dsig falls back to
	// verifying against the public key provided in the metadata.
	if el.FindElement("./Signature/KeyInfo/X509Data/X509Certificate") == nil {
		if sigEl := el.FindElement("./Signature"); sigEl != nil {
			if keyInfo := sigEl.FindElement("KeyInfo"); keyInfo != nil {
				sigEl.RemoveChild(keyInfo)
			}
		}
	}

	ctx, err := etreeutils.NSBuildParentContext(el)
	if err != nil {
		return err
	}
	ctx, err = ctx.SubContext(el)
	if err != nil {
		return err
	}
	el, err = etreeutils.NSDetatch(ctx, el)
	if err != nil {
		return err
	}

	if sp.SignatureVerifier != nil {
		return sp.SignatureVerifier.VerifySignature(validationContext, el)
	}

	_, err = validationContext.Validate(el)
	return err
}

// MakeLogoutRequest produces a new LogoutRequest object for idpURL.
func (sp *ServiceProvider) MakeLogoutRequest(idpURL, nameID string) (*LogoutRequest, error) {

	req := LogoutRequest{
		ID:           fmt.Sprintf("id-%x", randomBytes(20)),
		IssueInstant: TimeNow(),
		Version:      "2.0",
		Destination:  idpURL,
		Issuer: &Issuer{
			Format: "urn:oasis:names:tc:SAML:2.0:nameid-format:entity",
			Value:  firstSet(sp.EntityID, sp.MetadataURL.String()),
		},
		NameID: &NameID{
			Format:          sp.nameIDFormat(),
			Value:           nameID,
			NameQualifier:   sp.IDPMetadata.EntityID,
			SPNameQualifier: firstSet(sp.EntityID, sp.MetadataURL.String()),
		},
	}
	return &req, nil
}

// MakeRedirectLogoutRequest creates a SAML authentication request using
// the HTTP-Redirect binding. It returns a URL that we will redirect the user to
// in order to start the auth process.
func (sp *ServiceProvider) MakeRedirectLogoutRequest(nameID, relayState string) (*url.URL, error) {
	idpSSODescriptor, idpURL := sp.GetSLOBindingLocation(HTTPRedirectBinding)
	req, err := sp.MakeLogoutRequest(idpURL, nameID)
	if err != nil {
		return nil, err
	}
	redirectURL := req.Redirect(relayState)
	if sp.ShouldSignRequest(idpSSODescriptor) {
		err = sp.SignRedirectRequestURL(redirectURL)
		if err != nil {
			return nil, err
		}
	}
	return redirectURL, nil
}

// Redirect returns a URL suitable for using the redirect binding with the request
func (req *LogoutRequest) Redirect(relayState string) *url.URL {
	w := &bytes.Buffer{}
	w1 := base64.NewEncoder(base64.StdEncoding, w)
	w2, _ := flate.NewWriter(w1, 9)
	doc := etree.NewDocument()
	doc.SetRoot(req.Element())
	if _, err := doc.WriteTo(w2); err != nil {
		panic(err)
	}
	w2.Close()
	w1.Close()

	rv, _ := url.Parse(req.Destination)

	query := rv.Query()
	query.Set("SAMLRequest", string(w.Bytes()))
	if relayState != "" {
		query.Set("RelayState", relayState)
	}
	rv.RawQuery = query.Encode()

	return rv
}

// MakePostLogoutRequest creates a SAML authentication request using
// the HTTP-POST binding. It returns HTML text representing an HTML form that
// can be sent presented to a browser to initiate the logout process.
func (sp *ServiceProvider) MakePostLogoutRequest(nameID, relayState string) ([]byte, error) {
	idpSSODescriptor, idpURL := sp.GetSLOBindingLocation(HTTPPostBinding)
	req, err := sp.MakeLogoutRequest(idpURL, nameID)
	if err != nil {
		return nil, err
	}
	if sp.ShouldSignRequest(idpSSODescriptor) {
		err = sp.SignPostLogoutRequest(req)
		if err != nil {
			return nil, err
		}
	}
	return req.Post(relayState), nil
}

func (req *LogoutRequest) PostTemplateData(relayState string) *RequestTemplateData {
	doc := etree.NewDocument()
	doc.SetRoot(req.Element())
	reqBuf, err := doc.WriteToBytes()
	if err != nil {
		panic(err)
	}

	encodedReqBuf := base64.StdEncoding.EncodeToString(reqBuf)

	return &RequestTemplateData{
		URL:         req.Destination,
		SAMLRequest: encodedReqBuf,
		RelayState:  relayState,
	}
}

// Post returns an HTML form suitable for using the HTTP-POST binding with the request
func (req *LogoutRequest) Post(relayState string) []byte {
	td := req.PostTemplateData(relayState)
	rv, err := td.ExecuteTemplate(DefaultRequestTemplate)
	if err != nil {
		panic(err)
	}
	return rv
}

func (sp *ServiceProvider) nameIDFormat() string {
	var nameIDFormat string
	switch sp.AuthnNameIDFormat {
	case "":
		// To maintain library back-compat, use "transient" if unset.
		nameIDFormat = string(TransientNameIDFormat)
	case UnspecifiedNameIDFormat:
		// Spec defines an empty value as "unspecified" so don't set one.
	default:
		nameIDFormat = string(sp.AuthnNameIDFormat)
	}
	return nameIDFormat
}

// ValidateLogoutResponseRequest validates the LogoutResponse content from the request
func (sp *ServiceProvider) ValidateLogoutResponseRequest(req *http.Request) error {
	if data := req.URL.Query().Get("SAMLResponse"); data != "" {
		return sp.ValidateLogoutResponseRedirect(data)
	}

	err := req.ParseForm()
	if err != nil {
		return fmt.Errorf("unable to parse form: %v", err)
	}

	return sp.ValidateLogoutResponseForm(req.PostForm.Get("SAMLResponse"))
}

// ValidatePostLogoutResponse returns a nil error if the logout response is valid.
func (sp *ServiceProvider) ValidateLogoutResponseForm(postFormData string) error {
	rawResponseBuf, err := base64.StdEncoding.DecodeString(postFormData)
	if err != nil {
		return fmt.Errorf("unable to parse base64: %s", err)
	}

	var resp LogoutResponse

	if err := xml.Unmarshal(rawResponseBuf, &resp); err != nil {
		return fmt.Errorf("cannot unmarshal response: %s", err)
	}

	if err := sp.validateLogoutResponse(&resp); err != nil {
		return err
	}

	doc := etree.NewDocument()
	if err := doc.ReadFromBytes(rawResponseBuf); err != nil {
		return err
	}

	responseEl := doc.Root()
	if err = sp.validateSigned(responseEl); err != nil {
		return err
	}

	return nil
}

// ValidateRedirectLogoutResponse returns a nil error if the logout response is valid.
// URL Binding appears to be gzip / flate encoded
// See https://www.oasis-open.org/committees/download.php/20645/sstc-saml-tech-overview-2%200-draft-10.pdf  6.6
func (sp *ServiceProvider) ValidateLogoutResponseRedirect(queryParameterData string) error {
	rawResponseBuf, err := base64.StdEncoding.DecodeString(queryParameterData)
	if err != nil {
		return fmt.Errorf("unable to parse base64: %s", err)
	}

	gr := flate.NewReader(bytes.NewBuffer(rawResponseBuf))

	decoder := xml.NewDecoder(gr)

	var resp LogoutResponse

	err = decoder.Decode(&resp)
	if err != nil {
		return fmt.Errorf("unable to flate decode: %s", err)
	}

	if err := sp.validateLogoutResponse(&resp); err != nil {
		return err
	}

	doc := etree.NewDocument()
	if _, err := doc.ReadFrom(gr); err != nil {
		return err
	}

	responseEl := doc.Root()
	if err = sp.validateSigned(responseEl); err != nil {
		return err
	}

	return nil
}

// validateLogoutResponse validates the LogoutResponse fields. Returns a nil error if the LogoutResponse is valid.
func (sp *ServiceProvider) validateLogoutResponse(resp *LogoutResponse) error {
	if resp.Destination != sp.SloURL.String() {
		return fmt.Errorf("`Destination` does not match SloURL (expected %q)", sp.SloURL.String())
	}

	now := time.Now()
	if resp.IssueInstant.Add(MaxIssueDelay).Before(now) {
		return fmt.Errorf("issueInstant expired at %s", resp.IssueInstant.Add(MaxIssueDelay))
	}
	if resp.Issuer.Value != sp.IDPMetadata.EntityID {
		return fmt.Errorf("issuer does not match the IDP metadata (expected %q)", sp.IDPMetadata.EntityID)
	}
	if resp.Status.StatusCode.Value != StatusSuccess {
		return fmt.Errorf("status code was not %s", StatusSuccess)
	}

	return nil
}

func firstSet(a, b string) string {
	if a == "" {
		return b
	}
	return a
}

func (sp *ServiceProvider) signingKey() crypto.PrivateKey {
	if sp.SigningKey != nil {
		return sp.SigningKey
	}
	return sp.Key
}

func (sp *ServiceProvider) encryptionKey() crypto.PrivateKey {
	if sp.EncryptionKey != nil {
		return sp.EncryptionKey
	}
	return sp.Key
}

func (sp *ServiceProvider) signingCertificate() *x509.Certificate {
	if sp.SigningCertificate != nil {
		return sp.SigningCertificate
	}
	return sp.Certificate
}

func (sp *ServiceProvider) encryptionCertificate() *x509.Certificate {
	if sp.EncryptionCertificate != nil {
		return sp.EncryptionCertificate
	}
	return sp.Certificate
}

func (sp *ServiceProvider) signingContext() (*dsig.SigningContext, error) {

	signingKey := sp.signingKey()
	if signingKey == nil {
		return nil, errors.New("no signing key set")
	}

	signingCertificate := sp.signingCertificate()
	if signingCertificate == nil {
		return nil, errors.New("no signing certificate set")
	}

	signingContext := &dsig.SigningContext{
		IdAttribute:   dsig.DefaultIdAttr,
		Prefix:        dsig.DefaultPrefix,
	}

	keyPair := tls.Certificate{
		Certificate: [][]byte{signingCertificate.Raw},
		PrivateKey:  signingKey,
	}
	for _, intermediate := range sp.Intermediates {
		keyPair.Certificate = append(keyPair.Certificate, intermediate.Raw)
	}

	var err error
	signingContext.KeyStore = dsig.TLSCertKeyStore(keyPair)
	if sp.SigningAlgorithm != "" {
		err = signingContext.SetSignatureMethod(sp.SigningAlgorithm)
	} else {
		err = signingContext.SetSignatureMethod(dsig.RSASHA1SignatureMethod)
	}
	if err != nil {
		return nil, err
	}

	if sp.SigningCanonicalizer != nil {
		signingContext.Canonicalizer = sp.SigningCanonicalizer
	} else {
		signingContext.Canonicalizer = dsig.MakeC14N10ExclusiveCanonicalizerWithPrefixList("")
	}

	return signingContext, nil
}

func (sp *ServiceProvider) ShouldSignRequest(descriptor *IDPSSODescriptor) bool {
	if sp.SignRequests != nil {
		return *sp.SignRequests
	}
	if sp.signingCertificate() == nil {
		return false
	}
	return  descriptor != nil &&
		descriptor.WantAuthnRequestsSigned != nil &&
		*descriptor.WantAuthnRequestsSigned == true
}

func (sp *ServiceProvider) SignPostAuthnRequest(req *AuthnRequest) error {
	ctx, err := sp.signingContext()
	if err != nil {
		return err
	}
	el := req.Element()
	sigEl, err := ctx.ConstructSignature(el, true)
	if err != nil {
		return err
	}
	req.Signature = sigEl
	return nil
}

func (sp *ServiceProvider) SignPostLogoutRequest(req *LogoutRequest) error {
	ctx, err := sp.signingContext()
	if err != nil {
		return err
	}
	el := req.Element()
	sigEl, err := ctx.ConstructSignature(el, true)
	if err != nil {
		return err
	}
	req.Signature = sigEl
	return nil
}

func (sp *ServiceProvider) SignRedirectRequestURL(redirectURL *url.URL) error {
	ctx, err := sp.signingContext()
	if err != nil {
		return err
	}

	query := redirectURL.Query()

	samlRequest := query.Get("SAMLRequest")
	relayState := query.Get("RelayState")
	sigAlg := ctx.GetSignatureMethodIdentifier()

	toBeSigned := "SAMLRequest=" + url.QueryEscape(samlRequest)
	if relayState != "" {
		toBeSigned += "&RelayState=" + url.QueryEscape(relayState)
	}
	toBeSigned += "&SigAlg=" + url.QueryEscape(sigAlg)

	rawSignature, err := ctx.SignString(toBeSigned)
	if err != nil {
		return fmt.Errorf("unable to sign query string of redirect URL: %w", err)
	}

	query.Set("SigAlg", sigAlg)
	query.Set("Signature", base64.StdEncoding.EncodeToString(rawSignature))

	redirectURL.RawQuery = query.Encode()

	return nil
}

// Used with AuthnRequest and LogoutRequest
var DefaultRequestTemplate = template.Must(template.New("saml-post-form").Parse(`` +
	`<form method="post" action="{{.URL}}" id="SAMLRequestForm">` +
	`<input type="hidden" name="SAMLRequest" value="{{.SAMLRequest}}" />` +
	`<input type="hidden" name="RelayState" value="{{.RelayState}}" />` +
	`<input id="SAMLSubmitButton" type="submit" value="Submit" />` +
	`</form>` +
	`<script>document.getElementById('SAMLSubmitButton').style.visibility="hidden";` +
	`document.getElementById('SAMLRequestForm').submit();</script>`))

// Used with AuthnRequest and LogoutRequest
type RequestTemplateData struct {
	URL         string
	SAMLRequest string
	RelayState  string
}

func (rd *RequestTemplateData) ExecuteTemplate(tmpl *template.Template) ([]byte, error) {
	rv := bytes.Buffer{}
	if err := tmpl.Execute(&rv, rd); err != nil {
		return nil, err
	}
	return rv.Bytes(), nil
}

func (rd *RequestTemplateData) ExecuteTemplateString(templateStr string) ([]byte, error) {
	tmpl, err := template.New("saml-post-form").Parse(templateStr)
	if err != nil {
		return nil, err
	}
	return rd.ExecuteTemplate(tmpl)
}

func (rd *RequestTemplateData) ExecuteTemplateFile(templateFilename string) ([]byte, error) {
	tmpl, err := template.ParseFiles(templateFilename)
	if err != nil {
		return nil, err
	}
	return rd.ExecuteTemplate(tmpl)
}