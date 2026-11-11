const P=`@prefix ex: <https://example.org/lab/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix schema: <https://schema.org/> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

`;
const common=`PREFIX ex: <https://example.org/lab/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX schema: <https://schema.org/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>

`;
const offerOntology=P+`ex:AutonomousPurchasingAgent rdfs:subClassOf ex:ArtificialAgent ;
  owl:disjointWith foaf:Organization .
ex:ArtificialAgent rdfs:subClassOf foaf:Agent .
ex:RobotCollective rdfs:subClassOf ex:ArtificialAgent, foaf:Organization .
ex:ControlledArtificialAgent rdfs:subClassOf ex:ArtificialAgent .
`;
const baseOffer=P+`ex:offer42 a schema:Offer ;
  ex:responsibleParty ex:agent17 .
ex:agent17 a ex:AutonomousPurchasingAgent ;
  ex:transport "xmpp" ;
  ex:encryption "omemo" ;
  ex:validUntil "2026-11-12T12:00:00Z"^^xsd:dateTime .
`;
const offerLean=`import Init

namespace LinkedAssurance

/-- Vocabulary identifiers are RDF term VALUES, not Lean class declarations. -/
def artificialAgent : String := "https://example.org/lab/ArtificialAgent"
def responsibleParty : String := "https://example.org/lab/responsibleParty"

/-- A semantic evidence provider: it may be implemented by an RDF
    entailment engine, but this file does NOT prove that connection. -/
structure Evidence where
  hasRelation : String → String → String → Prop
  hasType : String → String → Prop
  ruledOutOrganization : String → Prop
  secureChannel : String → Prop
  liveCredential : String → Prop

def RequiresEthicsReview (e : Evidence) (offer agent : String) : Prop :=
  e.hasRelation offer responsibleParty agent ∧
  e.hasType agent artificialAgent ∧
  e.ruledOutOrganization agent

def MayProcess (e : Evidence) (agent : String) : Prop :=
  e.secureChannel agent ∧ e.liveCredential agent

/-- Classification can require review, but does not itself license execution. -/
theorem review_and_process_separate (e : Evidence) (o a : String)
    (hReview : RequiresEthicsReview e o a)
    (hProcess : MayProcess e a) :
    e.ruledOutOrganization a ∧ e.secureChannel a ∧
      e.liveCredential a := by
  exact ⟨hReview.2.2, hProcess.1, hProcess.2⟩

/-- Executable policy gate: any failed condition prevents execution. -/
def permit (classified excluded secure fresh : Bool) : Bool :=
  classified && excluded && secure && fresh

theorem permit_implies_secure (c x s f : Bool)
    (h : permit c x s f = true) : s = true := by
  cases c <;> cases x <;> cases s <;> cases f <;> simp_all [permit]

theorem permit_implies_fresh (c x s f : Bool)
    (h : permit c x s f = true) : f = true := by
  cases c <;> cases x <;> cases s <;> cases f <;> simp_all [permit]

#eval permit true true true false  -- false

end LinkedAssurance
`;
const eventLean=`import Init
namespace LinkedAssurance
def permitEvent (isEvent isAttendee consent windowOpen : Bool) : Bool :=
  isEvent && isAttendee && consent && windowOpen

theorem attendee_action_requires_consent (e a c w : Bool)
    (h : permitEvent e a c w = true) : c = true := by
  cases e <;> cases a <;> cases c <;> cases w <;> simp_all [permitEvent]

theorem attendee_action_requires_window (e a c w : Bool)
    (h : permitEvent e a c w = true) : w = true := by
  cases e <;> cases a <;> cases c <;> cases w <;> simp_all [permitEvent]

#eval permitEvent true true false true -- false
end LinkedAssurance
`;
const artifactLean=`import Init
namespace LinkedAssurance
def releaseArtifact (isArtifact isApproved validSignature beforeDeadline : Bool) : Bool :=
  isArtifact && isApproved && validSignature && beforeDeadline

theorem no_unsigned_release (a p sig deadline : Bool)
    (h : releaseArtifact a p sig deadline = true) : sig = true := by
  cases a <;> cases p <;> cases sig <;> cases deadline <;> simp_all [releaseArtifact]

theorem no_expired_release (a p sig deadline : Bool)
    (h : releaseArtifact a p sig deadline = true) : deadline = true := by
  cases a <;> cases p <;> cases sig <;> cases deadline <;> simp_all [releaseArtifact]

#eval releaseArtifact true true false true -- false
end LinkedAssurance
`;
const vocabLean=`import Init
namespace LinkedAssurance

/-- The vocabulary isn't enumerated in Lean: arbitrary class IRIs. -/
structure SemanticView where
  member : String → String → Prop
  subclass : String → String → Prop
  transitiveType : ∀ (x sub sup : String),
    member x sub → subclass sub sup → member x sup

def qualifies (v : SemanticView) (entity classIri : String) : Prop :=
  v.member entity classIri

theorem new_vocabulary_works (v : SemanticView)
    (person newClass policyClass : String)
    (hInstance : v.member person newClass)
    (hVocabulary : v.subclass newClass policyClass) :
    qualifies v person policyClass := by
  exact v.transitiveType person newClass policyClass
    hInstance hVocabulary

end LinkedAssurance
`;
const offer={
 id:"offer",short:"Ethics review",title:"Artificial agent and offer responsibility",
 summary:"New agent classes, disjointness evidence, and protocol/time gates.",
 ontology:offerOntology,data:baseOffer,defaultVariant:"nonorg",
 variants:[
 {id:"nonorg",name:"Autonomous non-organisation",data:baseOffer},
 {id:"organization",name:"Agent also an Organisation",data:P+`ex:offer42 a schema:Offer ; ex:responsibleParty ex:agent17 .
ex:agent17 a ex:RobotCollective ;
 ex:transport "xmpp" ; ex:encryption "omemo" ;
 ex:validUntil "2026-11-12T12:00:00Z"^^xsd:dateTime .
`},
 {id:"expired",name:"Expired credential",data:baseOffer.replace("2026-11-12T12:00:00Z","2026-11-10T12:00:00Z")},
 {id:"unclassified",name:"Unknown new agent class",data:baseOffer.replace("ex:AutonomousPurchasingAgent","ex:UnclassifiedAutonomousThing")}
 ],
 query:common+`SELECT ?agent ?type ?transport ?encryption ?expiry WHERE {
 ex:offer42 ex:responsibleParty ?agent .
 ?agent rdf:type ?type ;
        ex:transport ?transport ;
        ex:encryption ?encryption ;
        ex:validUntil ?expiry .
}`,
 ask:common+`ASK WHERE {
 ex:offer42 ex:responsibleParty ?agent .
 ?agent rdf:type ex:ArtificialAgent .
}`,
 complementary:[
  {key:"org",query:common+`ASK WHERE { ex:offer42 ex:responsibleParty ?agent . ?agent rdf:type foaf:Organization . }`},
  {key:"exclude",query:common+`ASK WHERE {
 ex:offer42 ex:responsibleParty ?agent .
 ?agent rdf:type ?class .
 ?class owl:disjointWith foaf:Organization .
}`}
 ],
 auditTime:"2026-11-11T12:00:00Z",
 lean:offerLean,
 reason:"RDFS supplies the ArtificialAgent superclass; an explicitly asserted OWL disjointness axiom is queried as evidence, not treated as full OWL negative entailment. A positive Organization classification plus an exclusion witness is reported as contradictory. This demonstration does not certify OWL consistency.",
 leanFirst:`-- Lean-first view: RDF terms remain runtime values.
def classify (ctx : SemanticContext) (offer agent : RDFTerm) : Prop :=
  EntailsType ctx agent ex.ArtificialAgent ∧
  EntailsProperty ctx offer ex.responsibleParty agent ∧
  ProvenExcludedType ctx agent foaf.Organization

theorem decision_implies_credential_safe ... := ...
-- Protocol timing + crypto obligations are Lean-side contracts.
-- This is a design sketch, not compiled Factoidal code.`,
 hybrid:`POLICY "Agent ethics review"
  RDF [RDFS]:
    offer42 ex:responsibleParty ?agent
    ?agent rdf:type ex:ArtificialAgent
    ?agent rdf:type ?class
    ?class owl:disjointWith foaf:Organization
  FIXED OPERATIONS:
    secureTransport(?agent, "xmpp", "omemo")
    credentialLive(?agent, auditTime)
  ROUTE:
    classify -> ethicsReview
    process only when all protocol gates hold
# Design notation, not a deployed DSL.`,
 rdfFirst:common+`# RDF-first classification. New vocabulary is just runtime RDF.
ASK WHERE {
 ex:offer42 ex:responsibleParty ?agent .
 ?agent rdf:type ex:ArtificialAgent .
 ?agent rdf:type ?class .
 ?class owl:disjointWith foaf:Organization .
}
# Separate registered fixed operations check credential + transport.
# Neither missing class membership nor missing disjointness proves negation.`,
};
const event={
 id:"event",short:"Event admission",title:"Event, attendee and consent",
 summary:"FOAF/Schema.org event relationship plus an external consent/time gate.",
 ontology:P+`ex:CommunityEvent rdfs:subClassOf schema:Event .
ex:RegisteredParticipant rdfs:subClassOf foaf:Agent .
`,
 data:P+`ex:festival a ex:CommunityEvent ; schema:attendee ex:mira .
ex:mira a ex:RegisteredParticipant ; ex:consent "yes" ;
  ex:accessUntil "2026-11-12T18:00:00Z"^^xsd:dateTime .
`,
 defaultVariant:"consent",
 variants:[
 {id:"consent",name:"Consent and valid window",data:P+`ex:festival a ex:CommunityEvent ; schema:attendee ex:mira .
ex:mira a ex:RegisteredParticipant ; ex:consent "yes" ;
 ex:accessUntil "2026-11-12T18:00:00Z"^^xsd:dateTime .
`},
 {id:"no-consent",name:"Consent withdrawn",data:P+`ex:festival a ex:CommunityEvent ; schema:attendee ex:mira .
ex:mira a ex:RegisteredParticipant ; ex:consent "no" ;
 ex:accessUntil "2026-11-12T18:00:00Z"^^xsd:dateTime .
`},
 {id:"outdated",name:"Access window expired",data:P+`ex:festival a ex:CommunityEvent ; schema:attendee ex:mira .
ex:mira a ex:RegisteredParticipant ; ex:consent "yes" ;
 ex:accessUntil "2026-11-10T12:00:00Z"^^xsd:dateTime .
`}
 ],
 query:common+`SELECT ?person ?consent ?expiry WHERE {
 ex:festival schema:attendee ?person .
 ?person ex:consent ?consent ; ex:accessUntil ?expiry .
}`,
 ask:common+`ASK WHERE { ex:festival rdf:type schema:Event ; schema:attendee ex:mira . }`,
 complementary:[],auditTime:"2026-11-11T12:00:00Z",lean:eventLean,
 reason:"FOAF Agent includes nonhuman, historical and fictional entities; the consent assertion is application-specific and not evidence of genuine informed consent. A verified production consent mechanism is a separate obligation.",
 leanFirst:`def AdmitEventAttendee (ctx : Context) (person : RDFTerm) : Prop :=
  EntailsType ctx ex.festival schema.Event ∧
  EntailsProperty ctx ex.festival schema.attendee person ∧
  ValidConsent ctx person ∧ InTimeWindow ctx person

theorem admitted_requires_consent ... := ...`,
 hybrid:`POLICY "Event admission"
  RDF [RDFS]:
    ex:festival rdf:type schema:Event
    ex:festival schema:attendee ?person
  OPERATIONS:
    validConsent(?person)
    beforeAccessExpiry(?person, clock)
  INVARIANT: admit -> consent and valid access window`,
 rdfFirst:common+`ASK WHERE {
  ex:festival rdf:type schema:Event ;
              schema:attendee ex:mira .
}
# Consent and expiry are separate fixed-operation gates.`
};
const artifact={
 id:"artifact",short:"Artifact release",title:"Artifact release and execution constraints",
 summary:"Verified-style release gate with explicit missing crypto trust boundary.",
 ontology:P+`ex:DocumentationArtifact rdfs:subClassOf schema:CreativeWork .
ex:SignedRelease rdfs:subClassOf ex:ReleaseApproval .
`,
 data:P+`ex:image77 a ex:DocumentationArtifact ; ex:approvedBy ex:reviewer ;
 ex:signatureState "verified" ; ex:releaseBefore "2026-11-12T12:00:00Z"^^xsd:dateTime .
ex:reviewer a foaf:Agent .
`,
 defaultVariant:"approved",variants:[
 {id:"approved",name:"Approval + signature flag",data:P+`ex:image77 a ex:DocumentationArtifact ; ex:approvedBy ex:reviewer ;
 ex:signatureState "verified" ; ex:releaseBefore "2026-11-12T12:00:00Z"^^xsd:dateTime .
ex:reviewer a foaf:Agent .
`},
 {id:"unsigned",name:"Missing signature verification",data:P+`ex:image77 a ex:DocumentationArtifact ; ex:approvedBy ex:reviewer ;
 ex:signatureState "missing" ; ex:releaseBefore "2026-11-12T12:00:00Z"^^xsd:dateTime .
ex:reviewer a foaf:Agent .
`},
 {id:"late",name:"Release deadline passed",data:P+`ex:image77 a ex:DocumentationArtifact ; ex:approvedBy ex:reviewer ;
 ex:signatureState "verified" ; ex:releaseBefore "2026-11-10T12:00:00Z"^^xsd:dateTime .
ex:reviewer a foaf:Agent .
`}
 ],
 query:common+`SELECT ?reviewer ?signature ?expiry WHERE {
 ex:image77 ex:approvedBy ?reviewer ;
            ex:signatureState ?signature ;
            ex:releaseBefore ?expiry .
}`,
 ask:common+`ASK WHERE { ex:image77 rdf:type schema:CreativeWork . }`,
 complementary:[],auditTime:"2026-11-11T12:00:00Z",lean:artifactLean,
 reason:"An RDF flag saying 'verified' is NOT a cryptographic signature check. This example proves only a Boolean release gate in Lean, with cryptographic authenticity remaining an unmet external premise.",
 leanFirst:`def ReleasePermitted (ctx : Context) (artifact : RDFTerm) : Prop :=
  EntailsType ctx artifact schema.CreativeWork ∧
  HasApprovedReviewer ctx artifact ∧
  SignatureVerified ctx artifact ∧
  WithinReleaseWindow ctx artifact

theorem release_requires_signature ... := ...`,
 hybrid:`POLICY "Artifact release"
  RDF [RDFS]:
    ex:image77 rdf:type schema:CreativeWork
    ex:image77 ex:approvedBy ?reviewer
  OPERATIONS:
    cryptographicVerify(?artifact, trustedKeys)
    beforeReleaseDeadline(?artifact, clock)
  INVARIANT: release -> validSignature`,
 rdfFirst:common+`ASK WHERE {
 ex:image77 rdf:type schema:CreativeWork ;
            ex:approvedBy ?reviewer .
}
# The signature verifier must be a separately specified operation.`
};
const vocabulary={
 id:"vocabulary",short:"New vocabulary",title:"Unfamiliar ontology, unchanged theorem",
 summary:"Invent a class tomorrow; subclass semantics still applies without new Lean declarations.",
 ontology:P+`ex:InterplanetaryCheesemaker rdfs:subClassOf ex:ApprovedSupplier .
ex:ApprovedSupplier rdfs:subClassOf foaf:Agent .
`,
 data:P+`ex:person42 a ex:InterplanetaryCheesemaker .
`,
 defaultVariant:"inherits",variants:[
 {id:"inherits",name:"Novel subclass",data:P+`ex:person42 a ex:InterplanetaryCheesemaker .
`},
 {id:"unrelated",name:"Unrelated class",data:P+`ex:person42 a ex:UnrelatedNewClass .
`},
 {id:"direct",name:"Directly approved",data:P+`ex:person42 a ex:ApprovedSupplier .
`}
 ],
 query:common+`SELECT ?class WHERE { ex:person42 rdf:type ?class . }`,
 ask:common+`ASK WHERE { ex:person42 rdf:type ex:ApprovedSupplier . }`,
 complementary:[],lean:vocabLean,
 reason:"The subclass theorem quantifies over arbitrary RDF term values; class IRIs invented after compilation still work. Without an explicit subclass relation, qualification cannot be inferred.",
 leanFirst:`theorem any_vocabulary (ctx : SemanticContext)
    (entity subclass superclass : RDFTerm)
    (h : EntailsType ctx entity subclass)
    (hSub : EntailsSubclass ctx subclass superclass) :
    EntailsType ctx entity superclass := ...`,
 hybrid:`POLICY "Open vocabulary"
  RDF [RDFS]:
    ?supplier rdf:type ?freshClass
    ?freshClass rdfs:subClassOf* ex:ApprovedSupplier
  LEAN SEMANTICS:
    subclass_entailment_generic
  RESULT:
    qualification does not require new Lean declarations`,
 rdfFirst:common+`ASK WHERE { ex:person42 rdf:type ex:ApprovedSupplier . }
# ex:InterplanetaryCheesemaker is not compiled into Lean;
# it enters as ordinary ontology data.`
};
export const scenarios=[offer,event,artifact,vocabulary];
export function getScenario(id){return scenarios.find(s=>s.id===id)||scenarios[0];}