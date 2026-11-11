const prefixes=`@prefix ex: <urn:lab:> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix schema: <https://schema.org/> .\n`;
const prolog=`PREFIX ex: <urn:lab:>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX schema: <https://schema.org/>\n`;
const ask=(key,pattern)=>({key,query:prolog+`ASK WHERE { ${pattern} }`});
function sample(id,title,ontology,data,classification,condition,description,note,extra=[]) {
  return {id,title,note,description:prefixes+description,
    dataset:prefixes+`\nex:ontology {\n${ontology}\n}\nex:data {\n${data}\n}\n# The default graph is explicitly empty.\n`,
    queries:[ask('classification',classification),ask('applicationCondition',condition),...extra]};
}
const vocabulary=sample('vocabulary','New vocabulary',
  'ex:InterplanetaryCheesemaker rdfs:subClassOf ex:ApprovedSupplier .',
  'ex:principal a ex:InterplanetaryCheesemaker .',
  'ex:principal a ex:ApprovedSupplier .','ex:principal a ex:ApprovedSupplier .',
  'ex:principal a ex:ApprovedSupplier .',
  'Rename the unfamiliar class in both graphs. Lean declarations stay unchanged. Select only the data graph to remove the subclass premise.');
const offer=sample('offer','Offer responsibility',
  'ex:AutonomousPurchaser rdfs:subClassOf ex:ArtificialAgent ; owl:disjointWith foaf:Organization .',
  'ex:offer a schema:Offer ; ex:responsibleParty ex:principal .\nex:principal a ex:AutonomousPurchaser .',
  'ex:offer ex:responsibleParty ex:principal . ex:principal a ex:ArtificialAgent .',
  'ex:offer ex:responsibleParty ex:principal .',
  'ex:principal a ex:ArtificialAgent .',
  'Artificial-agent evidence routes to review. The disjointness query reports an assertion, not an OWL refutation. Organization plus that assertion triggers escalation, not an inconsistency verdict.',
  [ask('reviewRequired','ex:principal a ex:ArtificialAgent .'),ask('organization','ex:principal a foaf:Organization .'),
   ask('disjointnessAssertion','ex:principal a ?class . ?class owl:disjointWith foaf:Organization .')]);
const event=sample('event','Event admission',
  'ex:CommunityEvent rdfs:subClassOf schema:Event .',
  'ex:festival a ex:CommunityEvent ; schema:attendee ex:principal .\nex:principal ex:consent "yes" .',
  'ex:festival a schema:Event ; schema:attendee ex:principal .',
  'ex:principal ex:consent "yes" .','ex:festival a schema:Event .',
  'Consent is an RDF assertion. The policy also requires a signature check, an unexpired demo credential, and explicit operational observations. Those do not establish informed consent.');
const artifact=sample('artifact','Artifact release',
  'ex:DocumentationArtifact rdfs:subClassOf schema:CreativeWork .',
  'ex:artifact a ex:DocumentationArtifact ; ex:approvedBy ex:principal ; ex:signatureState "verified" .',
  'ex:artifact a schema:CreativeWork .','ex:artifact ex:approvedBy ex:principal .',
  'ex:artifact a schema:CreativeWork .',
  'The string "verified" does not enter the credential gate. The separate ECDSA check authenticates only the displayed demo credential payload, not the artifact or its approval.');
const alert=sample('alert','False alarm and interruption',
  'ex:WorkSession rdfs:subClassOf ex:Session .',
  'ex:principal a ex:WorkSession ; ex:alert "unsafe content" .',
  'ex:principal a ex:Session .','ex:principal a ex:Session .','ex:principal a ex:Session .',
  'Test oracle: the session is legitimate and the adversary wants interruption. A supplied alert can trigger protective shutdown and satisfy that objective. Harm prevention remains unknown.',
  [ask('alert','ex:principal ex:alert "unsafe content" .')]);
export const scenarios=[vocabulary,offer,event,artifact,alert];
export function variants(s) {
  return [
    {id:'base',name:'Baseline',dataset:s.dataset},
    {id:'unclassified',name:'Unrelated class',dataset:s.dataset.replaceAll('ex:principal a ex:InterplanetaryCheesemaker','ex:principal a ex:UnknownClass').replaceAll('ex:principal a ex:AutonomousPurchaser','ex:principal a ex:UnknownClass').replaceAll('ex:festival a ex:CommunityEvent','ex:festival a ex:UnknownClass').replaceAll('ex:artifact a ex:DocumentationArtifact','ex:artifact a ex:UnknownClass').replaceAll('ex:principal a ex:WorkSession','ex:principal a ex:UnknownClass')},
    ...(s.id==='event'?[{id:'no-consent',name:'Consent absent',dataset:s.dataset.replace('ex:principal ex:consent "yes" .','')}]:[]),
    ...(s.id==='offer'?[{id:'both',name:'Also an Organization',dataset:s.dataset.replace('ex:principal a ex:AutonomousPurchaser .','ex:principal a ex:AutonomousPurchaser, foaf:Organization .')}]:[]),
    ...(s.id==='alert'?[{id:'no-alert',name:'No alert',dataset:s.dataset.replace(' ; ex:alert "unsafe content"','')}]:[]),
    {id:'invalid',name:'Invalid TriG',dataset:s.dataset+'\n<unterminated'},
  ];
}
