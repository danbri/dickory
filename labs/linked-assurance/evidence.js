// Transport and orchestration only. RDF parsing/equality/reasoning stay in Factoidal.
export const runtime = Object.freeze({package:'@factoidal/core',version:'0.35.1',
  sourceCommit:'6f57afba14e04ed648358e4693790edff69a6cd3',
  declaredWasmSha256:'2e241365bd7906474320610a65af99641474534fa0fe0e744ed3d9edeef4ee41',
  provenance:'factoidal-build.json; package-declared identity, not independent runtime attestation',
  module:'https://cdn.jsdelivr.net/npm/@factoidal/core@0.35.1/browser.js'});
export async function sha256(value) {
  const bytes = typeof value === 'string' ? new TextEncoder().encode(value) : value;
  return [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
    .map(b=>b.toString(16).padStart(2,'0')).join('');
}
export function queriesFrom(text) {
  const qs=JSON.parse(text), names=new Set();
  if (!Array.isArray(qs) || !qs.length || qs.length>20) throw Error('Use 1–20 ASK bindings.');
  for(const q of qs) {
    if(typeof q.key!=='string' || !q.key || names.has(q.key) || typeof q.query!=='string')
      throw Error('Every binding needs a unique key and a query string.');
    names.add(q.key);
  }
  return qs;
}
export function scopeFrom(value) {
  if(value==='default') return {kind:'default',graphs:[]};
  if(value==='data') return {kind:'selected',graphs:['urn:lab:data']};
  if(value==='ontology') return {kind:'selected',graphs:['urn:lab:ontology']};
  if(value==='union') return {kind:'constructed-union',graphs:['urn:lab:data','urn:lab:ontology']};
  throw Error('Unsupported graph scope.');
}
export function selectionQuery(scope){
  if(scope.kind==='default' && scope.graphs.length===0)return 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }';
  if(!['selected','constructed-union'].includes(scope.kind)||!scope.graphs.length||
      scope.graphs.some(g=>!['urn:lab:data','urn:lab:ontology'].includes(g)))throw Error('Unsupported graph scope.');
  return 'CONSTRUCT { ?s ?p ?o } WHERE { '+scope.graphs.map(g=>'{ GRAPH <'+g+'> { ?s ?p ?o } }').join(' UNION ')+' }';
}
export async function evaluateRdf(api, request) {
  if(!['simple','RDFS'].includes(request.regime))
    return {execution:'unsupported',claims:[],error:'Only simple and RDFS are admitted by this lab.'};
  let parsed,read;
  const readerNode=await api.node('trigDocumentReader'),reader=api.pipe(readerNode);
  try {read=await api.run(reader,request.dataset);parsed=read.graph;}
  catch(e){e.labPhase='parse';throw e;}
  let execution;
  try {
    const quads=parsed.toArray();
    // Selection is a real checked CONSTRUCT node, before the reasoner. Values
    // bound from this one document keep their blank identity across its graphs.
    const query=selectionQuery(request.scope),nodes=[{node:await api.node('shippedEvaluator',{query}),from:[{input:0}]}];
    let queryInput=0;
    if(request.regime==='RDFS'){queryInput=nodes.length;nodes.push({node:await api.node('rdfsReasoner'),from:[{node:0}]});}
    const bindings=[];
    for(const binding of request.queries) {
      const node=await api.node('shippedEvaluator',{query:binding.query});
      if(node.wireOut!=='Answer')throw Error(`Binding ${binding.key} must return ASK boolean.`);
      bindings.push({key:binding.key,query:binding.query,node:nodes.length});
      nodes.push({node,from:[{node:queryInput}]});
    }
    let explanationNode=null;
    if(request.regime==='RDFS'&&request.description.trim()){
      explanationNode=nodes.length;
      nodes.push({node:await api.node('rdfsExplainGraphStage',{description:request.description}),from:[{node:0}]});
    }
    const graph=api.graph({inputs:[readerNode.wireOut],nodes});
    execution=await api.run(graph,[read]);
    const selected=execution.values[0],selectedText=await api.serialize(selected,{format:'ntriples'});
    const claims=bindings.map(b=>({key:b.key,query:b.query,answer:execution.values[b.node]}));
    if(claims.some(c=>typeof c.answer!=='boolean'))throw Error('ASK binding did not produce a Boolean.');
    // A description certificate is its own branch, not a proof that an edited
    // ASK means what the policy author intended by its application key.
    const explanation=explanationNode===null?null:execution.values[explanationNode];
    return {execution:'completed',claims,explanation,selectedText,
      pipeline:{schema:'factoidal-contracted-stages-v1',readerCheck:reader.check,graphCheck:graph.check,
        evidence:execution.evidence,assumptions:execution.assumptions,registeredStagesProved:execution.proved,
        selection:{node:0,query,scope:request.scope},bindings,explanationNode,
        boundary:'Registered stage contracts and checked wiring. JavaScript execution and the policy-key interpretation remain trust boundaries.'},
      context:{datasetBytesSha256:await sha256(request.dataset),selectedGraphSha256:await sha256(selectedText),
        scope:JSON.stringify(request.scope),regime:request.regime,runtimeVersion:String(api.version)},
      dataset:{quads:quads.length,defaultQuads:quads.filter(q=>q.graph.termType==='DefaultGraph').length,
        namedGraphs:[...new Set(quads.filter(q=>q.graph.termType==='NamedNode').map(q=>q.graph.value))],selectedQuads:selected.size}};
  } finally {
    for(const value of new Set(execution?.values||[]))if(value instanceof api.Dataset)value.dispose();
    parsed.dispose();
  }
}
export function startRdf(request,budgetMs,workerFactory=()=>new Worker(new URL('./rdf-worker.js',import.meta.url),{type:'module'})) {
  if(!Number.isFinite(budgetMs)||budgetMs<1||budgetMs>120000) throw Error('RDF budget must be 1–120000 ms.');
  const worker=workerFactory(); let finish,timer;
  const promise=new Promise(resolve=>{
    let settled=false;
    finish=result=>{if(settled)return; settled=true;clearTimeout(timer);worker.terminate();resolve(result);};
    timer=setTimeout(()=>finish({execution:'timeout',claims:[],error:`Deadline ${budgetMs} ms exceeded; worker terminated.`}),budgetMs);
    worker.onmessage=e=>{if(e.data?.kind==='result')finish(e.data.result);};
    worker.onerror=e=>finish({execution:'engineFault',claims:[],error:e.message});
    worker.postMessage(request);
  });
  return {promise,cancel:()=>finish({execution:'cancelled',claims:[],error:'Cancelled by user.'})};
}
export function leanString(value) {
  return '"'+[...String(value)].map(c=>{
    if(c==='"')return '\\"';if(c==='\\')return '\\\\';
    if(c==='\n')return '\\n';if(c==='\r')return '\\r';if(c==='\t')return '\\t';
    if(c.codePointAt(0)<32)return '\\x'+c.codePointAt(0).toString(16).padStart(2,'0');
    return c;
  }).join('')+'"';
}
export function fixtureSource(result,s,context,requestedBindings=result.claims||[]) {
  if(!['completed','timeout','parserError','engineFault','cancelled','unsupported'].includes(result.execution)) throw Error('Unknown execution status.');
  for(const key of ['observedTime','expiresAt'])if(!Number.isSafeInteger(s[key])||s[key]<0)throw Error('Invalid timestamp.');
  const c=result.context||context;
  const bindings=(result.execution==='completed'?requestedBindings:[]).map(x=>`⟨${leanString(x.key)}, ${leanString(x.query)}⟩`).join(',\n');
  const observations=(result.claims||[]).map(x=>`⟨${leanString(x.query)}, ${x.answer===true}⟩`).join(',\n');
  return `module
public import Policy
public meta import Policy
open LinkedAssurance
def queryBindings : List QueryBinding := [${bindings}]
def observations : List QueryObservation := [${observations}]
def adaptedEvidence : Except String Evidence := adaptEvidence
  ⟨${['datasetBytesSha256','selectedGraphSha256','scope','regime','runtimeVersion'].map(k=>leanString(c[k])).join(', ')}⟩
  .${result.execution} queryBindings observations
def operational : OperationalState := {
  credentialVerified := ${s.credentialVerified===true}
  observedTime := ${s.observedTime}
  expiresAt := ${s.expiresAt}
  secureTransportObserved := ${s.secureTransportObserved===true}
  permissionGranted := ${s.permissionGranted===true}
  attackerWantsInterruption := ${s.attackerWantsInterruption===true}
  legitimateSession := ${s.legitimateSession===true}
}
#eval adaptedEvidence.map (fun evidence =>
  (policy evidence operational, attackerOutcome (policy evidence operational) operational))
-- An injected fixture is not a proof of correspondence to the original RDF.
`;
}
