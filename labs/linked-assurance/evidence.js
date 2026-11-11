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
export async function evaluateRdf(api, request) {
  if(!['simple','RDFS'].includes(request.regime))
    return {execution:'unsupported',claims:[],error:'Only simple and RDFS are admitted by this lab.'};
  let parsed;
  try {parsed=await api.parse(request.dataset,{format:'trig'});}
  catch(e){e.labPhase='parse';throw e;}
  let selected;
  try {
    const quads=parsed.toArray();
    const selection=quads.filter(q=>request.scope.kind==='default'
      ? q.graph.termType==='DefaultGraph'
      : q.graph.termType==='NamedNode' && request.scope.graphs.includes(q.graph.value));
    // One TriG document: preserve its blank identity. Select BEFORE inference.
    selected=await api.fromQuads(selection.map(q=>({...q,graph:{termType:'DefaultGraph',value:''}})));
    const selectedText=await api.serialize(selected,{format:'ntriples'}), claims=[];
    for(const binding of request.queries) {
      const r=await api.query(selected,binding.query,{output:'json',...(request.regime==='RDFS'?{entail:'RDFS'}:{})});
      if(typeof r?.boolean!=='boolean') throw Error(`Binding ${binding.key} must return ASK boolean.`);
      claims.push({key:binding.key,query:binding.query,answer:r.boolean});
    }
    // Graph-description evidence is displayed separately: arbitrary edited ASK
    // queries are NOT asserted equivalent to this description.
    const explanation=request.regime==='RDFS' && request.description.trim()
      ? await api.explain(selected,request.description,{profile:'rdfs'}) : null;
    return {execution:'completed',claims,explanation,selectedText,
      context:{datasetBytesSha256:await sha256(request.dataset),selectedGraphSha256:await sha256(selectedText),
        scope:JSON.stringify(request.scope),regime:request.regime,runtimeVersion:String(api.version)},
      dataset:{quads:quads.length,defaultQuads:quads.filter(q=>q.graph.termType==='DefaultGraph').length,
        namedGraphs:[...new Set(quads.filter(q=>q.graph.termType==='NamedNode').map(q=>q.graph.value))],selectedQuads:selected.size}};
  } finally {selected?.dispose(); parsed.dispose();}
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
export function fixtureSource(result,s,context) {
  if(!['completed','timeout','parserError','engineFault','cancelled','unsupported'].includes(result.execution)) throw Error('Unknown execution status.');
  for(const key of ['observedTime','expiresAt'])if(!Number.isSafeInteger(s[key])||s[key]<0)throw Error('Invalid timestamp.');
  const c=result.context||context;
  const claims=(result.claims||[]).map(x=>`⟨${leanString(x.key)}, ${leanString(x.query)}, ${x.answer===true}⟩`).join(',\n');
  return `import Policy
open LinkedAssurance
def evidence : Evidence := {
  context := ⟨${['datasetBytesSha256','selectedGraphSha256','scope','regime','runtimeVersion'].map(k=>leanString(c[k])).join(', ')}⟩
  execution := .${result.execution}
  claims := [${claims}]
}
def operational : OperationalState := {
  credentialVerified := ${s.credentialVerified===true}
  observedTime := ${s.observedTime}
  expiresAt := ${s.expiresAt}
  secureTransportObserved := ${s.secureTransportObserved===true}
  permissionGranted := ${s.permissionGranted===true}
  attackerWantsInterruption := ${s.attackerWantsInterruption===true}
  legitimateSession := ${s.legitimateSession===true}
}
#eval (policy evidence operational, attackerOutcome (policy evidence operational) operational)
-- An injected fixture is not a proof of correspondence to the original RDF.
`;
}
