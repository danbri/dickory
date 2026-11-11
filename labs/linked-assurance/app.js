import {scenarios,getScenario} from "./scenarios.js";

const $=id=>document.getElementById(id);
const state={scenario:getScenario("offer"),variant:null,editing:"data",edits:{data:"",ontology:""},engine:null,runToken:0,lastEvaluation:null};
function currentScenario(){return state.scenario;}
function selectedVariant(){return state.variant||state.scenario.variants[0];}
function setText(id,txt){$(id).textContent=txt;}
function setStatus(id,value,tone=""){const el=$(id);el.textContent=value;el.classList.remove("good","warn","bad");if(tone)el.classList.add(tone);}
function getEdition(){return state.edits[state.editing];}
function activateSample(id){
 state.scenario=getScenario(id);
 const s=state.scenario;
 $("scenario").value=s.id;
 $("variant").replaceChildren(...s.variants.map(v=>new Option(v.name,v.id)));
 const v=s.variants.find(v=>v.id===s.defaultVariant)||s.variants[0];
 $("variant").value=v.id;state.variant=v;
 state.edits={data:v.data,ontology:s.ontology};
 state.editing="data";renderEditorTabs();setText("policyTitle",s.title);
 $("leanEditor").value=s.lean;setText("proofNotes",s.reason);
 $("dataCount").textContent="Editable Turtle";
 drawPolicy();clearEvaluation();
}
function changeVariant(id){
 state.variant=state.scenario.variants.find(v=>v.id===id)||state.scenario.variants[0];
 state.edits={data:state.variant.data,ontology:state.scenario.ontology};
 renderEditorTabs();clearEvaluation();
}
function renderEditorTabs(){
 document.querySelectorAll(".tab").forEach(b=>b.classList.toggle("active",b.dataset.editor===state.editing));
 $("rdfEditor").value=getEdition();
}
function drawPolicy(){
 const value=Number($("orientationSlider").value), s=state.scenario;
 const mode=value<34?"LEAN-FIRST":value>66?"RDF-FIRST":"HYBRID";
 $("orientation").textContent=value+"% RDF · "+mode;
 $("policyMode").textContent=mode;
 $("policyLanguage").textContent=mode==="LEAN-FIRST"?"Lean-oriented semantic specification (sketch)":mode==="HYBRID"?"RDF + fixed-operation policy (sketch)":"SPARQL/RDF policy view (query text)";
 setText("policyText",mode==="LEAN-FIRST"?s.leanFirst:mode==="HYBRID"?s.hybrid:s.rdfFirst);
 $("policyExplanation").textContent=mode==="RDF-FIRST"?"This is a runtime query over arbitrary ontology terms. External checks, if required, are separate fixed operations.":
  mode==="HYBRID"?"Design notation for composing RDF entailments with registered operational checks. The running engine uses explicit queries and fixed JavaScript gates, not this hypothetical DSL.":
  "Lean-style specifications refer to ontology identifiers as runtime RDF terms. This is design notation; the standalone kernel-checkable examples are below.";
}
function clearEvaluation(){
 state.lastEvaluation=null;
 setStatus("rdfStatus","Not run");setStatus("decisionStatus","Not run");setStatus("proofStatus","Not checked");
 setText("rdfSummary","Query the dataset with Factoidal.");
 setText("decisionSummary","Evaluate the example policy against actual query results.");
 setText("proofSummary","The Lean source must be checked in the browser compiler; no kernel success is inferred.");
 setText("rdfTrace","");setText("decisionTrace","");setText("proofTrace","");
 setText("lastRun","NOT EVALUATED");
}
function termValue(binding,v){
 const term=binding?.[v];if(term==null)return null;
 if(typeof term==="string")return term;
 return term.value??term.lexicalForm??null;
}
function unwrap(r){
 if(r&&typeof r==="object"&&r.result&&r.results===undefined&&r.boolean===undefined) return r.result;
 return r;
}
function booleanValue(r){
 r=unwrap(r);
 if(typeof r==="boolean")return r;
 if(typeof r?.boolean==="boolean")return r.boolean;
 if(typeof r?.result?.boolean==="boolean")return r.result.boolean;
 if(typeof r?.results?.boolean==="boolean")return r.results.boolean;
 throw new Error("Factoidal did not return a recognised SPARQL ASK boolean: "+JSON.stringify(r).slice(0,180));
}
function rowsValue(r){
 r=unwrap(r);
 const rows=r?.results?.bindings??r?.bindings??r?.result?.results?.bindings;
 if(!Array.isArray(rows))throw new Error("Factoidal did not return SPARQL SELECT bindings: "+JSON.stringify(r).slice(0,220));
 return rows;
}
function rawOutput(label,obj){return label+" "+JSON.stringify(obj);}
async function loadEngine(){
 if(state.engine)return state.engine;
 setText("engineState","LOADING FACTOIDAL…");
 try {
  const mod=await import("https://danbri.github.io/factoidal/npm/factoidal/browser.js");
  if(typeof mod.query!=="function")throw new Error("Missing query() in Factoidal browser release");
  state.engine=mod;
  $("engineDot").classList.add("live");
  setText("engineState","FACTOIDAL BROWSER");
  return mod;
 }catch(err){
  $("engineDot").classList.remove("live");
  setText("engineState","ENGINE LOAD FAILED");
  throw new Error("Could not load the published Factoidal browser module: "+(err.message||String(err)));
 }
}
async function executeQuery(merged,sparql,regime){
 const mod=await loadEngine();
 const opts=regime==="RDFS"?{entail:"RDFS",output:"json"}:{output:"json"};
 return await mod.query(merged,sparql,opts);
}
function auditDate(s){return Number.isFinite(Date.parse(s))?Date.parse(s):NaN;}
function evaluateDecision(s,matched,rows,more,regime){
 const row=rows[0]||{};
 const audit=s.auditTime||"2026-11-11T12:00:00Z";
 const cutoff=auditDate(audit);
 if(s.id==="offer"){
  const person=termValue(row,"agent")||"unresolved";
  const transport=termValue(row,"transport"),crypto=termValue(row,"encryption");
  const expiry=termValue(row,"expiry");
  const secure=transport==="xmpp"&&crypto==="omemo";
  const fresh=Number.isFinite(auditDate(expiry))&&auditDate(expiry)>cutoff;
  const isOrg=more.org===true,disjointWitness=more.exclude===true;
  const conflicting=isOrg&&disjointWitness;
  let label,summary,tone;
  if(conflicting){label="Conflicting evidence";summary="The queried class exclusion and Organization classification coexist. Escalate: do not use this as a consistent OWL classification.";tone="bad";}
  else if(!matched){label="Classification unresolved";summary="RDFS query did not establish ArtificialAgent for this offer. No closed-world negative conclusion is drawn.";tone="warn";}
  else if(isOrg){label="Organisation route";summary="Positive Organization evidence. This sample does not take the non-organisation ethics route.";tone="good";}
  else if(!disjointWitness){label="Exclusion unproven";summary="ArtificialAgent is established, but no queried class/disjointness witness excludes Organization. Unknown is not false.";tone="warn";}
  else{label="Ethics review required";summary="ArtificialAgent and an explicit class/disjointness witness were found. This is a review requirement, not approval to execute.";tone="good";}
  const permitted=matched&&disjointWitness&&!isOrg&&secure&&fresh;
  return {label,summary,tone,trace:[
   "responsible="+person,"entailed ArtificialAgent="+matched,"positive Organization="+isOrg,
   "explicit disjointness witness="+disjointWitness,"transport "+transport+" / "+crypto+" = "+(secure?"pass":"fail"),
   "credential valid at "+audit+" = "+(fresh?"pass":"fail"),
   "operational precheck="+(permitted?"PASS (not authorised)":"BLOCKED"),
   "No OWL negative entailment or cryptographic proof is claimed."
  ]};
 }
 if(s.id==="event"){
  const consent=termValue(row,"consent")==="yes";
  const expires=termValue(row,"expiry"),fresh=Number.isFinite(auditDate(expires))&&auditDate(expires)>cutoff;
  const pass=matched&&consent&&fresh;
  return {label:pass?"Admission precheck passes":"Admission blocked",tone:pass?"good":"warn",
   summary:pass?"RDFS event classification, attendance, declared consent and validity window pass the demonstration gate.":"At least one required condition is unestablished or false.",
   trace:["RDFS Event and attendee="+matched,"consent declaration="+consent,"inside window="+fresh,"audit clock="+audit,"Consent's real-world validity is not certified."]};
 }
 if(s.id==="artifact"){
  const signature=termValue(row,"signature")==="verified";
  const expires=termValue(row,"expiry"),fresh=Number.isFinite(auditDate(expires))&&auditDate(expires)>cutoff;
  const pass=matched&&!!termValue(row,"reviewer")&&signature&&fresh;
  return {label:pass?"Release flag passes":"Release blocked",tone:pass?"warn":"bad",
   summary:pass?"All asserted RDF flags pass, but the signature is only a string, NOT a cryptographic verification.":"A required assertion, classification or expiry window is missing or failing.",
   trace:["entailed CreativeWork="+matched,"approval field present="+!!termValue(row,"reviewer"),"signature *flag*="+signature,"deadline live="+fresh,"real signature verification=NOT RUN"]};
 }
 const classValues=rows.map(r=>termValue(r,"class")).filter(Boolean);
 return {label:matched?(regime==="RDFS"?"Qualified via RDFS":"Directly qualified"):"Not established",tone:matched?"good":"warn",
  summary:matched?"The novel class supplied in the ontology contributes to a valid subclass entailment.":"No relevant RDF inheritance was established from the current asserted class.",
  trace:["qualifies as ApprovedSupplier="+matched,"query class rows="+classValues.length, ...classValues.slice(0,6).map(v=>"  "+v)]};
}
async function run(){
 const token=++state.runToken,s=state.scenario;
 state.edits[state.editing]=$("rdfEditor").value;
 const merged=state.edits.ontology+"\n"+state.edits.data;
 const regime=$("regime").value;
 $("run").disabled=true;$("run").textContent="Evaluating…";
 setStatus("rdfStatus","Running…");setStatus("decisionStatus","Awaiting RDF…");
 setText("rdfTrace","");
 try {
  const started=performance.now();
  const results=await executeQuery(merged,s.query,regime);
  const rows=rowsValue(results);
  const resultAsk=await executeQuery(merged,s.ask,regime);
  const matched=booleanValue(resultAsk);
  const more={};
  for(const q of s.complementary||[]){more[q.key]=booleanValue(await executeQuery(merged,q.query,regime));}
  if(token!==state.runToken)return;
  const ms=Math.round(performance.now()-started);
  setStatus("rdfStatus",matched?"Entailment established":"Not established",matched?"good":"warn");
  setText("rdfSummary",matched?"Factoidal returned true for the relevant RDF classification query.":"Factoidal did not establish the requested classification; this is not automatically a refutation.");
  setText("rdfTrace",[
    "Engine: Factoidal published browser.js",
    "Regime: "+regime,
    "ASK result: "+matched,
    "SELECT rows: "+rows.length,
    "Elapsed: "+ms+" ms",
    ...Object.entries(more).map(([k,v])=>k+" ASK: "+v)
  ].join("\n"));
  const decision=evaluateDecision(s,matched,rows,more,regime);
  setStatus("decisionStatus",decision.label,decision.tone);
  setText("decisionSummary",decision.summary);
  setText("decisionTrace",decision.trace.join("\n"));
  setStatus("proofStatus","Not kernel checked","warn");
  setText("proofSummary","The Lean source states general obligations over semantic evidence and executable gates. Run it in Lean WASM; this app makes no assertion of Lean kernel acceptance.");
  setText("proofTrace","RDF entailment: executed\nPolicy gate: evaluated\nLean kernel: not run here\nRDF-to-Lean evidence bridge: not proved");
  state.lastEvaluation={scenario:s.id,matched,rows:rows.length,ms,more,decision};
  setText("lastRun","EXECUTED · "+ms+" MS");
 }catch(err){
  if(token!==state.runToken)return;
  setStatus("rdfStatus","Execution error","bad");setStatus("decisionStatus","Not evaluated","warn");
  setText("rdfSummary",err.message||String(err));
  setText("rdfTrace","No fallback engine was used. An RDF result is not fabricated on error.");
  setText("decisionSummary","Cannot evaluate without an RDF result.");
  setText("decisionTrace","");
  setText("lastRun","ERROR");
 }finally{
  if(token===state.runToken){$("run").disabled=false;$("run").innerHTML="Evaluate policy <span>↗</span>";}
 }
}
function copyText(text){
 const fallback=()=>{
  const el=document.createElement("textarea");el.value=text;document.body.appendChild(el);el.select();document.execCommand("copy");el.remove();
 };
 if(navigator.clipboard?.writeText)navigator.clipboard.writeText(text).catch(fallback);
 else fallback();
}
function install(){
 $("scenario").replaceChildren(...scenarios.map(s=>new Option(s.title,s.id)));
 $("scenario").addEventListener("change",ev=>activateSample(ev.target.value));
 $("variant").addEventListener("change",ev=>changeVariant(ev.target.value));
 $("orientationSlider").addEventListener("input",drawPolicy);
 $("run").addEventListener("click",run);
 document.querySelectorAll(".tab").forEach(btn=>btn.addEventListener("click",()=>{
  state.edits[state.editing]=$("rdfEditor").value;
  state.editing=btn.dataset.editor;renderEditorTabs();
 }));
 $("rdfEditor").addEventListener("input",()=>{state.edits[state.editing]=$("rdfEditor").value;});
 $("restore").addEventListener("click",()=>{
  if(state.editing==="data")state.edits.data=selectedVariant().data;
  else state.edits.ontology=state.scenario.ontology;
  renderEditorTabs();clearEvaluation();
 });
 $("copyRdf").addEventListener("click",()=>copyText($("rdfEditor").value));
 $("copyPolicy").addEventListener("click",()=>copyText($("policyText").textContent));
 $("copyLean").addEventListener("click",()=>copyText($("leanEditor").value));
 $("openLean").addEventListener("click",async()=>{
  const source=$("leanEditor").value;
  copyText(source);
  // The actual browser Lean playground accepts a gzip-compressed
  // {files,active} workspace in #s= (client-side only).
  const tab=window.open("about:blank","_blank");
  try{
   if(typeof CompressionStream!=="function")throw new Error("CompressionStream is not supported");
   const workspace={files:[{name:"Main.lean",content:source}],active:"Main.lean"};
   const raw=new TextEncoder().encode(JSON.stringify(workspace));
   const zipped=new Uint8Array(await new Response(new Blob([raw]).stream().pipeThrough(new CompressionStream("gzip"))).arrayBuffer());
   let bin="";for(const b of zipped)bin+=String.fromCharCode(b);
   const hash=btoa(bin).replaceAll("+","-").replaceAll("/","_").replace(/=+$/,"");
   const url="https://lean.cau.li/#s="+hash;
   if(tab)tab.location.href=url;
   else window.location.href=url;
  }catch(err){
   if(tab)tab.location.href="https://lean.cau.li";
   setText("proofSummary","Lean source copied. The browser couldn't package a prefilled Lean workspace: "+err.message);
  }
 });
 $("library").replaceChildren(...scenarios.map((s,i)=>{
  const b=document.createElement("button");b.className="libraryItem";b.innerHTML='<span class="num">0'+(i+1)+' / EXPERIMENT</span><b></b><p></p>';
  b.querySelector("b").textContent=s.short;b.querySelector("p").textContent=s.summary;
  b.addEventListener("click",()=>{activateSample(s.id);document.querySelector(".controls").scrollIntoView({behavior:"smooth",block:"start"});});
  return b;
 }));
 activateSample("offer");
 // Loading is deferred to the first evaluation, keeping the landing page fast.
}
install();