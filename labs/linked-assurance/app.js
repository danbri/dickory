import {scenarios,variants} from './scenarios.js';
import {runtime,sha256,scopeFrom,queriesFrom,startRdf,fixtureSource} from './evidence.js';
import {verifyCredential} from './credential.js';
import {compilerEnvironment,compilePolicy,executePolicy} from './lean-host.js';
import {mountTutorial} from './tutorial.js';
import {mountCompilerBanner,enableIsolation} from './compiler-banner.js';
import {pipelineRecord} from './pipeline-record.js';
const $=id=>document.getElementById(id), show=(id,text)=>{$(id).textContent=text;};
const state={scenario:scenarios[0],editor:'dataset',inputs:{},evaluation:null,job:null,epoch:0,record:null,compiled:null};
const json=x=>JSON.stringify(x,null,2);
mountCompilerBanner($('compilerBanner'));
mountTutorial($('tutorialPanel'));
let lastLearnHash=location.hash.startsWith('#learn')?location.hash:'#learn';
function pageTab(){
  const learn=location.hash.startsWith('#learn');
  if(learn)lastLearnHash=location.hash;
  if(location.hash==='#proof-walkthrough')$('proof-walkthrough').open=true;
  $('tutorialPanel').hidden=!learn;$('workbenchPanel').hidden=learn;
  for(const [id,selected] of [['learnTab',learn],['workbenchTab',!learn]]){$(id).setAttribute('aria-selected',String(selected));$(id).tabIndex=selected?0:-1;}
}
$('learnTab').onclick=()=>{location.hash=lastLearnHash;};$('workbenchTab').onclick=()=>{location.hash='workbench';};
for(const id of ['learnTab','workbenchTab'])$(id).onkeydown=e=>{if(['ArrowLeft','ArrowRight','Home','End'].includes(e.key)){e.preventDefault();const other=e.key==='Home'?'workbenchTab':e.key==='End'?'learnTab':id==='learnTab'?'workbenchTab':'learnTab';$(other).click();$(other).focus();}};
window.addEventListener('hashchange',pageTab);pageTab();
let defaultPolicy,credential;
function invalidate(rdf=true) {
  state.epoch++;state.job?.cancel();state.job=null;state.record=null;
  show('credentialState','Not checked for current inputs.');
  if(rdf){state.evaluation=null;show('knowledge','Not evaluated');show('execution','Not run');show('executionNote','RDF work is terminated at its deadline.');show('rdfReport','');}
  $('cancel').disabled=true;show('decisionNote','Only the compiled Lean function produces this result.');
  show('decision','Not run');show('attackOutcome','Unknown');show('fixture','');show('manifest','');
  show('policyRunSummary','No result for the current inputs.');
}
function activate(s) {
  invalidate();state.scenario=s;
  state.inputs={dataset:s.dataset,queries:json(s.queries),description:s.description};
  $('variant').replaceChildren(...variants(s).map(v=>new Option(v.name,v.id)));
  $('attacker').value=s.id==='alert'?'interrupt':'none';
  show('scenarioNote',s.note);$('rdfEditor').value=state.inputs[state.editor];
  document.querySelectorAll('#catalogue button').forEach(b=>b.setAttribute('aria-current',String(b.dataset.id===s.id)));
}
function progress(text){show('compilerState',text);}
function inputSnapshot(){return {...state.inputs,scope:scopeFrom($('scope').value),regime:$('regime').value,queries:queriesFrom(state.inputs.queries)};}
async function evaluate() {
  invalidate();const epoch=state.epoch,request=inputSnapshot(),started=performance.now();
  state.job=startRdf(request,Number($('budget').value));
  $('cancel').disabled=false;show('execution','Running');show('status','Evaluating the selected graph with Factoidal…');
  const result=await state.job.promise;
  if(epoch!==state.epoch)return null;
  state.job=null;$('cancel').disabled=true;
  result.elapsedMs=Math.round(performance.now()-started);
  state.evaluation={request,result};
  const classified=result.claims?.find(c=>c.key==='classification')?.answer===true;
  show('knowledge',result.execution==='unsupported'?'Unsupported':classified?'Entailed (engine result)':'Not established');
  show('execution',result.execution);show('executionNote',result.error||`${result.elapsedMs} ms; ${result.dataset.selectedQuads} selected triples; ${result.dataset.defaultQuads} default-graph triples.`);
  show('rdfReport',json(result));show('status','RDF evaluation recorded. Policy has not run.');
  return state.evaluation;
}
async function compile() {
  const source=$('leanEditor').value;
  $('compile').disabled=true;
  try {
    const result=await compilePolicy(source,progress);
    show('compilerReport',json(result));
    if(source!==$('leanEditor').value){progress('Source changed during compilation; compile the current text.');return;}
    state.compiled=result.contractChecked?result:null;
    progress(result.contractChecked?'Policy contract checked; compiled module ready.':'Contract rejected. Inspect compiler diagnostics.');
  }catch(e){state.compiled=null;progress(String(e.message||e));show('compilerReport',String(e.stack||e));}
  finally{$('compile').disabled=false;}
}
async function prepareFixture() {
  if(!state.evaluation)await evaluate();
  if(!state.evaluation)return;
  const epoch=state.epoch,{request,result}=state.evaluation,source=$('leanEditor').value;
  const observedTime=Date.parse($('clock').value);
  if(!/(Z|[+-]\d{2}:\d{2})$/.test($('clock').value)||!Number.isSafeInteger(observedTime)||observedTime<0)throw Error('Enter an ISO timestamp with a time zone.');
  const payload=$('credentialPayload').value,signature=$('signature').value,scenario=state.scenario.id;
  const verification=await verifyCredential(credential.publicKey,payload,signature);
  if(epoch!==state.epoch)return null;
  show('credentialState',verification.verified?'ECDSA signature verified for the displayed demo payload.':'Credential check failed.');
  const operational={credentialVerified:verification.verified,observedTime,expiresAt:verification.expiresAt,
    secureTransportObserved:$('transport').value==='secure',permissionGranted:$('permission').value==='yes',
    attackerWantsInterruption:$('attacker').value==='interrupt',legitimateSession:state.scenario.id==='alert'};
  const fallback={datasetBytesSha256:await sha256(request.dataset),selectedGraphSha256:'unavailable',scope:json(request.scope),regime:request.regime,runtimeVersion:runtime.version};
  if(epoch!==state.epoch)return null;
  const fixture=fixtureSource(result,operational,fallback,request.queries);
  const identities={datasetBytesSha256:fallback.datasetBytesSha256,queriesSha256:await sha256(json(request.queries)),
    descriptionSha256:await sha256(request.description),policySourceSha256:await sha256(source),fixtureSha256:await sha256(fixture),
    meaning:'SHA-256 of exact UTF-8 serialization; not RDF canonicalization'};
  if(epoch!==state.epoch)return null;
  show('fixture',fixture);
  return {epoch,scenario,request,result,source,payload,signature,verification,operational,fixture,identities};
}
async function prepareOnly() {
  const p=await prepareFixture();if(!p||p.epoch!==state.epoch)return;
  state.record={schema:'linked-assurance-experiment-v1',scenario:p.scenario,
    pipeline:pipelineRecord({rdf:p.result,verification:p.verification,identities:p.identities}),
    input:{...p.request,policy:p.source,credentialPayload:p.payload,credentialSignature:p.signature,operational:p.operational},
    identities:p.identities,credentialVerification:p.verification,
    rdf:p.result,fixture:p.fixture,policyExecution:{executed:false,reason:'Policy not run'},
    environment:compilerEnvironment(),runtime,
    assumptions:['RDF-to-Lean serialization is unproved.','No Lean policy result or RDF refutation is inferred.']};
  show('manifest',json(state.record));show('status','Fixture and evidence ready to export. Policy not run.');
}
async function runPolicy() {
  show('policyRunSummary','Preparing the evidence and operational inputs…');
  if(!state.compiled||state.compiled.sourceSha256!==await sha256($('leanEditor').value))throw Error('Compile the current policy and contract first.');
  const prepared=await prepareFixture();if(!prepared)return;
  const {epoch,scenario,request,result,source,payload,signature,verification,operational,fixture,identities}=prepared;
  $('runPolicy').disabled=true;
  const started=performance.now();let phase='Starting the compiled policy…';
  const report=text=>{phase=text;if(epoch===state.epoch){progress(text);show('policyRunSummary',text);}};
  const timer=setInterval(()=>{if(epoch===state.epoch)show('policyRunSummary',phase+' · '+Math.round((performance.now()-started)/1000)+' s');},1000);
  try {
    const execution=await executePolicy(source,fixture,report);
    if(epoch!==state.epoch)return;
    show('decision',execution.executed?execution.decision:'compilerFault');
    show('attackOutcome',execution.executed?execution.attacker:'unknown');
    show('decisionNote',execution.executed?'Computed by the compiled Policy.olean on the displayed fixture.':'No policy decision available. Inspect diagnostics.');
    show('policyRunSummary',execution.executed?`Result: ${execution.decision} · attacker outcome: ${execution.attacker} · ${(performance.now()-started)/1000<1?'under 1':Math.round((performance.now()-started)/1000)} s`:'No decision produced. Open compiler diagnostics below.');
    show('compilerReport',json({compile:state.compiled,execution}));
    state.record={schema:'linked-assurance-experiment-v1',scenario,
      pipeline:pipelineRecord({rdf:result,verification,identities,compile:state.compiled,execution}),
      input:{...request,policy:source,credentialPayload:payload,credentialSignature:signature,operational},
      identities,fixture,rdf:result,credentialVerification:verification,compile:state.compiled,policyExecution:execution,
      environment:compilerEnvironment(),runtime,
      assumptions:['TriG parsing, graph selection and query execution use Factoidal 0.35.1.',
        'The JavaScript/RDF-to-Lean fixture translation is not formally proved.',
        'Graph-description evidence is separate from SPARQL-to-policy correspondence.',
        'The demo key authenticates only its credential payload.',
        'Clock, transport and permission are user-selected test observations.',
        'Lean execution uses compiler/runtime machinery; #eval is not a kernel proof of that execution.',
        'An attacker outcome uses the declared synthetic objective and test oracle. Harm prevention is unknown.']};
    show('manifest',json(state.record));show('status','Evidence record ready.');
  }finally{clearInterval(timer);$('runPolicy').disabled=false;}
}
function guard(fn){return async()=>{try{await fn();}catch(e){show('status',String(e.message||e));$('cancel').disabled=true;}};}
async function init() {
  const responses=await Promise.all([fetch('./lean/Policy.lean'),fetch('./demo-credential.json')]);
  if(responses.some(r=>!r.ok))throw Error('Required lab sources could not be loaded.');
  defaultPolicy=await responses[0].text();credential=await responses[1].json();
  $('leanEditor').value=defaultPolicy;$('credentialPayload').value=credential.payload;$('signature').value=credential.signature;
  $('catalogue').replaceChildren(...scenarios.map(s=>{const b=document.createElement('button');b.textContent=s.title;b.dataset.id=s.id;b.onclick=()=>activate(s);return b;}));
  document.querySelectorAll('[data-editor]').forEach(b=>b.onclick=()=>{
    state.inputs[state.editor]=$('rdfEditor').value;state.editor=b.dataset.editor;$('rdfEditor').value=state.inputs[state.editor];
    document.querySelectorAll('[data-editor]').forEach(t=>t.setAttribute('aria-selected',String(t===b)));
  });
  $('rdfEditor').oninput=()=>{state.inputs[state.editor]=$('rdfEditor').value;invalidate();};
  $('leanEditor').oninput=()=>{state.compiled=null;invalidate(false);progress('Source changed. Compile the current policy.');};
  $('variant').onchange=()=>{state.inputs.dataset=variants(state.scenario).find(v=>v.id===$('variant').value).dataset;invalidate();if(state.editor==='dataset')$('rdfEditor').value=state.inputs.dataset;};
  $('restore').onclick=()=>activate(state.scenario);
  $('resetPolicy').onclick=()=>{$('leanEditor').value=defaultPolicy;state.compiled=null;invalidate(false);};
  for(const id of ['scope','regime','budget'])$(id).onchange=()=>invalidate();
  for(const id of ['clock','transport','permission','attacker','credentialPayload','signature'])$(id).oninput=()=>invalidate(false);
  $('prepare').onclick=guard(prepareOnly);$('evaluate').onclick=guard(evaluate);$('compile').onclick=guard(compile);$('runPolicy').onclick=guard(async()=>{
    try{await runPolicy();}catch(e){show('policyRunSummary','Policy did not run: '+e.message);progress('Policy run stopped. See the result message above.');throw e;}
  });
  $('cancel').onclick=()=>state.job?.cancel();
  $('download').onclick=guard(async()=>{
    if(!state.record)throw Error('Evaluate RDF and prepare a fixture, or run the compiled policy first.');
    const url=URL.createObjectURL(new Blob([json(state.record)],{type:'application/json'}));
    const a=document.createElement('a');a.href=url;a.download='linked-assurance-evidence.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
  });
  $('isolate').onclick=guard(enableIsolation);
  const env=compilerEnvironment();progress(env.isolated?'Ready for Lean 4.33.1. Load the compiler using the banner above, or compile to load it now.':'First use: enable running Lean in the banner above. This reloads the page once.');
  $('isolate').hidden=env.isolated;activate(scenarios[0]);
  // Retain edits across the one-time isolation reload; do not persist credentials
  // beyond this tab's session or silently reuse a previous execution result.
  try{
    const saved=JSON.parse(sessionStorage.getItem('linked-assurance-reload')||'null');sessionStorage.removeItem('linked-assurance-reload');
    if(saved){activate(scenarios.find(s=>s.id===saved.scenario)||scenarios[0]);state.inputs=saved.inputs;$('rdfEditor').value=state.inputs[state.editor];for(const [id,value] of Object.entries(saved.controls))if($(id))$(id).value=value;}
  }catch{}
  window.addEventListener('lean-before-reload',()=>{
    try{sessionStorage.setItem('linked-assurance-reload',json({scenario:state.scenario.id,inputs:state.inputs,
      controls:Object.fromEntries(['leanEditor','variant','scope','regime','budget','clock','transport','permission','attacker','credentialPayload','signature'].map(id=>[id,$(id).value]))}));}catch{}
  });
}
init().catch(e=>show('status',String(e.message||e)));
