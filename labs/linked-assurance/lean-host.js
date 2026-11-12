import {sha256} from './evidence.js';
let compiler, loading, compilerVersion=null, versionProbe=null, busy=false, checked=null;
const runKey='linked-assurance-lean-run-v1';
let currentRun=null,previousRun=null;
try{previousRun=JSON.parse(globalThis.sessionStorage?.getItem(runKey)||'null');}catch{}
export function compilerRunSnapshot(){return {current:currentRun,previous:previousRun};}
function recordRun(update){
  currentRun={...currentRun,...update,updatedAt:new Date().toISOString()};
  try{globalThis.sessionStorage?.setItem(runKey,JSON.stringify(currentRun));}catch{}
  globalThis.window?.dispatchEvent(new Event('lean-runtime-status'));
}
function beginRun(activity,progress){
  currentRun=null;recordRun({activity,status:'running',phase:'Starting',startedAt:new Date().toISOString()});
  return phase=>{recordRun({phase});progress(phase);};
}
function finishRun(status,error){recordRun({status,memory:compiler?.memory||null,...(error?{error:String(error.message||error).slice(0,500)}:{})});}
export function compilerEnvironment() {
  return {isolated:globalThis.crossOriginIsolated===true,sharedMemory:typeof SharedArrayBuffer!=='undefined',
    secureContext:globalThis.isSecureContext===true,embedded:typeof window!=='undefined'&&window.self!==window.top,
    serviceWorkerAvailable:!!globalThis.navigator?.serviceWorker,serviceWorkerControlled:!!globalThis.navigator?.serviceWorker?.controller,
    sdk:'Dickory worker host; Lean 4.33.1 wasm32',compilerVersion,versionProbe,cache:compiler?.cache||null};
}
export function compilerUnavailableReason(){
  const env=compilerEnvironment();
  if(!env.secureContext)return 'compiler_unavailable: this page needs HTTPS or a localhost address.';
  if(env.embedded)return 'compiler_unavailable: open this page directly in Safari or a desktop browser, outside the embedded view.';
  if(!env.isolated)return 'compiler_unavailable: cross-origin isolation is missing. Use Enable browser isolation once. If it remains unavailable after reload, open this URL directly in Safari or a desktop browser; repeated reloads will not fix an unsupported browser. See Browser details above.';
  if(!env.sharedMemory)return 'compiler_unavailable: this browser isolates the page but does not expose SharedArrayBuffer. Try a full Safari or desktop browser. See Browser details above.';
  return null;
}
function messages(result) {
  return [result.stdout,result.stderr].join('\n').split('\n').flatMap(line=>{
    try {const m=JSON.parse(line);return m.severity?[m]:[];}catch{return [];}
  });
}
export function diagnosticText(result) {
  return messages(result).map(m=>m.data||m.message||'').join('\n')+'\n'+result.stdout+'\n'+result.stderr;
}
export function accepted(result) {
  return result.exitCode===0 && !messages(result).some(m=>m.severity==='error') && !hasProofPlaceholder(result);
}
export function hasProofPlaceholder(result){
  return messages(result).some(m=>m.kind==='hasSorry'||/declaration uses [`']sorry[`']/.test(m.data||m.message||''));
}
export function proofDiagnostic(result){
  if(hasProofPlaceholder(result))return 'The proof contains sorry, which is a placeholder. Replace it with a completed proof.';
  const error=messages(result).find(m=>m.severity==='error');
  if(error)return (error.pos?'Line '+error.pos.line+': ':'')+(error.data||error.message||'Lean reported an error.').split('\n').slice(0,3).join('\n');
  return 'The required contract or its axiom check did not pass. Full diagnostics are available in Advanced results.';
}
export function auditContract(result,name='LinkedAssurance.policy_contract') {
  if(!accepted(result))return false;
  const text=diagnosticText(result);
  const escaped=name.replaceAll('.','\\.');
  const matches=[...text.matchAll(new RegExp(escaped+'[^\\n]*depends on axioms: \\[([^\\]]*)\\]','g'))];
  if(matches.length)return matches.every(m=>m[1].split(',').map(x=>x.trim()).filter(Boolean).every(x=>['propext','Quot.sound','Classical.choice'].includes(x)));
  return new RegExp(escaped+'[^\\n]*does not depend on any axioms').test(text);
}
async function getCompiler(progress) {
  const unavailable=compilerUnavailableReason();
  if(unavailable)throw Error(unavailable);
  if(compiler){compiler.onProgress=progress;return compiler;}
  if(loading)return loading;
  loading=(async()=>{
    const {Lean4}=await import('./compiler.js');
    const instance=new Lean4({timeout:180000,onProgress:progress});
    try {
      await instance.init();
      progress('Initialising Lean 4.33.1 in a worker…');
      const version=await instance.run('-- Compiler version probe\n',{flags:['--version']});
      versionProbe=version;
      compilerVersion=version.stdout.match(/Lean \(version[^\n]+/)?.[0]||null;
      if(!compilerVersion)throw Error('compiler_unavailable: compiler version probe produced no version.\n'+diagnosticText(version));
      // This informational probe is not a proof check. Preserve its exit status;
      // the published-module checks or local policy compilation are separate.
      instance.version=compilerVersion;
      compiler=instance;return instance;
    }catch(e){instance.dispose();throw e;}
  })();
  try{return await loading;}finally{loading=null;}
}
export async function installSupportBundle(lean,bundle,sourceSha256,moduleName='Workbench'){
  if(!['Workbench','Policy'].includes(moduleName))throw Error('Unexpected module name.');
  if(bundle.status!=='pass'||bundle.sourceSha256!==sourceSha256||Object.entries(lean.compilerSha256).some(([name,hash])=>bundle.compilerSha256?.[name]!==hash))throw Error('Fixed support build does not match its source and compiler.');
  const files=new Map();
  for(const file of bundle.files){
    if(!new RegExp('^'+moduleName+'\\.(olean(\\.(private|server))?|ir(\\.sig)?)$').test(file.name)||files.has(file.name))throw Error('Unexpected support module file.');
    const bytes=Uint8Array.from(atob(file.base64),c=>c.charCodeAt(0));
    if(bytes.length!==file.bytes||await sha256(bytes)!==file.sha256)throw Error('Fixed support module checksum mismatch.');
    files.set(file.name,bytes);
  }
  if(!files.has(moduleName+'.olean'))throw Error('Fixed support module missing.');
  for(const [name,bytes] of files)lean.libraryFiles.set(name,bytes);
  if(moduleName==='Workbench')lean.supportSha256=sourceSha256;
}
async function ensureSupport(lean,progress){
  if(lean.supportSha256)return;
  const response=await fetch('./lean/Workbench.lean');if(!response.ok)throw Error('Workbench source unavailable.');
  const support=await response.text();
  progress('Loading the fixed support module built with this compiler…');
  const bundleResponse=await fetch('./artifacts/workbench-wasm.json');
  if(!bundleResponse.ok)throw Error('Fixed support build unavailable. Run node tools/build_modules.cjs after preparing the compiler.');
  await installSupportBundle(lean,await bundleResponse.json(),await sha256(support));
}
export async function checkLean(source,progress=()=>{}){
  if(busy)throw Error('A compiler operation is already running. Please wait for it to finish.');
  busy=true;progress=beginRun('Lean file check',progress);
  try{
    const lean=await getCompiler(progress);
    progress(lean.session?'Checking this Lean file…':'Importing the Lean library for this session; this can take about a minute even with saved files…');
    let result=await lean.run(source,{moduleName:'Tutorial',persistent:true});
    if(result.runtimeFault&&!/Maximum call stack|stack overflow/i.test(diagnosticText(result))){
      const initialFault=result;lean.resetSession();
      progress('Lean reported an internal session failure. Restarting from the saved compiler files and checking again…');
      result={...await lean.run(source,{moduleName:'Tutorial',persistent:true}),restartedAfterRuntimeFault:initialFault};
    }
    if(result.runtimeFault)lean.resetSession();
    finishRun(result.runtimeFault?'error':accepted(result)?'accepted':'rejected',result.runtimeFault?Error(diagnosticText(result)):undefined);
    return {...result,accepted:accepted(result),compilerVersion:lean.version,sourceSha256:await sha256(source)};
  }catch(e){finishRun('error',e);throw e;}finally{busy=false;}
}
export async function compilePolicy(source,progress=()=>{}) {
  if(busy)throw Error('A compiler operation is already running.');
  busy=true;progress=beginRun('Policy compilation',progress);
  try {
    const digest=await sha256(source);
    if(checked?.sourceSha256===digest){finishRun('accepted');return {...checked,cached:true};}
    checked=null;
    const lean=await getCompiler(progress);
    await ensureSupport(lean,progress);
    lean.resetSession();
    for(const key of [...lean.libraryFiles.keys()])if(key.startsWith('Policy.'))lean.libraryFiles.delete(key);
    const publishedResponse=await fetch('./artifacts/policy-wasm.json');
    if(publishedResponse.ok){
      const bundle=await publishedResponse.json();
      if(bundle.sourceSha256===digest){
        if(bundle.compiledSourceSha256!==await sha256(source+policyAudit)||bundle.supportSha256!==lean.supportSha256||!['policy_contract','policy_pipeline_contract','adaptEvidence_contract'].every(name=>auditContract(bundle.result,'LinkedAssurance.'+name)))throw Error('Published policy contract audit does not match this source and support module.');
        await installSupportBundle(lean,bundle,digest,'Policy');
        checked={...bundle.result,contractChecked:true,verificationLocation:'site build',sourceSha256:digest,compiledSourceSha256:bundle.compiledSourceSha256,supportSha256:lean.supportSha256,compilerVersion:lean.version,artifacts:bundle.files.map(f=>f.name)};
        progress('Published policy proof checked during the site build; exact source and compiler match.');
        finishRun('accepted');return checked;
      }
    }
    progress('Compiling Policy.lean and checking its required contract…');
    const result=await lean.run(source+policyAudit,{moduleName:'Policy',exportPrefix:'Policy',flags:['--json','-o','/lib/lean/Policy.olean']});
    const contractChecked=['LinkedAssurance.policy_contract','LinkedAssurance.policy_pipeline_contract','LinkedAssurance.adaptEvidence_contract'].every(name=>auditContract(result,name))&&result.artifacts.includes('Policy.olean');
    const out={...result,contractChecked,verificationLocation:'browser',sourceSha256:digest,compiledSourceSha256:await sha256(source+policyAudit),
      supportSha256:lean.supportSha256,compilerVersion:lean.version};
    if(contractChecked)checked=out;
    finishRun(contractChecked?'accepted':'rejected');
    return out;
  }catch(e){finishRun('error',e);throw e;}finally{busy=false;}
}
export async function executePolicy(source,fixture,progress=()=>{}) {
  if(busy)throw Error('A compiler operation is already running.');
  if(!checked||checked.sourceSha256!==await sha256(source))throw Error('Compile the current policy and its contract first.');
  busy=true;progress=beginRun('Policy execution',progress);compiler.onProgress=progress;
  try {
    progress('Importing the checked Policy.olean; evaluating the current fixture…');
    // Only the small runtime fixture is elaborated. The policy module is reused.
    const result=await compiler.run(fixture,{moduleName:'Run',flags:['--json'],persistent:true});
    const text=diagnosticText(result);
    const match=text.match(/LinkedAssurance\.Decision\.(permit|deny|defer|escalate|protectiveShutdown)\s*,\s*LinkedAssurance\.AttackOutcome\.(achieved|notAchieved|unknown)/);
    const executed=accepted(result)&&!!match;
    progress(executed?`Finished: policy returned ${match[1]}; attacker outcome ${match[2]}.`:'No policy decision produced. Inspect the compiler diagnostics.');
    finishRun(executed?'completed':'error');
    return {...result,executed,decision:match?.[1],attacker:match?.[2],
      sourceSha256:checked.sourceSha256,fixtureSha256:await sha256(fixture),compilerVersion:compiler.version};
  }catch(e){finishRun('error',e);throw e;}finally{busy=false;}
}

export const policyAudit=`\n#check (LinkedAssurance.policy_contract : ∀ (e : LinkedAssurance.Evidence) (s : LinkedAssurance.OperationalState), LinkedAssurance.policy e s = LinkedAssurance.Decision.permit → LinkedAssurance.permitRequirements e s)
#check (LinkedAssurance.policy_pipeline_contract : ∀ (ctx : LinkedAssurance.Context) (execution : LinkedAssurance.Execution) (bindings : List LinkedAssurance.QueryBinding) (observations : List LinkedAssurance.QueryObservation) (e : LinkedAssurance.Evidence) (s : LinkedAssurance.OperationalState), LinkedAssurance.adaptEvidence ctx execution bindings observations = Except.ok e → LinkedAssurance.policy e s = LinkedAssurance.Decision.permit → LinkedAssurance.adapterRequirements ctx execution bindings observations e ∧ LinkedAssurance.permitRequirements e s)
#print axioms LinkedAssurance.policy_contract
#print axioms LinkedAssurance.policy_pipeline_contract
#print axioms LinkedAssurance.adaptEvidence_contract
`;
