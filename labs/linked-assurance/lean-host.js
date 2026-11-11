import {sha256} from './evidence.js';
let compiler, loading, compilerVersion=null, versionProbe=null, busy=false, checked=null;
export function compilerEnvironment() {
  return {isolated:globalThis.crossOriginIsolated===true,sharedMemory:typeof SharedArrayBuffer!=='undefined',
    sdk:'Dickory worker host; Lean 4.33.1 wasm32',compilerVersion,versionProbe,cache:compiler?.cache||null};
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
export function auditContract(result,name='LinkedAssurance.policy_contract') {
  if(!accepted(result))return false;
  const text=diagnosticText(result);
  const escaped=name.replaceAll('.','\\.');
  const matches=[...text.matchAll(new RegExp(escaped+'[^\\n]*depends on axioms: \\[([^\\]]*)\\]','g'))];
  if(matches.length)return matches.every(m=>m[1].split(',').map(x=>x.trim()).filter(Boolean).every(x=>['propext','Quot.sound','Classical.choice'].includes(x)));
  return new RegExp(escaped+'[^\\n]*does not depend on any axioms').test(text);
}
async function getCompiler(progress) {
  const env=compilerEnvironment();
  if(!env.isolated||!env.sharedMemory)throw Error('compiler_unavailable: cross-origin isolation or SharedArrayBuffer is missing. Enable isolation and reload, or use tools/serve.py --isolate.');
  if(compiler)return compiler;
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
      // the support and policy compilation below must each succeed independently.
      instance.version=compilerVersion;
      compiler=instance;return instance;
    }catch(e){instance.dispose();throw e;}
  })();
  try{return await loading;}finally{loading=null;}
}
async function ensureSupport(lean,progress){
  if(lean.supportSha256)return;
  const response=await fetch('./lean/Workbench.lean');if(!response.ok)throw Error('Workbench source unavailable.');
  const support=await response.text();
  progress('Compiling Workbench.lean; the first library import can take about a minute…');
  const result=await lean.run(support,{moduleName:'Workbench',exportPrefix:'Workbench',flags:['--json','-o','/lib/lean/Workbench.olean']});
  if(!accepted(result)||!result.artifacts.includes('Workbench.olean'))throw Error('Cannot compile the support module. '+diagnosticText(result));
  lean.supportSha256=await sha256(support);
}
export async function checkLean(source,progress=()=>{}){
  if(busy)throw Error('A compiler operation is already running. Please wait for it to finish.');
  busy=true;
  try{
    const lean=await getCompiler(progress);
    progress(lean.session?'Checking this Lean file…':'Importing the Lean library for this session; this can take about a minute even with saved files…');
    let result=await lean.run(source,{moduleName:'Tutorial',persistent:true});
    if(result.runtimeFault){
      const initialFault=result;lean.resetSession();
      progress('Lean reported an internal session failure. Restarting from the saved compiler files and checking again…');
      result={...await lean.run(source,{moduleName:'Tutorial',persistent:true}),restartedAfterRuntimeFault:initialFault};
    }
    return {...result,accepted:accepted(result),compilerVersion:lean.version,sourceSha256:await sha256(source)};
  }finally{busy=false;}
}
export async function compilePolicy(source,progress=()=>{}) {
  if(busy)throw Error('A compiler operation is already running.');
  busy=true;
  try {
    const digest=await sha256(source);
    if(checked?.sourceSha256===digest)return {...checked,cached:true};
    checked=null;
    const lean=await getCompiler(progress);
    await ensureSupport(lean,progress);
    lean.resetSession();
    for(const key of [...lean.libraryFiles.keys()])if(key.startsWith('Policy.'))lean.libraryFiles.delete(key);
    const audit=`\n#check (LinkedAssurance.policy_contract : ∀ (e : LinkedAssurance.Evidence) (s : LinkedAssurance.OperationalState), LinkedAssurance.policy e s = LinkedAssurance.Decision.permit → LinkedAssurance.permitRequirements e s)
#check (LinkedAssurance.policy_pipeline_contract : ∀ (ctx : LinkedAssurance.Context) (execution : LinkedAssurance.Execution) (bindings : List LinkedAssurance.QueryBinding) (observations : List LinkedAssurance.QueryObservation) (e : LinkedAssurance.Evidence) (s : LinkedAssurance.OperationalState), LinkedAssurance.adaptEvidence ctx execution bindings observations = Except.ok e → LinkedAssurance.policy e s = LinkedAssurance.Decision.permit → LinkedAssurance.adapterRequirements ctx execution bindings observations e ∧ LinkedAssurance.permitRequirements e s)
#print axioms LinkedAssurance.policy_contract
#print axioms LinkedAssurance.policy_pipeline_contract
#print axioms LinkedAssurance.adaptEvidence_contract
`;
    progress('Compiling Policy.lean and checking its required contract…');
    const result=await lean.run(source+audit,{moduleName:'Policy',exportPrefix:'Policy',flags:['--json','-o','/lib/lean/Policy.olean']});
    const contractChecked=['LinkedAssurance.policy_contract','LinkedAssurance.policy_pipeline_contract','LinkedAssurance.adaptEvidence_contract'].every(name=>auditContract(result,name))&&result.artifacts.includes('Policy.olean');
    const out={...result,contractChecked,sourceSha256:digest,compiledSourceSha256:await sha256(source+audit),
      supportSha256:lean.supportSha256,compilerVersion:lean.version};
    if(contractChecked)checked=out;
    return out;
  }finally{busy=false;}
}
export async function executePolicy(source,fixture,progress=()=>{}) {
  if(busy)throw Error('A compiler operation is already running.');
  if(!checked||checked.sourceSha256!==await sha256(source))throw Error('Compile the current policy and its contract first.');
  busy=true;
  try {
    progress('Importing the checked Policy.olean; evaluating the current fixture…');
    // Only the small runtime fixture is elaborated. The policy module is reused.
    const result=await compiler.run(fixture,{moduleName:'Run',flags:['--json'],persistent:true});
    const text=diagnosticText(result);
    const match=text.match(/LinkedAssurance\.Decision\.(permit|deny|defer|escalate|protectiveShutdown)\s*,\s*LinkedAssurance\.AttackOutcome\.(achieved|notAchieved|unknown)/);
    const executed=accepted(result)&&!!match;
    progress(executed?`Finished: policy returned ${match[1]}; attacker outcome ${match[2]}.`:'No policy decision produced. Inspect the compiler diagnostics.');
    return {...result,executed,decision:match?.[1],attacker:match?.[2],
      sourceSha256:checked.sourceSha256,fixtureSha256:await sha256(fixture),compilerVersion:compiler.version};
  }finally{busy=false;}
}
