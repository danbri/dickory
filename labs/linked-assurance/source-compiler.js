// SPDX-License-Identifier: Apache-2.0
// Fresh compiler state per source request: never replace the UI's checked Policy.
import {sourceRequest,compilationReceipt,compilationFault,describeArtifacts} from './profile/lean-source.js';
import {sha256} from './evidence.js';
let active=false;
export async function compileBrowserSource(input,options={}){
  const request=sourceRequest(input),identity={host:'browser-wasm',version:'Lean 4.33.1 wasm32',commit:'4f9018a62ead9be0ffd652021d5afc8501e92253'};
  if(active)return compilationFault(request,'compiler_busy','A source compilation is already running.',identity);
  if(!globalThis.isSecureContext||!globalThis.crossOriginIsolated||typeof SharedArrayBuffer==='undefined')return compilationFault(request,'compiler_unavailable','An isolated HTTPS/localhost document with SharedArrayBuffer is required.',identity);
  if(options.signal?.aborted)return compilationFault(request,'cancelled','Cancelled before setup.',identity);
  active=true;
  let lean,stopped=null,timer,abort,rejectStop;
  const stopPromise=new Promise((_,reject)=>{rejectStop=reject;});
  const stop=reason=>{if(stopped)return;stopped=reason;lean?.dispose();rejectStop(Error(reason));};
  const check=()=>{if(stopped){lean?.dispose();throw Error(stopped);}};
  abort=()=>stop('cancelled');options.signal?.addEventListener('abort',abort,{once:true});
  timer=setTimeout(()=>stop('timeout'),request.budgetMs);
  if(options.signal?.aborted)abort();
  const work=(async()=>{
    const {Lean4}=await import('./compiler.js');check();
    lean=new Lean4({timeout:request.budgetMs,onProgress:options.onProgress||(()=>{})});
    await lean.init();check();
    identity.runtimeSha256=lean.runtimeSha256;
    if(request.environment==='workbench'){
      const {installSupportBundle}=await import('./lean-host.js');check();
      const [source,bundle]=await Promise.all([
        fetch(new URL('./lean/Workbench.lean',import.meta.url)),
        fetch(new URL('./artifacts/workbench-wasm.json',import.meta.url))
      ]);
      if(!source.ok||!bundle.ok)throw Error('compiler_unavailable: matching Workbench module unavailable');
      await installSupportBundle(lean,await bundle.json(),await sha256(await source.text()));check();
    }
    // This uses the actual CLI export path, not the warm checker that emits no module.
    const result=await lean.run(request.source,{moduleName:'Script',exportPrefix:'Script',flags:['--json','-o','/lib/lean/Script.olean']});check();
    const entries=(result.artifacts||[]).map(name=>[name,lean.libraryFiles.get(name)]).filter(([,bytes])=>bytes);
    const artifacts=await describeArtifacts(entries,request.includeArtifacts);check();
    return compilationReceipt(request,result,artifacts,identity);
  })();
  try{return await Promise.race([work,stopPromise]);}
  catch(e){
    const message=String(e.message||e),status=stopped||(message.includes('_limit')?'resource_limit':message.includes('compiler_unavailable')?'compiler_unavailable':'compiler_fault');
    return await compilationFault(request,status,message,identity);
  }finally{
    clearTimeout(timer);options.signal?.removeEventListener('abort',abort);lean?.dispose();
    // Pending asset preparation may still finish after cancellation. The work
    // checks stopped before spawning a compiler. Hold the source-session lock
    // until it settles, avoiding overlapping initialisations after a timeout.
    if(stopped)work.catch(()=>{}).finally(()=>{lean?.dispose();active=false;});
    else active=false;
  }
}
