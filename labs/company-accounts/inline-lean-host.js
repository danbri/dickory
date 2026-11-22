/**
 * Same-origin, on-device Lean 4.33.1 compiler for the Company Accounts lab.
 * Uses Dickory's existing verified cauli/lean4 Init/IR library, the existing
 * worker API, and an export-pruned variant of that EXACT same WASM executable.
 * The original executable code sections remain byte-for-byte intact.
 *
 * This is distinct from cauli's relinked 4.33.0-pre slim runtime and does not
 * rebrand a native/CI proof as an interactive local proof.
 */
import {Lean4} from '../linked-assurance/compiler.js';
import {loadCompilerAssets} from '../linked-assurance/compiler-cache.js';
import {accepted,diagnosticText} from '../linked-assurance/lean-host.js';
import {sha256Source} from './proof-evidence.js';

const PIN='4f9018a62ead9be0ffd652021d5afc8501e92253';
let instance=null,loading=null,busy=false;
export function mobileLeanAvailable(){
  if(!globalThis.isSecureContext)return 'Requires HTTPS or localhost.';
  if(globalThis.window&&window.self!==window.top)return 'Open in a full browser tab.';
  if(!globalThis.crossOriginIsolated)return 'Browser isolation is required. Enable isolation and reload first.';
  if(typeof SharedArrayBuffer==='undefined')return 'SharedArrayBuffer is unavailable.';
  return null;
}
async function assets(progress){
  const response=await fetch(new URL('./artifacts/slim-compiler-assets.json',import.meta.url),
    {cache:'no-store'});
  if(!response.ok)throw Error('Pinned Lean 4.33.1 slim asset manifest unavailable');
  const manifest=await response.json();
  if(manifest.sourceCommit!==PIN||
      manifest.leanVersion!=='4.33.1'||
      manifest.factoidalPin!=='leanprover/lean4:v4.33.1'||
      Object.keys(manifest.runtime||{}).sort().join(',')!=='lean-lib.tar.gz,lean.js,lean.wasm')
    throw Error('Mobile compiler does not match Factoidal Core Lean 4.33.1');
  return loadCompilerAssets(manifest.runtime,progress);
}
async function getCompiler(progress){
  const unavailable=mobileLeanAvailable();
  if(unavailable)throw Error(unavailable);
  if(instance){instance.onProgress=progress;return instance;}
  if(loading)return loading;
  loading=(async()=>{
    const lean=new Lean4({
      timeout:180000,onProgress:progress,
      assetLoader:assets,expectedVersion:'4.33.1',expectedCommit:PIN,
      workerURL:new URL('./inline-lean-worker.js',import.meta.url)
    });
    try{
      await lean.init();
      lean.version='Lean 4.33.1 wasm32; cauli fork '+PIN+'; Dickory export-pruned binary';
      instance=lean;
      return lean;
    }catch(e){lean.dispose();throw e;}
  })();
  try{return await loading;}finally{loading=null;}
}
export async function checkMobileLean(source,progress=()=>{}){
  if(busy)throw Error('A mobile Lean check is already running.');
  busy=true;
  try {
    const lean=await getCompiler(progress);
    progress(lean.session?'Compiling in the same on-device Lean session…':
      'Importing pinned Init library for real on-device Lean 4.33.1…');
    const result=await lean.run(source,{moduleName:'MobileAccounts',persistent:true});
    if(result.runtimeFault)lean.resetSession();
    const message=diagnosticText(result);
    return {
      ...result,accepted:!result.runtimeFault&&accepted(result),
      sourceSha256:await sha256Source(source),
      compilerVersion:lean.version,
      diagnostics:message,
      verificationLocation:'on-device Lean/WASM worker',
    };
  }catch(error){
    if(instance){instance.resetSession();}
    throw error;
  }finally{busy=false;}
}
export function releaseMobileLean(){
  if(instance)instance.dispose();
  instance=null;loading=null;busy=false;
}
