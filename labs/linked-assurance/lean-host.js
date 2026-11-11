// The Lean 4 compiler runs inside this app's isolated browser context.
// The SDK (MIT) loads real Lean WebAssembly and Init oleans; NO fake proof result.
let lean=null,loading=null,activeRun=false;
const remote="https://esm.sh/lean4.js@0.0.2?bundle";
export async function loadLean(onProgress=()=>{}){
 if(lean)return lean;
 if(loading)return loading;
 if(!crossOriginIsolated || typeof SharedArrayBuffer==="undefined")
   throw new Error("Lean WASM needs a cross-origin isolated workbench route (COOP/COEP).");
 loading=(async()=>{
  onProgress("Loading Lean WASM JavaScript SDK");
  const {Lean4}=await import(remote);
  const runtime=new Lean4({timeout:180000,onProgress});
  try{
   await runtime.init();
   lean=runtime;
   onProgress("Lean WASM assets ready");
   return lean;
  }catch(e){runtime.dispose();throw e}
 })();
 try{return await loading}
 finally{loading=null}
}
function diagnosticMessages(text){
 const messages=[];
 for(const line of String(text||"").split("\n")){
  if(!line.trim())continue;
  try{const entry=JSON.parse(line);if(entry?.severity || entry?.message)messages.push(entry)}
  catch{}
 }
 return messages;
}
export async function compileLean(source,{fixture="",onProgress=()=>{}}={}){
 if(activeRun)throw Error("A Lean compile is already running");
 const text=String(source)+"\n"+String(fixture||"");
 if(/\b(?:sorry|admit|native_decide)\b/.test(text) || /\baxiom\s+/.test(text))
  return {status:"rejected",verified:false,stdout:"",stderr:"Explicit axiom, sorry/admit or native_decide in source: the workbench does not certify these.",exitCode:null};
 activeRun=true;
 try{
  const compiler=await loadLean(onProgress);
  onProgress("Elaborating and checking with the Lean 4 WASM compiler");
  const result=await compiler.run(text,{flags:["--json"]});
  const messages=diagnosticMessages(result.stdout+"\n"+result.stderr);
  const errors=messages.filter(m=>m.severity==="error");
  const stderrError=/(^|\n)(?:error:|.*\berror\b)/im.test(result.stderr);
  const verified=result.exitCode===0 && !errors.length && !stderrError;
  return {
   status:verified?"accepted":"error",
   verified,exitCode:result.exitCode,
   stdout:result.stdout,stderr:result.stderr,
   diagnostics:messages
  };
 }finally{activeRun=false}
}
export function leanAvailable(){return !!lean}