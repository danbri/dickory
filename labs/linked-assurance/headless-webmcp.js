// SPDX-License-Identifier: Apache-2.0
import {listCases,makeCase,normalizeRdf} from './headless-contract.js';
import {startRdf} from './evidence.js';
import {createDispatcher} from './profile/core.js';
import {workbenchProfile} from './profile/catalogue.js';
import {preparePolicyInput} from './profile/policy-input.js';
import {registerWebMCP,invokeNativeWebMCP} from './profile/webmcp.js';
async function read(path,json=false){const r=await fetch(new URL(path,import.meta.url));if(!r.ok)throw Error('Missing '+path);return json?r.json():r.text();}
export async function evaluateCase(input={},options={}){
 const {identity,request}=makeCase(input);
 options.signal?.throwIfAborted();
 const job=startRdf(request,identity.budgetMs),cancel=()=>job.cancel();
 options.signal?.addEventListener('abort',cancel,{once:true});
 try{return {case:identity,observation:normalizeRdf(await job.promise),attestation:{runtime:'chromium-page-worker',userAgent:navigator.userAgent,documentType:typeof document,windowType:typeof window,workerAPI:typeof Worker,crossOriginIsolated:globalThis.crossOriginIsolated===true}};}
 finally{options.signal?.removeEventListener('abort',cancel);}
}
export async function createBrowserDispatcher(config){
 const profile=workbenchProfile(config??await read('./developer-profile.json',true));
 const check=async()=>{const host=await import('./lean-host.js'),source=await read('./lean/Policy.lean');const result=await host.compilePolicy(source);return {execution:result.contractChecked?'completed':'proof_rejected',contractChecked:result.contractChecked,sourceSha256:result.sourceSha256,compilerVersion:result.compilerVersion,verificationLocation:result.verificationLocation};};
 const policy=async(input,options)=>{
  const rdf=await evaluateCase(input,options),host=await import('./lean-host.js');
  options.signal?.throwIfAborted();
  const [source,demo]=await Promise.all([read('./lean/Policy.lean'),read('./demo-credential.json',true)]);
  const c=await host.compilePolicy(source);options.signal?.throwIfAborted();
  if(!c.contractChecked)return {execution:'proof_rejected',contractChecked:false,policy:{executed:false}};
  const p=await preparePolicyInput(input,rdf.observation,demo,source);
  const result=await host.executePolicy(source,p.fixture);options.signal?.throwIfAborted();
  return {execution:result.executed?'completed':'compiler_fault',case:p.case,resolved:p.resolved,rdfObservation:rdf.observation,
   policy:{executed:result.executed,decision:result.decision??null,attacker:result.attacker??null},
   fixtureSha256:p.fixtureSha256,sourceSha256:p.sourceSha256,operational:p.operational,contractChecked:true,
   attestation:{runtime:'browser-wasm-lean',compilerVersion:result.compilerVersion,rdfWorker:rdf.attestation}};
 };
 return createDispatcher({profile,transport:'webmcp',capabilities:['rdf','lean-policy'],runtime:{host:'browser',userAgent:navigator.userAgent},handlers:{
  linked_assurance_cases:()=>({cases:listCases()}),linked_assurance_evaluate:evaluateCase,
  linked_assurance_check_policy:check,linked_assurance_policy:policy
 }});
}
let ready;
export function mountWebMCP(){
 if(!ready)ready=(async()=>{const dispatcher=await createBrowserDispatcher();const registration=await registerWebMCP(dispatcher);return {dispatcher,registration};})();
 return ready;
}
if(new URL(location.href).searchParams.has('headless')){
 window.__linkedAssuranceHeadless={ready:mountWebMCP(),
  invokeNative:async(name,args)=>{await mountWebMCP();return invokeNativeWebMCP(name,args);},
  invokeDirect:async(name,args)=>{const {dispatcher}=await mountWebMCP();return dispatcher.invoke(name,args);}};
}
