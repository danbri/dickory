// WebMCP tools: document.modelContext is the current Chrome API.
// Not navigator.modelContext. When the API is unavailable, the same
// real tool handlers remain callable by a local headless test harness;
// we do not claim that fallback constitutes native WebMCP registration.
import {listCases,makeCase,normalizeRdf} from './headless-contract.js';
import {startRdf} from './evidence.js';

const emptySchema={type:'object',properties:{},additionalProperties:false};
const caseSchema={type:'object',properties:{
  scenario:{type:'string',description:'Sample case identifier'},
  variant:{type:'string',description:'Case data variant',default:'base'},
  scope:{type:'string',enum:['default','data','ontology','union'],default:'union'},
  regime:{type:'string',enum:['simple','RDFS'],default:'RDFS'},
  budgetMs:{type:'integer',minimum:1,maximum:120000,default:60000}
},additionalProperties:false};

export async function evaluateCase(input={},options={}) {
  const {identity,request}=makeCase(input);
  options.signal?.throwIfAborted?.();
  const job=startRdf(request,identity.budgetMs);
  const cancel=()=>job.cancel();
  options.signal?.addEventListener('abort',cancel,{once:true});
  try{
    const result=await job.promise;
    options.signal?.throwIfAborted?.();
    return {
      case:identity,observation:normalizeRdf(result),
      attestation:{
        runtime:'chromium-page-worker',
        userAgent:navigator.userAgent,
        documentType:typeof document,windowType:typeof window,
        workerAPI:typeof Worker,webAssembly:typeof WebAssembly,
        crossOriginIsolated:globalThis.crossOriginIsolated===true
      }
    };
  }finally{options.signal?.removeEventListener('abort',cancel);}
}
export function toolDefinitions(){
  return [
    {name:'linked_assurance_cases',
      description:'List the pinned Linked Assurance RDF scenarios and admissible graph scopes.',
      inputSchema:emptySchema,annotations:{readOnlyHint:true},
      execute:()=>({cases:listCases()})},
    {name:'linked_assurance_evaluate',
      description:'Evaluate a pinned Linked Assurance RDF case using the real Factoidal WASM engine in a killable browser worker. Returns observations, not a proof of policy correctness.',
      inputSchema:caseSchema,annotations:{readOnlyHint:true},
      execute:async(input={},options={})=>{
        try{return await evaluateCase(input,options)}
        catch(e){if(options.signal?.aborted)throw e;return {error:String(e?.message||e)}}
      }}
  ];
}
export async function mountWebMCP(){
  const api=document.modelContext;
  if(!api||typeof api.registerTool!=='function')
    return {registered:false,reason:'document.modelContext not enabled in this browser'};
  for(const tool of toolDefinitions())await api.registerTool(tool);
  return {registered:true,names:toolDefinitions().map(t=>t.name)};
}
// Harness access only via explicit ?headless=1; not an MCP substitute.
// In normal browsing tool dispatch is exclusively browser-managed WebMCP.
if(new URL(location.href).searchParams.has('headless')){
  window.__linkedAssuranceHeadless={
    list:()=>listCases(),run:evaluateCase,
    names:toolDefinitions().map(t=>t.name)
  };
}
