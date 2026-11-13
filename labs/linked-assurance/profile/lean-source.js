// SPDX-License-Identifier: Apache-2.0
// Compilation is not an application-policy proof or an OS sandbox.
import {sha256} from '../evidence.js';
export const SOURCE_TOOL = 'linked_assurance_compile_lean';
export const sourceTool = {
  name:SOURCE_TOOL,
  description:'Compile supplied Lean 4.33.1 source to an importable module. Compilation may execute metaprograms and #eval. Only enable for trusted developer input. Compiler acceptance is not policy certification.',
  requires:['lean-source'],budgetField:'budgetMs',
  annotations:{readOnlyHint:false,consequentialHint:true,untrustedContentHint:true,debugging:true},
  inputSchema:{type:'object',properties:{
    source:{type:'string',minLength:1,maxLength:65536},
    environment:{type:'string',enum:['core','workbench'],default:'core'},
    budgetMs:{type:'integer',minimum:1,maximum:120000,default:120000},
    includeArtifacts:{type:'boolean',default:false}
  },required:['source'],additionalProperties:false}
};
export function sourceRequest(input){
  if(!input||typeof input.source!=='string'||!input.source.length||new TextEncoder().encode(input.source).length>262144)throw TypeError('Expected non-empty Lean source, at most 256 KiB UTF-8.');
  const environment=input.environment??'core',budgetMs=input.budgetMs??120000;
  if(!['core','workbench'].includes(environment))throw TypeError('Unknown Lean source environment.');
  if(!Number.isInteger(budgetMs)||budgetMs<1||budgetMs>120000)throw TypeError('Compiler budget must be 1..120000 ms.');
  if(input.includeArtifacts!==undefined&&typeof input.includeArtifacts!=='boolean')throw TypeError('includeArtifacts must be Boolean.');
  return {source:input.source,environment,budgetMs,includeArtifacts:input.includeArtifacts===true};
}
export function compilerMessages(result){
  return [result.stdout||'',result.stderr||''].join('\n').split('\n').flatMap(line=>{
    try{const d=JSON.parse(line);return ['error','warning','information'].includes(d.severity)?[d]:[];}catch{return [];}
  });
}
export async function compilationReceipt(request,result,artifacts,compiler){
  const diagnostics=compilerMessages(result);
  const placeholder=diagnostics.some(d=>d.kind==='hasSorry'||/declaration uses.*sorry/.test(d.data||d.message||''));
  const accepted=result.exitCode===0&&!result.runtimeFault&&!diagnostics.some(d=>d.severity==='error');
  const artifactProduced=accepted&&artifacts.some(f=>f.name==='Script.olean');
  return {
    execution:!accepted?'compile_rejected':!artifactProduced?'compiler_fault':placeholder?'compiled_with_placeholders':'compiled',
    sourceSha256:await sha256(request.source),environment:request.environment,
    compilation:{accepted,artifactProduced,exitCode:result.exitCode??null},
    proof:{placeholderDetected:placeholder,policyContractChecked:false,axiomAuditPerformed:false,
      assurance:'Compiler acceptance and diagnostics only; no application theorem or independent environment recheck is asserted.'},
    compiler,artifacts:artifactProduced?artifacts:[],diagnostics,
    stdout:String(result.stdout||'').slice(0,1048576),stderr:String(result.stderr||'').slice(0,1048576),
    diagnosticsTruncated:String(result.stdout||'').length>1048576||String(result.stderr||'').length>1048576,
    compileTimeEffects:'Lean metaprograms, initializers and #eval may run while compiling. A separate runtime entry point was not invoked.'
  };
}
export async function compilationFault(request,execution,message,compiler={}){
  return {execution,sourceSha256:await sha256(request.source),environment:request.environment,
    compilation:{accepted:false,artifactProduced:false,exitCode:null},
    proof:{placeholderDetected:null,policyContractChecked:false,axiomAuditPerformed:false},
    compiler,artifacts:[],diagnostics:[],error:String(message)};
}
export async function describeArtifacts(entries,includeBytes=false){
  let total=0;const artifacts=[];
  for(const [name,bytes] of entries){
    if(!/^Script\.(olean(\.(server|private))?|ir(\.sig)?|ilean)$/.test(name))throw Error('Unexpected compilation artifact name.');
    total+=bytes.byteLength;if(total>8388608)throw Error('compiler_artifact_limit');
    const item={name,bytes:bytes.byteLength,sha256:await sha256(bytes)};
    if(includeBytes){let raw='';for(let i=0;i<bytes.length;i+=8192)raw+=String.fromCharCode(...bytes.subarray(i,i+8192));item.base64=btoa(raw);}
    artifacts.push(item);
  }
  return artifacts.sort((a,b)=>a.name.localeCompare(b.name));
}
