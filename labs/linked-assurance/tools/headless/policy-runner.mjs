#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
// Fixed repository policy only. Native Lean is not a sandbox for untrusted code.
import fs from 'node:fs/promises';
import {spawn} from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import {pathToFileURL} from 'node:url';
import {runNodeCase,parseArgs} from './node-runner.mjs';
import {preparePolicyInput} from '../../profile/policy-input.js';
import {policyAudit,auditContract,accepted,diagnosticText} from '../../lean-host.js';
import {sha256} from '../../evidence.js';
async function processLean(args,cwd,signal){
 return await new Promise((resolve,reject)=>{
  if(signal?.aborted){reject(Error('cancelled'));return;}
  const child=spawn('lean',args,{cwd,env:{...process.env,LEAN_PATH:cwd},stdio:['ignore','pipe','pipe']});
  let stdout='',stderr='',size=0,settled=false;
  const finish=(error,result)=>{if(settled)return;settled=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);error?reject(error):resolve(result);};
  const stop=why=>{child.kill('SIGKILL');finish(Error(why));};
  const abort=()=>stop('cancelled');
  const timer=setTimeout(()=>stop('compiler_timeout'),180000);signal?.addEventListener('abort',abort,{once:true});
  for(const [stream,key] of [[child.stdout,'stdout'],[child.stderr,'stderr']])stream.on('data',chunk=>{
   size+=chunk.length;if(size>8*1024*1024){stop('compiler_output_limit');return;}
   if(key==='stdout')stdout+=chunk;else stderr+=chunk;
  });
  child.on('error',error=>finish(Error('compiler_unavailable: '+error.message)));
  child.on('close',code=>finish(null,{exitCode:code,stdout,stderr}));
 });
}
async function compileFixed(dir,signal){
 const version=await processLean(['--version'],dir,signal);
 if(version.exitCode!==0||!/\b4\.33\.1\b/.test(version.stdout))throw Error('compiler_unavailable: Native Lean 4.33.1 required');
 const support=await fs.readFile(new URL('../../lean/Workbench.lean',import.meta.url),'utf8');
 const source=await fs.readFile(new URL('../../lean/Policy.lean',import.meta.url),'utf8');
 await fs.writeFile(path.join(dir,'Workbench.lean'),support);
 const supportResult=await processLean(['--json','-o','Workbench.olean','Workbench.lean'],dir,signal);
 if(!accepted(supportResult))return {contractChecked:false,diagnostic:diagnosticText(supportResult),source};
 await fs.writeFile(path.join(dir,'Policy.lean'),source+policyAudit);
 const checked=await processLean(['--json','-o','Policy.olean','Policy.lean'],dir,signal);
 const contractChecked=['policy_contract','policy_pipeline_contract','adaptEvidence_contract'].every(n=>auditContract(checked,'LinkedAssurance.'+n));
 return {contractChecked,source,sourceSha256:await sha256(source),supportSha256:await sha256(support),compilerVersion:version.stdout.trim(),diagnostic:contractChecked?'':diagnosticText(checked)};
}
export async function checkNativePolicy(options={}){
 const dir=await fs.mkdtemp(path.join(os.tmpdir(),'dickory-check-'));
 try{const c=await compileFixed(dir,options.signal);return {execution:c.contractChecked?'completed':'proof_rejected',contractChecked:c.contractChecked,sourceSha256:c.sourceSha256,compilerVersion:c.compilerVersion,diagnostic:c.diagnostic};}
 finally{await fs.rm(dir,{recursive:true,force:true});}
}
export async function runNativePolicyCase(input={},options={}){
 const rdf=await runNodeCase(input,options);
 const dir=await fs.mkdtemp(path.join(os.tmpdir(),'dickory-policy-'));
 try{
  const c=await compileFixed(dir,options.signal);
  if(!c.contractChecked)return {execution:'proof_rejected',contractChecked:false,policy:{executed:false},diagnostic:c.diagnostic};
  const demo=JSON.parse(await fs.readFile(new URL('../../demo-credential.json',import.meta.url),'utf8'));
  const p=await preparePolicyInput(input,rdf.observation,demo,c.source);
  await fs.writeFile(path.join(dir,'Run.lean'),p.fixture);
  const result=await processLean(['--json','Run.lean'],dir,options.signal),text=diagnosticText(result);
  const match=text.match(/LinkedAssurance\.Decision\.(permit|deny|defer|escalate|protectiveShutdown)\s*,\s*LinkedAssurance\.AttackOutcome\.(achieved|notAchieved|unknown)/);
  const executed=accepted(result)&&!!match;
  return {execution:executed?'completed':'compiler_fault',case:p.case,resolved:p.resolved,rdfObservation:rdf.observation,
   policy:{executed,decision:executed?match[1]:null,attacker:executed?match[2]:null},
   fixtureSha256:p.fixtureSha256,sourceSha256:p.sourceSha256,operational:p.operational,contractChecked:true,
   attestation:{runtime:'node-native-lean',node:process.versions.node,nativeLean:c.compilerVersion,rdfWorker:rdf.attestation}};
 }finally{await fs.rm(dir,{recursive:true,force:true});}
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 try{process.stdout.write(JSON.stringify(await runNativePolicyCase(parseArgs(process.argv.slice(2))))+'\n');}
 catch(e){process.stderr.write(String(e)+'\n');process.exitCode=1;}
}
