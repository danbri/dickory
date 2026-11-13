#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
import {Worker} from 'node:worker_threads';
import {pathToFileURL} from 'node:url';
import {makeCase,normalizeRdf,listCases} from '../../headless-contract.js';
export async function runNodeCase(input={},options={}){
 const {identity,request}=makeCase(input);
 const host={runtime:'node',node:process.versions.node,executable:process.execPath,windowType:typeof globalThis.window,documentType:typeof globalThis.document};
 if(options.signal?.aborted)return {case:identity,observation:normalizeRdf({execution:'cancelled'}),attestation:host};
 const worker=new Worker(new URL('./node-worker.mjs',import.meta.url),{stdout:true,stderr:true});
 // Runtime diagnostics must never corrupt MCP stdio / CLI JSON stdout.
 worker.stdout.on('data',chunk=>process.stderr.write(chunk));worker.stderr.on('data',chunk=>process.stderr.write(chunk));
 return await new Promise(resolve=>{
  let settled=false;
  const finish=value=>{if(settled)return;settled=true;clearTimeout(timer);options.signal?.removeEventListener('abort',cancel);void worker.terminate();resolve({case:identity,...value});};
  const incomplete=execution=>finish({observation:normalizeRdf({execution}),attestation:host});
  const cancel=()=>incomplete('cancelled');
  const timer=setTimeout(()=>incomplete('timeout'),identity.budgetMs);
  options.signal?.addEventListener('abort',cancel,{once:true});
  worker.on('message',m=>{if(m.kind==='result')finish(m);});
  worker.on('error',()=>incomplete('engineFault'));
  worker.on('exit',()=>{if(!settled)incomplete('engineFault');});
  worker.postMessage({request});
 });
}
export function parseArgs(argv){
 const input={};
 for(let i=0;i<argv.length;i++){
  if(argv[i]==='--list')return {list:true};
  const key=argv[i].slice(2),value=argv[++i];
  if(!['scenario','variant','scope','regime','budgetMs'].includes(key)||value===undefined)throw Error('Expected --scenario/variant/scope/regime/budgetMs value');
  input[key]=key==='budgetMs'?Number(value):value;
 }
 return input;
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 try{const input=parseArgs(process.argv.slice(2));process.stdout.write(JSON.stringify(input.list?{cases:listCases()}:await runNodeCase(input))+'\n');}
 catch(e){process.stderr.write(String(e)+'\n');process.exitCode=1;}
}
