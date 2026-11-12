#!/usr/bin/env node
// Node CLI: Factoidal runs in a real Node.js worker thread.
import {Worker} from 'node:worker_threads';
import {pathToFileURL} from 'node:url';
import {makeCase,normalizeRdf,listCases} from '../../headless-contract.js';

export async function runNodeCase(input={}) {
  const {identity,request}=makeCase(input);
  const worker=new Worker(new URL('./node-worker.mjs',import.meta.url));
  return await new Promise(resolve=>{
    let settled=false;
    const finish=(value)=>{
      if(settled)return;
      settled=true;clearTimeout(timer);void worker.terminate();
      resolve({case:identity,...value});
    };
    const timer=setTimeout(()=>finish({
      observation:normalizeRdf({execution:'timeout'}),
      attestation:{runtime:'node',node:process.versions.node,executable:process.execPath},
      diagnostic:'Worker terminated at the requested wall-clock deadline'
    }),identity.budgetMs);
    worker.on('message',m=>{if(m.kind==='result')finish({
      observation:m.observation,attestation:m.attestation,diagnostic:m.diagnostic
    })});
    worker.on('error',e=>finish({
      observation:normalizeRdf({execution:'engineFault'}),
      attestation:{runtime:'node',node:process.versions.node,executable:process.execPath},
      diagnostic:String(e)
    }));
    worker.on('exit',code=>{if(!settled)finish({
      observation:normalizeRdf({execution:'engineFault'}),
      attestation:{runtime:'node',node:process.versions.node,executable:process.execPath},
      diagnostic:'Worker exited without an outcome: '+code
    })});
    worker.postMessage({request});
  });
}
export function parseArgs(argv){
  const input={};
  for(let i=0;i<argv.length;i++){
    if(argv[i]==='--list')return {list:true};
    if(!argv[i].startsWith('--')||i+1>=argv.length)throw Error('Expected --key value');
    const key=argv[i].slice(2),value=argv[++i];
    if(!['scenario','variant','scope','regime','budgetMs'].includes(key))throw Error('Unknown argument '+key);
    input[key]=key==='budgetMs'?Number(value):value;
  }
  return input;
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
  try{
    const opts=parseArgs(process.argv.slice(2));
    process.stdout.write(JSON.stringify(opts.list?{cases:listCases()}:await runNodeCase(opts))+'\n');
  }catch(e){process.stderr.write(String(e.stack||e)+'\n');process.exitCode=1;}
}
