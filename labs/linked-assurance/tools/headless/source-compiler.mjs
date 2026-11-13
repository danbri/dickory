// SPDX-License-Identifier: Apache-2.0
// Trusted local developer code ONLY. Native Lean can execute IO at compile time.
// A temporary directory, deadline and process-group cleanup are NOT a sandbox.
import fs from 'node:fs/promises';
import {spawn} from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import {sourceRequest,compilationReceipt,compilationFault,describeArtifacts} from '../../profile/lean-source.js';

async function invokeLean(args,cwd,deadline,signal){
  if(signal?.aborted)throw Error('cancelled');
  const remaining=Math.ceil(deadline-performance.now());
  if(remaining<=0)throw Error('compiler_timeout');
  return await new Promise((resolve,reject)=>{
    const grouped=process.platform!=='win32';
    const child=spawn('lean',args,{cwd,env:{...process.env,LEAN_PATH:cwd},detached:grouped,stdio:['ignore','pipe','pipe']});
    let stdout='',stderr='',size=0,failure=null,settled=false;
    const kill=()=>{try{if(grouped&&child.pid)process.kill(-child.pid,'SIGKILL');else child.kill('SIGKILL');}catch{}};
    const stop=why=>{failure??=Error(why);kill();};
    const abort=()=>stop('cancelled');
    const timer=setTimeout(()=>stop('compiler_timeout'),remaining);
    const done=(error,value)=>{if(settled)return;settled=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);kill();error?reject(error):resolve(value);};
    signal?.addEventListener('abort',abort,{once:true});if(signal?.aborted)abort();
    for(const [stream,name] of [[child.stdout,'stdout'],[child.stderr,'stderr']])stream.on('data',chunk=>{
      size+=chunk.length;if(size>1048576){stop('compiler_output_limit');return;}
      if(name==='stdout')stdout+=chunk;else stderr+=chunk;
    });
    child.on('error',e=>done(Error('compiler_unavailable: '+e.message)));
    child.on('close',(code,signalName)=>done(failure||(!Number.isInteger(code)?Error('compiler_fault: '+signalName):null),{exitCode:code,stdout,stderr}));
  });
}

export async function compileNativeSource(input,options={}){
  const request=sourceRequest(input),compiler={host:'node-native',requiredVersion:'4.33.1'};
  // This cannot be enabled through a tool argument. HTTP never provides this capability.
  if(process.env.LINKED_TRUST_LEAN_SOURCE!=='1')return compilationFault(request,'compiler_unavailable','Trusted native source compilation requires host-owned LINKED_TRUST_LEAN_SOURCE=1.',compiler);
  const deadline=performance.now()+request.budgetMs;
  let dir;
  try{
    dir=await fs.mkdtemp(path.join(os.tmpdir(),'dickory-source-'));
    const version=await invokeLean(['--version'],dir,deadline,options.signal);
    compiler.version=version.stdout.trim();
    if(version.exitCode!==0||!/\b4\.33\.1\b/.test(compiler.version))throw Error('compiler_unavailable: native Lean 4.33.1 required');
    if(request.environment==='workbench'){
      const support=await fs.readFile(new URL('../../lean/Workbench.lean',import.meta.url),'utf8');
      await fs.writeFile(path.join(dir,'Workbench.lean'),support);
      const compiled=await invokeLean(['--json','-o','Workbench.olean','Workbench.lean'],dir,deadline,options.signal);
      if(compiled.exitCode!==0)throw Error('compiler_unavailable: Workbench failed to compile: '+compiled.stdout+compiled.stderr);
    }
    // Fixed module/path: callers cannot write arbitrary paths through tool parameters.
    await fs.writeFile(path.join(dir,'Script.lean'),request.source);
    const result=await invokeLean(['--json','-o','Script.olean','Script.lean'],dir,deadline,options.signal);
    const entries=[];
    if(result.exitCode===0)for(const name of await fs.readdir(dir)){
      if(!/^Script\.(olean(\.(server|private))?|ir(\.sig)?|ilean)$/.test(name))continue;
      const filename=path.join(dir,name),stat=await fs.lstat(filename);
      if(!stat.isFile()||stat.size>8388608)throw Error('compiler_artifact_limit');
      entries.push([name,new Uint8Array(await fs.readFile(filename))]);
    }
    if(options.signal?.aborted)throw Error('cancelled');
    return await compilationReceipt(request,result,await describeArtifacts(entries,request.includeArtifacts),compiler);
  }catch(e){
    const message=String(e.message||e);
    const execution=options.signal?.aborted?'cancelled':message.includes('compiler_timeout')?'timeout':message.includes('_limit')?'resource_limit':message.includes('compiler_unavailable')?'compiler_unavailable':'compiler_fault';
    return await compilationFault(request,execution,message,compiler);
  }finally{if(dir)await fs.rm(dir,{recursive:true,force:true});}
}
