#!/usr/bin/env node
// Native Node path: actual Factoidal WASM, actual ECDSA verification,
// actual Lean 4.33.1 compiler/kernel, Policy.lean, Workbench.lean.
// Browser counterpart is tools/viewer-browser/lean-policy.mjs.
import fs from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import {pathToFileURL} from 'node:url';
import {runNodeCase,parseArgs} from './node-runner.mjs';
import {makeCase} from '../../headless-contract.js';
import {fixtureSource,sha256} from '../../evidence.js';
import {verifyCredential} from '../../credential.js';

function callLean(directory,filename,source,output){
  const file=path.join(directory,filename);
  return fs.writeFile(file,source).then(()=>{
    const args=['--json'];
    if(output)args.push('-o',path.join(directory,output));
    args.push(file);
    const result=spawnSync('lean',args,{
      cwd:directory,env:{...process.env,LEAN_PATH:directory},
      encoding:'utf8',timeout:180000,maxBuffer:8*1024*1024
    });
    if(result.error)throw result.error;
    if(result.status!==0)throw Error('Lean '+filename+' failed ('+result.status+'): '+
      (result.stdout||'')+'\n'+(result.stderr||''));
    const text=(result.stdout||'')+'\n'+(result.stderr||'');
    if(text.includes('declaration uses')&&text.includes('sorry'))throw Error('Lean used a sorry placeholder');
    return text;
  });
}
function getDecision(text){
  const match=text.match(/LinkedAssurance\.Decision\.(permit|deny|defer|escalate|protectiveShutdown)\s*,\s*LinkedAssurance\.AttackOutcome\.(achieved|notAchieved|unknown)/);
  return match?{decision:match[1],attacker:match[2],executed:true}:
    {decision:null,attacker:null,executed:false};
}
export async function runNativePolicyCase(input={}){
  const {identity,request}=makeCase(input);
  const rdf=await runNodeCase(input);
  const credential=JSON.parse(await fs.readFile(new URL('../../demo-credential.json',import.meta.url),'utf8'));
  const signed=await verifyCredential(credential.publicKey,credential.payload,credential.signature);
  const clock=input.clock||'2026-11-11T12:00:00Z';
  const observedTime=Date.parse(clock);
  if(!Number.isSafeInteger(observedTime)||observedTime<0)throw Error('Invalid observed time');
  const op={
    credentialVerified:signed.verified,observedTime,expiresAt:signed.expiresAt,
    secureTransportObserved:input.secureTransportObserved!==false,
    permissionGranted:input.permissionGranted!==false,
    attackerWantsInterruption:input.attackerWantsInterruption??(identity.scenario==='alert'),
    legitimateSession:identity.scenario==='alert'
  };
  const observation=rdf.observation;
  const fallback={
    datasetBytesSha256:await sha256(request.dataset),
    selectedGraphSha256:'unavailable',
    scope:JSON.stringify(request.scope),regime:request.regime,runtimeVersion:'0.35.1'
  };
  const fixture=fixtureSource({
    execution:observation.execution,
    context:observation.context,claims:observation.claims
  },op,fallback,request.queries);
  const dir=await fs.mkdtemp(path.join(os.tmpdir(),'linked-assurance-node-'));
  try{
    const version=spawnSync('lean',['--version'],{encoding:'utf8',timeout:10000});
    if(version.status!==0||!/\b4\.33\.1\b/.test(version.stdout))
      throw Error('Native Lean 4.33.1 required; observed '+version.stdout+' '+version.stderr);
    const source=await fs.readFile(new URL('../../lean/Policy.lean',import.meta.url),'utf8');
    const support=await fs.readFile(new URL('../../lean/Workbench.lean',import.meta.url),'utf8');
    await callLean(dir,'Workbench.lean',support,'Workbench.olean');
    await callLean(dir,'Policy.lean',source,'Policy.olean');
    const output=await callLean(dir,'Run.lean',fixture,null);
    const outcome=getDecision(output);
    if(!outcome.executed)throw Error('Lean accepted fixture but no policy decision was found: '+output.slice(-1200));
    return {
      case:identity,rdfObservation:observation,
      policy:outcome,fixtureSha256:await sha256(fixture),
      sourceSha256:await sha256(source),operational:op,
      attestation:{
        runtime:'node-native-lean',
        node:process.versions.node,executable:process.execPath,
        nativeLean:version.stdout.trim(),
        rdfWorker:rdf.attestation
      }
    };
  }finally{await fs.rm(dir,{recursive:true,force:true});}
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
  try{
    const input=parseArgs(process.argv.slice(2));
    process.stdout.write(JSON.stringify(await runNativePolicyCase(input))+'\n');
  }catch(e){process.stderr.write(String(e.stack||e)+'\n');process.exitCode=1;}
}
