import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {compileNativeSource} from '../tools/headless/source-compiler.mjs';
import {createNodeDispatcher} from '../tools/headless/dispatcher.mjs';
import {sourceTool,SOURCE_TOOL,sourceRequest,compilationReceipt} from '../profile/lean-source.js';
import {workbenchProfile} from '../profile/catalogue.js';
import {decode} from '../profile/core.js';

export const GOOD='module\npublic import Init\n@[expose] public section\ndef next (n : Nat) := n + 1\ntheorem next_zero : next 0 = 1 := by rfl\n#eval next 41\n';
function trust(t){const old=process.env.LINKED_TRUST_LEAN_SOURCE;process.env.LINKED_TRUST_LEAN_SOURCE='1';t.after(()=>{if(old===undefined)delete process.env.LINKED_TRUST_LEAN_SOURCE;else process.env.LINKED_TRUST_LEAN_SOURCE=old;});}

test('source is mandatory, typed and opt-in; no silent promotion to remote code execution',async()=>{
 assert.throws(()=>decode(sourceTool.inputSchema,{}),/required/);
 assert.throws(()=>decode(sourceTool.inputSchema,{source:123}),/string/);
 assert.throws(()=>decode(sourceTool.inputSchema,{source:GOOD,filename:'../../bad'}),/unknown/);
 const args=decode(sourceTool.inputSchema,{source:GOOD});
 assert.equal(args.environment,'core');assert.equal(args.includeArtifacts,false);
 assert(!workbenchProfile().tools.some(t=>t.name===SOURCE_TOOL));
 assert(workbenchProfile({enabledTools:[SOURCE_TOOL]}).tools.some(t=>t.name===SOURCE_TOOL));
 assert.throws(()=>sourceRequest({source:GOOD,budgetMs:Infinity}),/budget/);
});

test('native source is unavailable without host opt-in',async t=>{
 const previous=process.env.LINKED_TRUST_LEAN_SOURCE;delete process.env.LINKED_TRUST_LEAN_SOURCE;
 t.after(()=>{if(previous!==undefined)process.env.LINKED_TRUST_LEAN_SOURCE=previous;});
 const r=await compileNativeSource({source:GOOD});
 assert.equal(r.execution,'compiler_unavailable');assert.deepEqual(r.artifacts,[]);
});

test('native HTTP adapter never grants source-compilation capability',async t=>{
 trust(t);
 const dispatcher=await createNodeDispatcher('mcp-http',{enabledTools:[SOURCE_TOOL]});
 assert.equal(dispatcher.definitions()[0].available,false);
 assert.equal((await dispatcher.invoke(SOURCE_TOOL,{source:GOOD})).status,'unsupported');
});

test('real native compiler emits independently hashed Script.olean and evaluates 42',{timeout:120000},async t=>{
 trust(t);
 const dispatcher=await createNodeDispatcher('local-cli',{enabledTools:[SOURCE_TOOL]});
 const reply=await dispatcher.invoke(SOURCE_TOOL,{source:GOOD,includeArtifacts:true});
 assert.equal(reply.status,'completed');const r=reply.result;
 assert.equal(r.execution,'compiled',JSON.stringify(r));
 assert.equal(r.compilation.artifactProduced,true);assert.equal(r.proof.policyContractChecked,false);
 assert.equal(r.proof.axiomAuditPerformed,false);assert.equal(r.proof.placeholderDetected,false);
 assert.match(r.compiler.version,/4\.33\.1/);assert.match(r.stdout,/42/);
 assert.equal(r.sourceSha256,createHash('sha256').update(GOOD).digest('hex'));
 const module=r.artifacts.find(f=>f.name==='Script.olean'),bytes=Buffer.from(module.base64,'base64');
 assert.equal(bytes.length,module.bytes);assert.equal(bytes.subarray(0,4).toString(),'olea');
 assert.equal(createHash('sha256').update(bytes).digest('hex'),module.sha256);
});

test('real compiler rejects false theorem without returning an artifact',{timeout:120000},async t=>{
 trust(t);const r=await compileNativeSource({source:'import Init\nexample : (1 : Nat) = 2 := by rfl\n'});
 assert.equal(r.execution,'compile_rejected',JSON.stringify(r));assert.equal(r.compilation.accepted,false);
 assert.deepEqual(r.artifacts,[]);assert(r.diagnostics.some(d=>d.severity==='error'));
});

test('a sorry compilation is not reported as a completed proof',{timeout:120000},async t=>{
 trust(t);const r=await compileNativeSource({source:'import Init\nexample : False := by sorry\n'});
 assert.equal(r.execution,'compiled_with_placeholders',JSON.stringify(r));
 assert.equal(r.proof.placeholderDetected,true);assert.equal(r.proof.policyContractChecked,false);
});

test('supplied policy-related Lean can import the actual Workbench module',{timeout:120000},async t=>{
 trust(t);const source='module\npublic import Workbench\nopen LinkedAssurance\nexample (e : Evidence) (s : OperationalState) (h : ready e s = true) : permitRequirements e s := ready_sound e s h\n';
 const r=await compileNativeSource({source,environment:'workbench'});
 assert.equal(r.execution,'compiled',JSON.stringify(r));assert.equal(r.environment,'workbench');
});

test('cancellation and timeout produce no semantic rejection or stale artifacts',{timeout:120000},async t=>{
 trust(t);const signal=AbortSignal.abort();
 const cancelled=await compileNativeSource({source:GOOD},{signal});assert.equal(cancelled.execution,'cancelled');
 const timed=await compileNativeSource({source:GOOD,budgetMs:1});assert.equal(timed.execution,'timeout',JSON.stringify(timed));
 for(const r of [cancelled,timed]){assert.equal(r.compilation.accepted,false);assert.deepEqual(r.artifacts,[]);}
});

test('exit zero without an exported module is not compiled success',async()=>{
 const r=await compilationReceipt(sourceRequest({source:GOOD}),{exitCode:0,stdout:'',stderr:''},[],{});
 assert.equal(r.execution,'compiler_fault');assert.equal(r.compilation.artifactProduced,false);
});
