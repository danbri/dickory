import test from 'node:test';
import assert from 'node:assert/strict';
import {defineProfile,decode,createDispatcher} from '../profile/core.js';
import {workbenchProfile,policyInput} from '../profile/catalogue.js';
import {registerWebMCP,invokeNativeWebMCP} from '../profile/webmcp.js';
const tool={name:'site.echo',description:'Site-owned tool',requires:[],inputSchema:{type:'object',properties:{
 text:{type:'string'},count:{type:'integer',minimum:0,maximum:10,default:2},flag:{type:'boolean'},nil:{type:'null'}},required:['text'],additionalProperties:false}};
const setup=(extra={})=>createDispatcher({profile:defineProfile({id:'example',tools:[tool],...extra}),transport:'webmcp',handlers:{'site.echo':args=>args},runtime:{host:'unit-test'}});
test('same field defaults and ordering on repeated decoding',()=>{
 const input={text:'hello'},expected={count:2,text:'hello'};
 assert.deepEqual(decode(tool.inputSchema,input),expected);
 assert.deepEqual(decode(tool.inputSchema,expected),expected);
 assert.deepEqual(input,{text:'hello'});
});
test('required, optional, explicit null, unknown and typed fields',()=>{
 for(const input of [{},{text:null},{text:'x',count:'2'},{text:'x',count:11},{text:'x',flag:null},{text:'x',other:true},[],null])assert.throws(()=>decode(tool.inputSchema,input));
 assert.deepEqual(decode(tool.inputSchema,{text:'x',nil:null}),{count:2,nil:null,text:'x'});
});
test('only explicitly implemented schema keywords are accepted',()=>{
 assert.throws(()=>defineProfile({id:'x',tools:[{...tool,inputSchema:{...tool.inputSchema,oneOf:[]}}]}),/unsupported/);
 assert.throws(()=>defineProfile({id:'x',tools:[{...tool,inputSchema:{...tool.inputSchema,required:['text','nope']}}]}));
 assert.throws(()=>defineProfile({id:'x',tools:[{...tool,inputSchema:{...tool.inputSchema,properties:{text:{type:'string',default:'x'}}}}]}),/required fields/);
});
test('site chooses tools, transports and capabilities; disabled calls never invoke handler',async()=>{
 let calls=0;
 for(const config of [{enabledTools:[]},{transports:['mcp-stdio']}]){
  const d=createDispatcher({profile:defineProfile({id:'x',tools:[tool],...config}),transport:'webmcp',handlers:{'site.echo':()=>{calls++;return {};}}});
  assert.equal((await d.invoke('site.echo',{text:'x'})).status,'unsupported');
 }
 const d=createDispatcher({profile:defineProfile({id:'x',tools:[{...tool,requires:['private']}] }),transport:'webmcp',capabilities:[],handlers:{'site.echo':()=>{calls++;return {};}}});
 assert.equal((await d.invoke('site.echo',{text:'x'})).status,'unsupported');assert.equal(calls,0);
});
test('the profile snapshots site configuration',()=>{
 const tools=[structuredClone(tool)],p=defineProfile({id:'x',tools});tools[0].name='changed';
 assert.equal(p.tools[0].name,'site.echo');assert(Object.isFrozen(p.tools[0].inputSchema));
});
test('four transports use identical resolved arguments',async()=>{
 const profile=defineProfile({id:'x',tools:[tool],transports:['local-cli','mcp-stdio','mcp-http','webmcp']});
 const outputs=[];
 for(const transport of profile.transports)outputs.push((await createDispatcher({profile,transport,handlers:{'site.echo':a=>a}}).invoke('site.echo',{text:'x'})).result);
 for(const o of outputs)assert.deepEqual(o,outputs[0]);
});
test('late result cannot override cancellation',async()=>{
 const c=new AbortController();let release;
 const d=createDispatcher({profile:defineProfile({id:'x',tools:[tool]}),transport:'webmcp',handlers:{'site.echo':()=>new Promise(r=>release=r)}});
 const pending=d.invoke('site.echo',{text:'x'},{signal:c.signal});c.abort();release({decision:'permit'});
 const r=await pending;assert.equal(r.status,'cancelled');assert.equal(r.result,undefined);
});
test('application deny and attacker-success remain data, not transport failure',async()=>{
 const d=createDispatcher({profile:defineProfile({id:'x',tools:[tool]}),transport:'webmcp',handlers:{'site.echo':()=>({decision:'protectiveShutdown',attacker:'achieved'})}});
 const r=await d.invoke('site.echo',{text:'x'});assert.equal(r.status,'completed');assert.equal(r.result.attacker,'achieved');
});
test('site computation budget is enforced before handler entry',async()=>{
 let calls=0;const d=createDispatcher({profile:workbenchProfile({maxBudgetMs:10}),transport:'webmcp',capabilities:['rdf'],handlers:{linked_assurance_evaluate:()=>{calls++;return {};}}});
 assert.equal((await d.invoke('linked_assurance_evaluate',{budgetMs:11})).status,'invalid_request');assert.equal(calls,0);
});
test('operational inputs never depend on scenario/UI state',()=>{
 const a=decode(policyInput,{scenario:'alert'}),b=decode(policyInput,{scenario:'vocabulary'});
 assert.deepEqual(a.state,b.state);assert.equal(a.state.attackerWantsInterruption,false);assert.equal(a.state.legitimateSession,false);
});
test('WebMCP adapter passes schemas, cancellation and explicit origins (adapter unit test, NOT native evidence)',async()=>{
 const d=setup();let registered,options;
 const r=await registerWebMCP(d,{context:{registerTool:async(t,o)=>{registered=t;options=o;}}});
 assert.equal(r.registered,true);assert.equal(registered.name,tool.name);assert.equal(registered.annotations.readOnlyHint,false);assert.equal(registered.annotations.consequentialHint,true);assert.equal(options.exposedTo,undefined);
 assert.deepEqual((await registered.execute({text:'x'},{})).result,{count:2,text:'x'});r.dispose();assert.equal(options.signal.aborted,true);
 assert.equal((await registerWebMCP(d,{context:null})).registered,false);
 await assert.rejects(()=>invokeNativeWebMCP('site.echo',{}, {context:null}),/unavailable/);
});
test('invalid input does not call a handler',async()=>{
 let n=0;const d=createDispatcher({profile:defineProfile({id:'x',tools:[tool]}),transport:'webmcp',handlers:{'site.echo':()=>{n++;return {};}}});
 assert.equal((await d.invoke('site.echo',{text:17})).status,'invalid_request');assert.equal(n,0);
});
