import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {Worker} from 'node:worker_threads';
import * as api from '@factoidal/core';
import {evaluateRdf,scopeFrom,startRdf,queriesFrom,fixtureSource,leanString} from '../evidence.js';
import {verifyCredential} from '../credential.js';
import {auditContract} from '../lean-host.js';
import {scenarios,variants} from '../scenarios.js';
const run=(s,scope='union',regime='RDFS')=>evaluateRdf(api,{...s,scope:scopeFrom(scope),regime});
const answer=(r,key='classification')=>r.claims.find(c=>c.key===key)?.answer;
for(const s of scenarios)test(`${s.id}: real Factoidal query and graph evidence`,async()=>{
 const r=await run(s);assert.equal(r.execution,'completed');assert.equal(answer(r),true);
 assert.equal(r.context.runtimeVersion,'0.35.1');assert.equal(r.dataset.defaultQuads,0);
 assert.equal(r.explanation.entailed,true);assert(r.explanation.bundle.steps.length>0);
 assert.equal(answer(await run({...s,dataset:variants(s).find(v=>v.id==='unclassified').dataset})),false);
});
test('select before inference; new vocabulary stays runtime data',async()=>{
 const s=scenarios[0];for(const scope of ['data','default','ontology'])assert.equal(answer(await run(s,scope)),false);
 assert.equal(answer(await run(s,'union','simple')),false);
 assert.equal(answer(await run({...s,dataset:s.dataset.replaceAll('InterplanetaryCheesemaker','NewClassNeverCompiledIntoLean')})),true);
});
test('shared blanks in one TriG document retain identity',async()=>{
 const s={dataset:'<urn:lab:data> { _:x <urn:p> <urn:o> . } <urn:lab:ontology> { _:x <urn:q> <urn:r> . }',description:'',queries:[{key:'shared',query:'ASK { ?x <urn:p> <urn:o> ; <urn:q> <urn:r> }'}]};
 assert.equal(answer(await run(s),'shared'),true);
});
test('unsupported regimes and invalid input never become false observations',async()=>{
 assert.equal((await run(scenarios[0],'union','OWL-DL')).execution,'unsupported');
 await assert.rejects(run({...scenarios[0],dataset:'<unfinished'}));
 await assert.rejects(run({...scenarios[0],queries:[{key:'bad',query:'SELECT * WHERE {?s ?p ?o}'}]}),/ASK boolean/);
 assert.throws(()=>queriesFrom('[{"key":"x","query":"ASK{}"},{"key":"x","query":"ASK{}"}]'),/unique/);
});
test('consent withdrawal, overlapping classification and absent alert',async()=>{
 const event=scenarios[2],offer=scenarios[1],alert=scenarios[4];
 assert.equal(answer(await run({...event,dataset:variants(event).find(v=>v.id==='no-consent').dataset}),'applicationCondition'),false);
 const r=await run({...offer,dataset:variants(offer).find(v=>v.id==='both').dataset});
 assert.equal(answer(r,'organization'),true);assert.equal(answer(r,'disjointnessAssertion'),true);
 assert.equal(answer(await run({...alert,dataset:variants(alert).find(v=>v.id==='no-alert').dataset}),'alert'),false);
});
test('wall-clock timeout terminates a real worker in an infinite loop',async()=>{
 let terminated=false;
 const factory=()=>{const w=new Worker('while(true){}',{eval:true});return {postMessage(){},terminate(){terminated=true;return w.terminate();},set onmessage(_){},set onerror(_){}};};
 const started=performance.now(),r=await startRdf({},30,factory).promise;
 assert.equal(r.execution,'timeout');assert.deepEqual(r.claims,[]);assert(terminated);assert(performance.now()-started<2000);
});
test('cancellation wins over late worker replies',async()=>{
 let worker,terminated=0;const task=startRdf({},1000,()=>worker={postMessage(){},terminate(){terminated++;}});
 task.cancel();worker.onmessage({data:{kind:'result',result:{execution:'completed',claims:[{answer:true}]}}});
 assert.equal((await task.promise).execution,'cancelled');assert.equal(terminated,1);
});
test('ECDSA check rejects changed payload and an RDF verified string',async()=>{
 const c=JSON.parse(await fs.readFile(new URL('../demo-credential.json',import.meta.url)));
 assert.equal((await verifyCredential(c.publicKey,c.payload,c.signature)).verified,true);
 assert.equal((await verifyCredential(c.publicKey,c.payload.replace('2026-11-12','2030-11-12'),c.signature)).verified,false);
 assert.equal((await verifyCredential(c.publicKey,c.payload,'verified')).verified,false);
 assert.equal((await verifyCredential(c.publicKey,c.payload.replace('urn:lab:principal','urn:lab:someoneElse'),c.signature)).verified,false);
});
test('contract audit rejects additional axioms and compiler errors',()=>{
 const r=data=>({exitCode:0,stderr:'',stdout:JSON.stringify({severity:'information',data})});
 assert(auditContract(r("'LinkedAssurance.policy_contract' depends on axioms: [propext, Quot.sound]")));
 assert(!auditContract(r("'LinkedAssurance.policy_contract' depends on axioms: [sorryAx]")));
 assert(!auditContract(r("'LinkedAssurance.policy_contract' depends on axioms: [HiddenAssumption]")));
 assert(!auditContract({exitCode:1,stdout:'',stderr:'failed'}));
});
test('Lean transport escapes text instead of splicing executable source',()=>{
 assert.equal(leanString('"\nend LinkedAssurance'),'"\\"\\nend LinkedAssurance"');
 assert.throws(()=>fixtureSource({execution:'timeout'},{observedTime:NaN,expiresAt:0},{}),/timestamp/);
});
