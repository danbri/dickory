import test from 'node:test';
import assert from 'node:assert/strict';
import {runNativePolicyCase,checkNativePolicy} from '../policy-runner.mjs';
test('native Lean checks the actual fixed contract',{timeout:120000},async()=>{
 const r=await checkNativePolicy();assert.equal(r.contractChecked,true,JSON.stringify(r));
});
for(const [name,input,decision,attacker] of [
 ['baseline',{scenario:'vocabulary',budgetMs:60000,state:{}},'permit','unknown'],
 ['bad signature',{scenario:'vocabulary',budgetMs:60000,state:{credentialSignature:'verified'}},'deny','unknown'],
 ['false alarm',{scenario:'alert',budgetMs:60000,state:{credentialSignature:'verified',attackerWantsInterruption:true,legitimateSession:true}},'protectiveShutdown','achieved']
])test(name,{timeout:120000},async()=>{
 const r=await runNativePolicyCase(input);
 assert.equal(r.execution,'completed',JSON.stringify(r));assert.equal(r.policy.decision,decision);assert.equal(r.policy.attacker,attacker);
 assert.equal(r.attestation.runtime,'node-native-lean');assert.equal(r.attestation.rdfWorker.documentType,'undefined');
 if(input.state.credentialSignature)assert.equal(r.operational.credentialVerified,false);
});
