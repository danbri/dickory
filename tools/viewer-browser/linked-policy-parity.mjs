// SPDX-License-Identifier: Apache-2.0
// No UI history: exactly the same serialized state bundle drives both runtimes.
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {runNativePolicyCase} from '../../labs/linked-assurance/tools/headless/policy-runner.mjs';
import {runBrowserTool} from './linked-headless.mjs';
const checks=[];
for(const input of [
 {scenario:'vocabulary',scope:'union',regime:'RDFS',budgetMs:60000,state:{}},
 {scenario:'alert',scope:'union',regime:'RDFS',budgetMs:60000,state:{credentialSignature:'verified',attackerWantsInterruption:true,legitimateSession:true}}
]){
 const node=await runNativePolicyCase(input);
 const browser=await runBrowserTool('linked_assurance_policy',input);
 assert.equal(browser.status,'completed',JSON.stringify(browser));
 const other=browser.result;
 assert.equal(node.execution,'completed');assert.equal(other.execution,'completed');
 assert.equal(node.fixtureSha256,other.fixtureSha256,'exact state and evidence, not merely same outcome');
 assert.equal(node.sourceSha256,other.sourceSha256);assert.deepEqual(node.operational,other.operational);
 assert.deepEqual(node.policy,other.policy);assert.deepEqual(node.rdfObservation,other.rdfObservation);
 assert.equal(browser.runtime.invocation,'native-WebMCP');
 checks.push({input,policy:node.policy,fixtureSha256:node.fixtureSha256,sourceSha256:node.sourceSha256,node:node.attestation,browser:other.attestation,invocation:browser.runtime.invocation});
}
await fs.mkdir(new URL('../../labs/linked-assurance/artifacts/',import.meta.url),{recursive:true});
await fs.writeFile(new URL('../../labs/linked-assurance/artifacts/profile-policy-parity.json',import.meta.url),JSON.stringify({status:'pass',checks},null,2));
console.log(JSON.stringify({status:'pass',checks:checks.length}));
