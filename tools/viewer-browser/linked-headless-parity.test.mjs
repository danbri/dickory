import test from 'node:test';
import assert from 'node:assert/strict';
import {compareCase,runBrowserTool} from './linked-headless.mjs';
for(const input of [{scenario:'vocabulary'},{scenario:'offer'},{scenario:'event'},{scenario:'artifact'},
 {scenario:'alert'},{scenario:'vocabulary',scope:'data'},{scenario:'vocabulary',regime:'simple'},
 {scenario:'event',variant:'no-consent'},{scenario:'alert',variant:'no-alert'},{scenario:'offer',variant:'both'}]){
 test('actual Node/native-WebMCP parity '+JSON.stringify(input),{timeout:120000},async()=>{
  const r=await compareCase({...input,budgetMs:60000});
  assert.equal(r.distinctRuntimes,true);assert.equal(r.equivalence.equivalent,true,JSON.stringify(r));
  assert.equal(r.runtimeEvidence.browser.invocation,'native-WebMCP');
  assert.equal(r.runtimeEvidence.node.documentType,'undefined');
 });
}
test('native WebMCP exposes all four shared operations',{timeout:120000},async()=>{
 const r=await runBrowserTool('linked_assurance_cases');
 assert.equal(r.status,'completed');assert(r.runtime.names.includes('linked_assurance_policy'));
 assert(r.runtime.names.includes('linked_assurance_check_policy'));assert.equal(r.runtime.invocation,'native-WebMCP');
});
