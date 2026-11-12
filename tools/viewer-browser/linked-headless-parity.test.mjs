// Empirical premises of RunnerParity.lean: two real separate environments.
// Fail on disagreement. No mocked RDF answers or precomputed result files.
import test from 'node:test';
import assert from 'node:assert/strict';
import {compareCase,runBrowserCase} from './linked-headless.mjs';
import {runNodeCase} from '../../labs/linked-assurance/tools/headless/node-runner.mjs';
const cases=[
 {scenario:'vocabulary'},
 {scenario:'offer'},
 {scenario:'event'},
 {scenario:'artifact'},
 {scenario:'alert'},
 {scenario:'vocabulary',scope:'data'},
 {scenario:'vocabulary',regime:'simple'},
 {scenario:'event',variant:'no-consent'},
 {scenario:'alert',variant:'no-alert'},
 {scenario:'offer',variant:'both'}
];
for(const input of cases){
  test('Node/Chromium semantic parity: '+JSON.stringify(input),{timeout:120000},async()=>{
    const result=await compareCase(input);
    assert.equal(result.distinctRuntimes,true,'Must independently attest Node and Chromium');
    assert.equal(result.equivalence.comparable,true);
    assert.equal(result.equivalence.equivalent,true,JSON.stringify(result.equivalence));
  });
}
test('invalid TriG does not turn into a negative ASK',{timeout:120000},async()=>{
 const input={scenario:'vocabulary',variant:'invalid'};
 const [node,browser]=await Promise.all([runNodeCase(input),runBrowserCase(input)]);
 assert.equal(node.observation.execution,'parserError');
 assert.equal(browser.observation.execution,'parserError');
 assert.deepEqual(node.observation.claims,[]);
 assert.deepEqual(browser.observation.claims,[]);
});
test('Node and browser are demonstrably distinct execution environments',{timeout:120000},async()=>{
 const r=await compareCase({scenario:'vocabulary'});
 assert.equal(r.runtimeEvidence.node.runtime,'node');
 assert.equal(r.runtimeEvidence.node.windowType,'undefined');
 assert.equal(r.runtimeEvidence.node.documentType,'undefined');
 assert.equal(r.runtimeEvidence.browser.runtime,'chromium-page-worker');
 assert.equal(r.runtimeEvidence.browser.windowType,'object');
 assert.equal(r.runtimeEvidence.browser.documentType,'object');
 assert.match(r.runtimeEvidence.browser.browserProduct,/Chrome|Chromium/);
});
