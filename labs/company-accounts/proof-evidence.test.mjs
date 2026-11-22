import test from 'node:test';
import assert from 'node:assert/strict';
import {webKitCompilerRisk,validatePublishedEvidence,REQUIRED_PROOFS,sha256Source,publishedProofSummary} from './proof-evidence.js';

const sample=()=>{
  return {
    schema:'dickory-swad-lean-evidence-v1',
    status:'pass',
    verificationLocation:'CI/native Lean 4.33.1; NOT iPhone WASM',
    compilerVersion:'Lean (version 4.33.1, x86_64-unknown-linux-gnu)',
    sourceSha256:'a'.repeat(64),negativeSourceSha256:'b'.repeat(64),
    proofs:REQUIRED_PROOFS.map(name=>({name,axioms:name==='exact_ratio_nonzero'?['propext']:[]})),
    negativeTest:{result:'expected-rejection',compilerExit:'nonzero (verified by verify.sh)',diagnostics:['tactic decide failed']},
    scope:'A chosen semantics, not importer fidelity',ci:{runUrl:'https://github.com/danbri/dickory/actions/runs/1'}
  };
};
test('all iOS browser brands and desktop Safari use the CI-evidence path',()=>{
  for(const app of ['Version/26 Mobile Safari','CriOS/156 Mobile Safari','FxiOS/150 Mobile Safari']){
    assert.equal(webKitCompilerRisk('Mozilla/5.0 (iPhone; CPU iPhone OS 26_1 like Mac OS X) AppleWebKit/605.1.15 '+app),true);
  }
  assert.equal(webKitCompilerRisk('Mozilla/5.0 (Macintosh) AppleWebKit/605.1.15 Version/26 Safari/605.1'),true);
  assert.equal(webKitCompilerRisk('Mozilla/5.0 (Macintosh) AppleWebKit/537.36 Chrome/156.0 Safari/537.36'),false);
  assert.equal(webKitCompilerRisk('', 'MacIntel', 5),true);
});
test('native evidence must be complete and have only kernel-standard axioms',()=>{
  assert.equal(validatePublishedEvidence(sample()).proofs.length,7);
  for(const mutation of [
    x=>x.proofs.pop(),
    x=>x.proofs[0].axioms=['sorryAx'],
    x=>x.proofs[1].name=x.proofs[0].name,
    x=>x.negativeTest.result='success',
    x=>x.sourceSha256='abc',
    x=>x.compilerVersion='Lean (version 0.0.0)'
  ]){
    const value=sample();mutation(value);
    assert.throws(()=>validatePublishedEvidence(value));
  }
});
test('source SHA changes on edits and CI summary discloses its provenance',async()=>{
  const hash=await sha256Source('theorem test : True := by trivial');
  assert.equal(hash.length,64);
  assert.notEqual(hash,await sha256Source('theorem test : True := by sorry'));
  const info=publishedProofSummary(sample(),true);
  assert.match(info,/NOT a browser compilation/);
  assert.match(info,/Deliberately false theorem: REJECTED/);
  assert.match(info,/propext/);
});
