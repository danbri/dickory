import test from 'node:test';
import assert from 'node:assert/strict';
import {smallLeanProbe,leanMobileWorkspaceLink,decodeMobileWorkspaceFragment} from './mobile-lean.js';
import {readFile} from 'node:fs/promises';

test('small original company-accounts proof round-trips through documented mobile Lean hash',async()=>{
  const url=await leanMobileWorkspaceLink(smallLeanProbe,'PhoneProbe.lean');
  const dest=new URL(url);
  assert.equal(dest.hostname,'lean.cau.li');
  assert.equal(dest.searchParams.get('variant'),'slim');
  assert(url.includes('#s='));
  const decoded=await decodeMobileWorkspaceFragment(dest.hash);
  assert.equal(decoded.active,'PhoneProbe.lean');
  assert.equal(decoded.files.length,1);
  assert.equal(decoded.files[0].content,smallLeanProbe);
  assert.match(smallLeanProbe,/acid_ignores_stock/);
  assert.match(smallLeanProbe,/#print axioms/);
  assert.match(smallLeanProbe,/#eval Lean.versionString/);
});

test('unmodified full Lean source is transferred exactly; URL fragment is not a POST',async()=>{
  const source=await readFile(new URL('./lean/Accounts.lean',import.meta.url),'utf8');
  const url=await leanMobileWorkspaceLink(source,'Accounts.lean');
  const dest=new URL(url);
  assert.equal(dest.origin,'https://lean.cau.li');
  assert.equal(dest.pathname,'/');
  assert.equal(dest.search,'?variant=slim');
  const decoded=await decodeMobileWorkspaceFragment(dest.hash);
  assert.equal(decoded.active,'Accounts.lean');
  assert.equal(decoded.files[0].content,source);
  assert.match(source,/theorem archived_rule8_counterexample/);
  const modified=await leanMobileWorkspaceLink(source+'\\n-- changed','Accounts.lean');
  assert.notEqual(modified,url);
});

test('invalid and oversized source is refused rather than silently truncated',async()=>{
  await assert.rejects(leanMobileWorkspaceLink(''),/empty/);
  await assert.rejects(leanMobileWorkspaceLink('hello','/tmp/Unsafe.lean'),/Invalid/);
  await assert.rejects(leanMobileWorkspaceLink('x'.repeat(251_000)),/limit/);
});
