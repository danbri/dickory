import {checkLean, auditContract, compilerEnvironment, compilerUnavailableReason, diagnosticText} from '../linked-assurance/lean-host.js';
import {webKitCompilerRisk, sha256Source, validatePublishedEvidence, publishedProofSummary} from './proof-evidence.js';
import {leanMobileWorkspaceLink,smallLeanProbe} from './mobile-lean.js';
import {mountInlineCompiler} from './inline-lean-controller.js';

const $ = id => document.getElementById(id);
const archive = JSON.parse($('inlineArchive').textContent);
const byName = new Map(archive.files.map(item => [item.name, item]));
const rules = [
  ['Return on net assets', '100 × operating profit / net assets', 'The denominator must be nonzero.'],
  ['Profit margin', '100 × operating profit / sales revenue', 'The 2004 prose omits the percent factor used by implementations.'],
  ['Asset turnover', 'sales revenue / net assets', 'A dimensionless ratio, not a percentage.'],
  ['Estimated employees', 'sales revenue / sales per employee', 'The old factor 1,000,000 needs independent unit evidence; headcount integrality is not assumed.'],
  ['Operating profit per employee', 'operating profit / employee count', 'N3 and MathML solve the inverse equation. That is distinct from calculating profit per head.'],
  ['Non-UK sales percentage', '100 × non-UK sales / total sales', 'An exactly zero non-UK numerator is legitimate; the old N3 guard excludes it.'],
  ['Current ratio', '(stock + debtors + cash) / current liabilities', 'N3 solves for current assets instead, given current ratio.'],
  ['Acid-test ratio', '(debtors + cash) / current liabilities', 'Original N3 adds stock and emits corp:at, colliding with asset turnover.'],
  ['Current assets', 'stock + debtors + cash', 'The lab deliberately limits assets to these three components.'],
  ['Debtor days', '365 × debtors / annual sales', 'A declared modern annual-period convention. The archived formula differs by scaling and division direction.'],
  ['Stock days', '365 × stock / annual cost of sales', 'Modern annual-period convention. Archive has conflicting scalings and emits corp:dd.']
];
const required = [
  'SWADAccounts.acid_ignores_stock',
  'SWADAccounts.archived_rule8_counterexample',
  'SWADAccounts.archived_rule10_counterexample',
  'SWADAccounts.archived_rule11_predicate_mismatch'
];
const contract = [
 '#check (SWADAccounts.acid_ignores_stock :',
 '  ∀ (a : SWADAccounts.Accounts) (replacement : SWADAccounts.Money),',
 '    SWADAccounts.acidTest { a with stock := replacement } = SWADAccounts.acidTest a)',
 '#check (SWADAccounts.archived_rule8_counterexample :',
 '  SWADAccounts.sameExactValue (SWADAccounts.acidTest SWADAccounts.fixture) (SWADAccounts.archivedN3AcidTest SWADAccounts.fixture) = false)',
 '#check (SWADAccounts.archived_rule10_counterexample :',
 '  SWADAccounts.sameExactValue (SWADAccounts.debtorDays SWADAccounts.fixture) (SWADAccounts.archivedN3DebtorDays SWADAccounts.fixture) = false)',
 '#check (SWADAccounts.archived_rule11_predicate_mismatch :',
 '  SWADAccounts.archivedStockOutputPredicate ≠ SWADAccounts.stockOutputPredicate)',
 ...required.map(name => '#print axioms ' + name)
].join('\n') + '\n';

let initialLean = '';
let publishedEvidence = null;
let mobileLinkGeneration = 0;
async function updateMobileLeanLink(source) {
  const generation = ++mobileLinkGeneration;
  const el = $('mobileFull');
  el.removeAttribute('href');
  el.setAttribute('aria-disabled','true');
  $('mobileLeanStatus').textContent='Encoding current Lean source for the slim mobile compiler…';
  try {
    const url=await leanMobileWorkspaceLink(source,'Accounts.lean');
    if(generation!==mobileLinkGeneration)return;
    el.href=url;
    el.setAttribute('aria-disabled','false');
    $('mobileLeanStatus').textContent='Ready. The link contains your editor source in its fragment; the destination will only compile after you press Run there.';
  } catch(error) {
    if(generation!==mobileLinkGeneration)return;
    $('mobileLeanStatus').textContent='Could not generate mobile Lean link: '+String(error.message||error);
  }
}
async function prepareMobileLeanProbe() {
  try {
    const link=$('mobileProbe');
    link.href=await leanMobileWorkspaceLink(smallLeanProbe,'PhoneProbe.lean');
    link.target='_blank';
    link.rel='noopener noreferrer';
    link.setAttribute('aria-disabled','false');
  } catch(error) {
    $('mobileLeanStatus').textContent='Could not prepare mobile Lean probe: '+String(error.message||error);
  }
}
const webKitRisk = webKitCompilerRisk(navigator.userAgent, navigator.platform, navigator.maxTouchPoints);

async function loadPublishedEvidence() {
  const response = await fetch('./artifacts/lean-evidence.json', {cache:'no-store'});
  if(!response.ok) throw Error('Published native Lean evidence could not be fetched.');
  const record = validatePublishedEvidence(await response.json());
  const exactHash = await sha256Source(initialLean);
  if(record.sourceSha256 !== exactHash) throw Error('Published evidence SHA-256 does not match the shipped Accounts.lean bytes.');
  publishedEvidence = record;
  $('publishedSummary').textContent = publishedProofSummary(record, true);
  $('publishedProofDetail').open = webKitRisk;
  $('proofStatus').textContent = webKitRisk
    ? 'PUBLISHED CI PROOF VERIFIED FOR REPOSITORY SOURCE — native Lean 4.33.1, not compiled on this phone.'
    : 'Seven native Lean proofs verified during the site build. You can also run the live WASM compiler on a supported browser.';
  return record;
}

async function showPublishedForCurrentSource(includeNegative=false) {
  if (!publishedEvidence) {
    $('proofStatus').textContent = 'No independently checked native evidence is available; no proof is claimed.';
    $('diagnostics').textContent = 'Published evidence was not loaded or failed its integrity checks.';
    return false;
  }
  const current = await sha256Source($('leanCode').value);
  if(current !== publishedEvidence.sourceSha256) {
    $('proofStatus').textContent = 'EDITED SOURCE — NOT VERIFIED. The published Lean proof covers only the original exact bytes. Use desktop Chrome for a new interactive check.';
    $('diagnostics').textContent = 'Current source SHA-256: '+current+
      '\nVerified source SHA-256: '+publishedEvidence.sourceSha256+
      '\nNo Lean compilation or theorem check has been performed on these edits.';
    return false;
  }
  $('proofStatus').textContent = includeNegative
    ? 'CI NEGATIVE TEST: expected rejection confirmed for the unmodified source. Not a browser-local compiler run.'
    : 'CI PROOFS: seven Lean theorems accepted for the exact unmodified source. Not checked on this device.';
  $('diagnostics').textContent = publishedProofSummary(publishedEvidence, includeNegative);
  return true;
}

function getSource(short) { return byName.get('tests/' + short)?.text || 'Missing archived source: ' + short; }
function displayRule() {
  const n = Number($('rule').value), [title, summary, finding] = rules[n-1];
  $('ruleTitle').textContent = String(n) + ' / ' + title;
  $('ruleSummary').textContent = 'Lean reference: ' + summary;
  $('ruleFinding').textContent = 'Review note: ' + finding;
  $('n3Code').textContent = getSource('cwm' + n + '.n3');
  $('mathCode').textContent = getSource('mmlrule' + n + '.mml');
  $('n3Output').textContent = getSource('_out_cwm' + n + '.n3');
  $('mathOutput').textContent = getSource('_out_mml' + n + '.txt');
}
function selected() { return byName.get($('sourceFile').value); }
function displaySource() {
  const file = selected();
  if (!file) return;
  $('fileMeta').textContent = file.name + ' · ' + file.bytes + ' bytes · SHA-256 ' + file.sha256 +
    ' · original: ' + file.url;
  $('sourceText').textContent = file.encoding === 'base64'
    ? '(Binary ZIP, ' + file.bytes + ' bytes). Contents:\n' + (file.members || []).join('\n')
    : file.text;
}
function downloadBytes(file) {
  if (file.encoding === 'base64') {
    const binary = atob(file.base64);
    return Uint8Array.from(binary, x => x.charCodeAt(0));
  }
  if (file.encoding === 'latin-1') {
    return Uint8Array.from(file.text, x => x.charCodeAt(0));
  }
  return new TextEncoder().encode(file.text);
}
function downloadBlob(name, bytes, type='application/octet-stream') {
  const url = URL.createObjectURL(new Blob([bytes], {type}));
  const a = document.createElement('a');
  a.href = url; a.download = name; a.click();
  setTimeout(() => URL.revokeObjectURL(url), 3000);
}
function showIsolation() {
  const env = compilerEnvironment(), reason = compilerUnavailableReason();
  if(webKitRisk) {
    $('isolationStatus').textContent = env.isolated && env.sharedMemory
      ? 'Browser isolation is enabled. The experimental inline 4.33.1 compiler can be started using Verify locally. The native CI proofs remain available separately.'
      : 'Inline Lean needs browser isolation and shared memory. Enable isolation once to try the smaller-export 4.33.1 runtime. This is experimental on iPhone.';
    $('enableIsolation').hidden = env.isolated && env.sharedMemory;
    $('runProofs').textContent = 'Inspect published Lean proof record';
    $('runNegative').textContent = 'Inspect CI rejection of false theorem';
    $('proofMode').textContent = 'Two independent paths: source-hash verified CI record, or on-demand on-device Lean 4.33.1 compilation via the experimental inline compiler below.';
    return;
  }
  $('isolationStatus').textContent = reason || 'Cross-origin isolation and shared memory ready; Lean can start here.';
  $('enableIsolation').hidden = env.isolated && env.sharedMemory;
  $('proofMode').textContent = 'Live Lean/WASM proof checking available where supported; published CI evidence is also available below.';
}
async function isolate() {
  if (window.self !== window.top) throw Error('Open the lab in a full browser tab, not an embedded iframe.');
  if (!navigator.serviceWorker) throw Error('Browser service workers are unavailable.');
  const reg = await navigator.serviceWorker.register(new URL('./coi-sw.js', import.meta.url), {
    scope: new URL('./', import.meta.url).href, updateViaCache:'none'
  });
  await reg.update();
  const worker = reg.installing || reg.waiting || reg.active;
  if (!worker) throw Error('No isolation helper was installed.');
  await new Promise((resolve, reject) => {
    if (worker.state === 'activated') return resolve();
    const fail = setTimeout(() => reject(Error('Isolation service worker activation timed out.')), 15000);
    const check = () => {
      if (worker.state === 'activated') {
        clearTimeout(fail); worker.removeEventListener('statechange', check); resolve();
      }
    };
    worker.addEventListener('statechange', check);
    check();
  });
  await new Promise((resolve, reject) => {
    if (navigator.serviceWorker.controller === worker) return resolve();
    const fail = setTimeout(() => reject(Error('The isolation helper did not take control.')), 15000);
    const check = () => {
      if (navigator.serviceWorker.controller === worker) {
        clearTimeout(fail);
        navigator.serviceWorker.removeEventListener('controllerchange', check);
        resolve();
      }
    };
    navigator.serviceWorker.addEventListener('controllerchange', check);
    check();
  });
  location.reload();
}
async function runPositive() {
  const source = $('leanCode').value;
  if(webKitRisk) return showPublishedForCurrentSource(false);
  let result;
  try {
    result = await checkLean(source + '\n' + contract, progress => {
      $('proofStatus').textContent = progress;
    });
  } catch(error) {
    const matched = await showPublishedForCurrentSource(false);
    $('proofStatus').textContent = 'LOCAL WASM COMPILER FAILED: '+String(error.message||error).split('\n')[0]+
      (matched?' — matching native CI proofs are shown below; this is NOT a browser proof.':
        ' — no proof accepted for these editor bytes.');
    return false;
  }
  if(result.runtimeFault) {
    const matched = await showPublishedForCurrentSource(false);
    const reason = /Maximum call stack|stack overflow/i.test(diagnosticText(result))
      ? 'WebKit/WASM stack exhausted'
      : 'WASM runtime fault';
    $('proofStatus').textContent = reason+'. '+(matched
      ? 'The unmodified source has independently checked native CI evidence below; the local compilation did not succeed.'
      : 'The edited source remains unverified.');
    return false;
  }
  $('diagnostics').textContent = diagnosticText(result);
  const contractOkay = result.accepted && required.every(name => auditContract(result, name));
  const status = contractOkay ? 'LIVE WASM CHECK ACCEPTED: required theorem types and permitted axiom audit' :
    result.accepted ? 'INCOMPLETE: Lean accepted this file, but the required axiom audit is not established' :
    'REJECTED: Lean did not accept this file or its required theorems';
  $('proofStatus').textContent = status + '\nCompiler ' + (result.compilerVersion || '?');
  return contractOkay;
}
async function runNegative() {
  if(webKitRisk) {
    await showPublishedForCurrentSource(true);
    return;
  }
  const okay = await runPositive();
  if (!okay) {
    $('proofStatus').textContent += '\nNo live negative test was run because the positive check did not succeed.';
    return;
  }
  const falseClaim = '\nexample : SWADAccounts.sameExactValue (SWADAccounts.acidTest SWADAccounts.fixture) ' +
    '(SWADAccounts.archivedN3AcidTest SWADAccounts.fixture) = true := by decide\n';
  let result;
  try {
    result = await checkLean($('leanCode').value + '\n' + contract + falseClaim, progress => {
      $('proofStatus').textContent = progress;
    });
  } catch(error) {
    $('proofStatus').textContent = 'LOCAL WASM COMPILER FAILURE, not a rejection: '+String(error.message||error).split('\n')[0];
    return;
  }
  if(result.runtimeFault) {
    $('proofStatus').textContent = 'WASM compiler runtime failure, not a successful rejection.';
    $('diagnostics').textContent = diagnosticText(result).slice(0,2000);
    return;
  }
  $('diagnostics').textContent = diagnosticText(result);
  if(result.exitCode===0 || result.accepted) {
    $('proofStatus').textContent = 'ALARM: the deliberately false claim was accepted.';
  } else {
    $('proofStatus').textContent = 'EXPECTED LIVE REJECTION: Lean refused the false rule-8 equality. Positive obligations were checked locally first.';
  }
}
async function guard(fn) {
  $('runProofs').disabled = $('runNegative').disabled = true;
  try { await fn(); }
  catch (error) {
    $('proofStatus').textContent = 'Check failed: ' + (error?.message || String(error));
  } finally { $('runProofs').disabled = $('runNegative').disabled = false; }
}
async function start() {
  $('sourceCount').textContent = archive.files.length;
  $('archiveStatus').textContent = archive.testDirCount + ' test-directory files + ' +
    archive.relatedCount + ' linked documents; each stored inline with SHA-256 and original URL.';
  for (let n=1; n<=11; n++) $('rule').add(new Option(String(n) + ' — ' + rules[n-1][0], String(n)));
  $('rule').addEventListener('change', displayRule);
  for (const file of archive.files) $('sourceFile').add(new Option(file.name, file.name));
  $('sourceFile').addEventListener('change', displaySource);
  displayRule(); displaySource();
  $('downloadSource').onclick = () => {
    const f = selected();
    downloadBlob(f.name.split('/').at(-1), downloadBytes(f));
  };
  $('downloadManifest').onclick = () => {
    const summary = archive.files.map(({name,url,sha256,bytes,encoding}) =>
      ({name,url,sha256,bytes,encoding}));
    downloadBlob('swad-archive-manifest.json',
      new TextEncoder().encode(JSON.stringify({origin:archive.origin,files:summary},null,2)),
      'application/json');
  };
  $('enableIsolation').onclick = async () => {
    try { await isolate(); }
    catch (error) { $('isolationStatus').textContent = 'Isolation failed: ' + error.message; }
  };
  showIsolation();
  const response = await fetch('./lean/Accounts.lean');
  if (!response.ok) throw Error('Repository Lean source missing from site');
  initialLean = await response.text();
  $('leanCode').value = initialLean;
  mountInlineCompiler({source:()=> $('leanCode').value,contract});
  $('mobileFull').target='_blank';
  $('mobileFull').rel='noopener noreferrer';
  await prepareMobileLeanProbe();
  await updateMobileLeanLink(initialLean);
  let mobileDebounce;
  $('leanCode').addEventListener('input', () => {
    $('proofStatus').textContent = 'Source edited — no current proof check for these bytes. The published CI record is for the original source only.';
    $('diagnostics').textContent = '';
    clearTimeout(mobileDebounce);
    mobileDebounce=setTimeout(()=>updateMobileLeanLink($('leanCode').value),250);
  });
  try {
    await loadPublishedEvidence();
  } catch(error) {
    $('proofStatus').textContent = 'Published proof evidence unavailable: '+error.message;
    $('publishedSummary').textContent = 'No verified native proof record is available.';
  }
  $('runProofs').onclick = () => guard(runPositive);
  $('runNegative').onclick = () => guard(runNegative);
  $('resetCode').onclick = () => {
    $('leanCode').value = initialLean;
    updateMobileLeanLink(initialLean);
    if(webKitRisk) guard(() => showPublishedForCurrentSource(false));
    else $('proofStatus').textContent = 'Restored repository source. Run the browser compiler for a new local check, or inspect the native CI report.';
  };
}
start().catch(error => {
  $('archiveStatus').textContent = 'Lab startup error: ' + error.message;
});
