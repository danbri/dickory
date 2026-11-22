/* Source-bound, CI-native proof evidence for browsers where live Lean WASM
 * cannot operate reliably. This module neither compiles Lean nor invents a
 * proof. It checks exact published source bytes and reported theorem axioms. */
export const REQUIRED_PROOFS = Object.freeze([
  'acid_ignores_stock',
  'acid_undefined_at_zero_liabilities',
  'archived_rule8_counterexample',
  'archived_rule10_counterexample',
  'archived_rule11_predicate_mismatch',
  'current_assets_components',
  'exact_ratio_nonzero'
]);
const ALLOWED_AXIOMS = new Set(['propext','Classical.choice','Quot.sound']);

export function webKitCompilerRisk(ua='',platform='',touchPoints=0) {
  // On iOS even "Chrome" and "Firefox" run on WebKit. Desktop Safari uses
  // WebKit as well; the linked-assurance compiler documents stack exhaustion.
  if (/(iPhone|iPad|iPod)/i.test(ua) || (platform==='MacIntel' && touchPoints>1)) return true;
  return /AppleWebKit/i.test(ua) && /Safari/i.test(ua) &&
    !/(Chrome|Chromium|CriOS|Edg|OPR|Opera)/i.test(ua);
}

export async function sha256Source(source) {
  const bytes = new TextEncoder().encode(source);
  const digest = await crypto.subtle.digest('SHA-256',bytes);
  return [...new Uint8Array(digest)].map(b=>b.toString(16).padStart(2,'0')).join('');
}

export function validatePublishedEvidence(record) {
  if (!record || record.schema!=='dickory-swad-lean-evidence-v1' ||
      record.status!=='pass' ||
      record.verificationLocation!=='CI/native Lean 4.33.1; NOT iPhone WASM' ||
      !/^Lean \(version 4\.33\.1\b/.test(record.compilerVersion||'') ||
      !/^[a-f0-9]{64}$/.test(record.sourceSha256||'') ||
      !/^[a-f0-9]{64}$/.test(record.negativeSourceSha256||'') ||
      record.negativeTest?.result!=='expected-rejection' ||
      record.negativeTest?.compilerExit!=='nonzero (verified by verify.sh)' ||
      !Array.isArray(record.proofs)) {
    throw Error('Published Lean evidence is missing, malformed or not a completed native check.');
  }
  const names=new Set();
  for(const proof of record.proofs){
    if (!proof || !REQUIRED_PROOFS.includes(proof.name) ||
        names.has(proof.name) || !Array.isArray(proof.axioms) ||
        proof.axioms.some(axiom=>!ALLOWED_AXIOMS.has(axiom))) {
      throw Error('Published Lean proof list or axiom audit is invalid.');
    }
    names.add(proof.name);
  }
  if (REQUIRED_PROOFS.some(name=>!names.has(name)) || record.proofs.length!==REQUIRED_PROOFS.length) {
    throw Error('Published Lean proof evidence is incomplete.');
  }
  return record;
}

export function publishedProofSummary(record, includeNegative=false) {
  const lines=[
    'Source-bound native Lean 4.33.1 CI check — NOT a browser compilation.',
    'Source SHA-256: '+record.sourceSha256,
    'Verified theorems and axiom dependencies:'
  ];
  for(const proof of record.proofs){
    lines.push('  '+proof.name+' — '+(proof.axioms.length ? proof.axioms.join(', ') : 'no axioms'));
  }
  if(includeNegative){
    lines.push('Deliberately false theorem: REJECTED by native Lean CI.');
    for(const diagnostic of record.negativeTest.diagnostics||[]){
      lines.push('  '+String(diagnostic).slice(0,1600));
    }
  }
  lines.push(record.scope);
  if (record.ci?.runUrl) lines.push('Reproduce / audit CI run: '+record.ci.runUrl);
  return lines.join('\n');
}
