#!/bin/sh
# Run from any working directory; Lean 4.33.1 is required on PATH.
set -eu
LAB=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$LAB/artifacts"
LEAN_PATH="$LAB/lean" lean --json -o "$LAB/lean/Accounts.olean" \
  "$LAB/lean/Accounts.lean" > "$LAB/artifacts/lean-positive.jsonl" 2>&1 || {
  cat "$LAB/artifacts/lean-positive.jsonl"
  echo 'Lean positive source failed' >&2
  exit 1
}
python3 - "$LAB/artifacts/lean-positive.jsonl" <<'PY'
import json, sys
expected = {
 'current_assets_components', 'acid_undefined_at_zero_liabilities',
 'exact_ratio_nonzero', 'acid_ignores_stock',
 'archived_rule8_counterexample', 'archived_rule10_counterexample',
 'archived_rule11_predicate_mismatch'
}
seen = set()
for line in open(sys.argv[1]):
    try:
        data = json.loads(line).get('data', '')
    except (json.JSONDecodeError, AttributeError):
        continue
    for name in expected:
        identity = "'SWADAccounts." + name + "'"
        if identity in data:
            if 'does not depend on any axioms' in data:
                seen.add(name)
            elif 'depends on axioms:' in data:
                raise SystemExit('Unexpected theorem axiom dependency: ' + data)
if seen != expected:
    raise SystemExit('Missing no-axiom checks: ' + repr(sorted(expected - seen)))
print('All seven Lean theorem dependencies audited: no axioms')
PY
if LEAN_PATH="$LAB/lean" lean --json "$LAB/lean/Negative.lean" \
  > "$LAB/artifacts/lean-negative.jsonl" 2>&1; then
  echo 'UNSOUND: false historical equality was accepted' >&2
  exit 1
fi
# Do not confuse a broken import with the intended rejected proof.
if grep -E -q 'unknown module|unknown identifier|failed to import|unknown constant' \
    "$LAB/artifacts/lean-negative.jsonl"; then
  cat "$LAB/artifacts/lean-negative.jsonl"
  echo 'Negative case failed for an infrastructure reason' >&2
  exit 1
fi
grep -q '"severity":"error"' "$LAB/artifacts/lean-negative.jsonl" || {
  cat "$LAB/artifacts/lean-negative.jsonl"
  echo 'No structured Lean error for negative check' >&2
  exit 1
}
echo 'Lean positive theorems accepted; deliberately false equality rejected.'
