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
