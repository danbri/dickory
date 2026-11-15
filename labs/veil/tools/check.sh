#!/bin/sh
# Reproducible check of the Veil lab: fetch the pinned factoidal-core sources, build, and gate.
# Fails when the build fails (a failed #check_invariants, #model_check or #guard is an error),
# when Veil trusted an SMT answer without a reconstructed proof, or when a theorem of the lab
# rests on an axiom other than propext, Classical.choice and Quot.sound.
set -eu
cd "$(dirname "$0")/.."
./tools/fetch_core.sh
log=artifacts/build.log
lake build 2>&1 | tee "$log"
if grep -n "Trusting SMT solver" "$log"; then echo "FAIL: an SMT answer was trusted"; exit 1; fi
if grep -n "declaration uses 'sorry'" "$log"; then echo "FAIL: sorry"; exit 1; fi
grep -q "No violation" "$log" || { echo "FAIL: no model-check result read"; exit 1; }
n=$(grep -c "audit .* axioms:" "$log" || true)
[ "$n" -gt 0 ] || { echo "FAIL: the axiom audit printed nothing"; exit 1; }
if grep "audit .* axioms:" "$log" | grep -v -E "axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)*\]"; then
  echo "FAIL: an axiom other than propext, Classical.choice, Quot.sound"; exit 1
fi
echo "OK: $n theorems audited"
