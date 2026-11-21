#!/usr/bin/env python3
"""Materialize a falsifiable, source-bound native Lean assurance record.

Only call after verify.sh has accepted Accounts.lean and rejected Negative.lean.
This is NOT a browser compiler result, and does not certify modified editor text.
"""
from __future__ import annotations

from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "current_assets_components",
    "acid_undefined_at_zero_liabilities",
    "exact_ratio_nonzero",
    "acid_ignores_stock",
    "archived_rule8_counterexample",
    "archived_rule10_counterexample",
    "archived_rule11_predicate_mismatch",
}

def messages(path: Path) -> list:
    rows = []
    for raw in path.read_text().splitlines():
        if not raw.strip():
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"Non-JSON compiler diagnostic in {path}: {raw[:120]}") from exc
        if isinstance(obj, dict):
            rows.append(obj)
    return rows

def main():
    source_path = HERE / "lean/Accounts.lean"
    negative_path = HERE / "lean/Negative.lean"
    positives = messages(HERE / "artifacts/lean-positive.jsonl")
    negatives = messages(HERE / "artifacts/lean-negative.jsonl")
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "version 4.33.1" not in version:
        raise SystemExit(f"Unexpected native Lean version: {version}")

    if any(m.get("severity") == "error" for m in positives):
        raise SystemExit("Positive check contained Lean errors")

    proofs = {}
    pattern = re.compile(
        r"^'SWADAccounts\.([A-Za-z0-9_]+)' "
        r"(does not depend on any axioms|depends on axioms: \[([^\]]*)\])$"
    )
    for row in positives:
        value = row.get("data", "")
        found = pattern.fullmatch(value) if isinstance(value, str) else None
        if not found:
            continue
        name = found.group(1)
        if name not in EXPECTED:
            continue
        if name in proofs:
            raise SystemExit("Duplicate Lean axiom record for " + name)
        axioms = sorted({item.strip() for item in (found.group(3) or "").split(",") if item.strip()})
        if not set(axioms).issubset(ALLOWED):
            raise SystemExit("Disallowed axiom for " + name + ": " + str(axioms))
        proofs[name] = {"name": name, "axioms": axioms}
    if set(proofs) != EXPECTED:
        raise SystemExit(f"Missing proof diagnostics: {sorted(EXPECTED - set(proofs))}")

    errors = [m.get("data", "") for m in negatives if m.get("severity") == "error"]
    if not errors:
        raise SystemExit("Negative test did not produce a Lean error")
    if any(re.search("unknown module|unknown identifier|failed to import|unknown constant", e, re.I)
           for e in errors):
        raise SystemExit("Negative test failed for an infrastructure reason")
    # The source of the negative check is strictly tied to the known false
    # concrete comparison; the compiler's nonzero exit was gated by verify.sh.
    if "sameExactValue (acidTest fixture) (archivedN3AcidTest fixture) = true" not in negative_path.read_text():
        raise SystemExit("Unexpected negative-test source; inspect before accepting")
    record = {
        "schema": "dickory-swad-lean-evidence-v1",
        "status": "pass",
        "verificationLocation": "CI/native Lean 4.33.1; NOT iPhone WASM",
        "compilerVersion": version,
        "sourceSha256": sha256(source_path.read_bytes()).hexdigest(),
        "negativeSourceSha256": sha256(negative_path.read_bytes()).hexdigest(),
        "sourcePath": "lean/Accounts.lean",
        "negativeSourcePath": "lean/Negative.lean",
        "proofs": [proofs[name] for name in sorted(EXPECTED)],
        "negativeTest": {
            "source": "lean/Negative.lean",
            "compilerExit": "nonzero (verified by verify.sh)",
            "result": "expected-rejection",
            "diagnostics": [str(x)[:1800] for x in errors[:3]],
        },
        "ci": {
            "commit": os.getenv("GITHUB_SHA", "local-uncommitted-preview"),
            "runUrl": ("https://github.com/danbri/dickory/actions/runs/" + os.environ["GITHUB_RUN_ID"])
                      if os.getenv("GITHUB_RUN_ID") else None,
        },
        "scope": ("Proofs about the declared Lean accounting model, not an "
                  "independent proof of W3C input-field units or N3/MathML interpreter fidelity"),
    }
    output = HERE / "artifacts/lean-evidence.json"
    output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Published source-bound native Lean evidence: {len(proofs)} audited theorems, "
          f"negative rejection, SHA-256 {record['sourceSha256']}")

if __name__ == "__main__":
    main()
