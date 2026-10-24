#!/usr/bin/env python3
"""Meaningful negative checks for the registry and representation boundary."""
import copy
import json
import os
from pathlib import Path
import subprocess
from verify import ROOT, validate, formal_files, complete_coverage_errors

registry = json.loads((ROOT / "catalogue/registry.json").read_text())
evidence = json.loads((ROOT / "artifacts/declarations.json").read_text())
catalogue = json.loads((ROOT / "catalogue/claims.json").read_text())
assert not validate(registry, evidence, catalogue)
results = []

# An unimported file must not silently escape the formal-folder inventory.
probe = ROOT / "Audit/UnregisteredMutation.lean"
assert not probe.exists()
try:
    probe.write_text("-- Deliberately unregistered mutation fixture.\n")
    errors = validate(registry, evidence, catalogue)
    assert any("Formal file inventory mismatch" in e for e in errors), errors
    results.append("unimported formal file rejected")
finally:
    probe.unlink()

# A typed source symbol must resolve, not merely look like a Lean name.
bad = copy.deepcopy(catalogue)
mapped = next(c for c in bad["claims"] if c["cleanroom_mapping"])
mapped["cleanroom_mapping"]["bindings"][0]["lean"] = "RDF11.Nonexistent"
assert any("Unresolved claim binding" in e for e in validate(registry, evidence, bad))
results.append("nonexistent Lean binding rejected")

bad = copy.deepcopy(catalogue)
bad["documents"][0]["atoms"][0]["refs"] = ["MISSING-SOURCE-RECORD"]
assert any("Unknown source disposition/reference" in e for e in validate(registry, evidence, bad))
results.append("unknown source disposition rejected")

# Closure includes constants used in elaborated proofs, not just named imports.
bad = copy.deepcopy(evidence)
target = next(r for r in bad["declarations"] if r["name"] == "RDF11.SimplyEntails")
target["dependencies"].append("Missing.HiddenImplicit")
assert any("Missing elaborated dependency" in e for e in validate(registry, bad, catalogue))
results.append("missing elaborated dependency rejected")

bad = copy.deepcopy(evidence)
target = next(r for r in bad["declarations"] if r["name"] == "RDF11.subgraph_entailment")
target["axioms"].append("sorryAx")
assert any("Unapproved axioms" in e for e in validate(registry, bad, catalogue))
results.append("proof placeholder dependency rejected")

assert complete_coverage_errors(catalogue)
results.append("complete-coverage request rejected for this draft")

# Actual Lean type checking, not a Python emulation of uniqueness.
env = dict(os.environ)
env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
snippet = """import RDF11
open RDF11
def duplicateEnumeration : Enumeration (Set.ofList [0, 0]) where
  triples := [0, 0]
  nodup := by simp
  membership := by intro t; rfl
"""
run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                     input=snippet, text=True, capture_output=True)
log = run.stdout + run.stderr
(ROOT / "artifacts/duplicate-rejected.log").write_text(log)
assert run.returncode != 0 and "False" in log and "unsolved goals" in log, log
results.append("Lean rejects duplicate-bearing Enumeration")

# Admission is required before entailment; illegal syntax is not vacuous success.
snippet = """import RDF11
open RDF11
def rejectedEmpty : (ExtensionBoundary.requiresTriple (Literal := Unit) () () () : SemanticExtension.{0} Unit Unit).AdmissibleGraph Unit where
  val := Set.empty
  property := by simp [ExtensionBoundary.requiresTriple, Set.empty]
"""
run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                     input=snippet, text=True, capture_output=True)
log = run.stdout + run.stderr
(ROOT / "artifacts/inadmissible-graph-rejected.log").write_text(log)
assert run.returncode != 0 and "False" in log and "unsolved goals" in log, log
results.append("Lean rejects an inadmissible graph before entailment")

snippet = """import RDF11
open RDF11
def wrongDecoder : ClosureEvaluation.ContainerDecoder (fun n : Nat => n + 1) where
  decode := fun _ => some 0
  correct := by intro a n; cases a <;> cases n <;> simp
"""
run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                     input=snippet, text=True, capture_output=True)
log = run.stdout + run.stderr
(ROOT / "artifacts/decoder-rejected.log").write_text(log)
assert run.returncode != 0 and "False" in log and "unsolved goals" in log, log
results.append("Lean rejects an incorrect indexed-name decoder")

snippet = """import RDF11
open RDF11
def nextFact (_ : List Nat) : List Nat := [1]
example : FiniteSaturation.stable nextFact (FiniteSaturation.run nextFact 0 []) = true := by
  change false = true
  simp
"""
run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                     input=snippet, text=True, capture_output=True)
log = run.stdout + run.stderr
(ROOT / "artifacts/unsaturated-result-rejected.log").write_text(log)
assert run.returncode != 0 and "False" in log and "unsolved goals" in log, log
results.append("Lean rejects a zero-fuel result as saturated")

snippet = """import RDF11
open RDF11
def illegalConclusion : Bool := InstanceSearch.ordinaryCheck
  [(GeneralizedScope.substitutedTriple false true : GeneralizedTriple Bool Unit Unit)]
  [GeneralizedScope.originalTriple false]
"""
run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                     input=snippet, text=True, capture_output=True)
log = run.stdout + run.stderr
(ROOT / "artifacts/generalized-decision-rejected.log").write_text(log)
assert run.returncode != 0 and "type mismatch" in log.lower() and "Triple" in log, log
results.append("Lean rejects a generalized conclusion at the ordinary decision interface")

snippet = """import RDF11
open RDF11
example : InstanceSearch.check
  ([⟨.iri false, .iri false, .iri false⟩, ⟨.iri true, .iri true, .iri true⟩] :
    List (GeneralizedTriple Bool Unit Unit))
  [⟨.blank (), .iri false, .iri false⟩, ⟨.blank (), .iri true, .iri true⟩] = true := by
  change false = true
  simp
"""
run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                     input=snippet, text=True, capture_output=True)
log = run.stdout + run.stderr
(ROOT / "artifacts/incompatible-blank-witnesses-rejected.log").write_text(log)
assert run.returncode != 0 and "False" in log and "unsolved goals" in log, log
results.append("Lean rejects independent witnesses for one shared conclusion blank")

for label, filename, snippet in [
    ("Lean rejects an untagged langString literal", "untagged-langstring-rejected.log",
     """import RDF11
open RDF11
def missingTag : StructuredLiteral Unit () := .typed "text" ⟨(), by simp⟩
"""),
    ("Lean rejects an empty language tag", "empty-language-tag-rejected.log",
     """import RDF11
open RDF11
def emptyTag : BCP47.Tag := ⟨"", by
  apply BCP47.wellFormed_of_primary
  simp [BCP47.subtag, asciiLower, String.map_eq_internal]⟩
""")]:
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, env=env,
                         input=snippet, text=True, capture_output=True)
    log = run.stdout + run.stderr
    (ROOT / "artifacts" / filename).write_text(log)
    assert run.returncode != 0 and "False" in log and "unsolved goals" in log, log
    results.append(label)

(ROOT / "artifacts/negative-checks.json").write_text(json.dumps(
    {"status": "pass", "checks": results}, indent=2) + "\n")
print(json.dumps(results, indent=2))

