#!/usr/bin/env python3
"""Rebuild, extract actual elaborated dependencies, then check a frozen registry.
This program does NOT approve source extraction or formalization fidelity.
"""
from pathlib import Path
from hashlib import sha256
import json
import os
import subprocess
import sys
from source_catalogue import produce

ROOT = Path(__file__).resolve().parents[1]

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def formal_files(root=ROOT):
    # Includes unimported/untracked files anywhere in this project.
    # Lake's own build/cache tree is the sole generated-output exclusion.
    return {p.relative_to(root).as_posix(): p for p in root.rglob("*.lean")
            if ".lake" not in p.relative_to(root).parts}

def validate(registry, evidence, catalogue, files=None, questions=None):
    errors = []
    files = formal_files() if files is None else files
    registered_files = {x["path"]: x for x in registry["files"]}
    if set(files) != set(registered_files):
        errors.append("Formal file inventory mismatch: " +
                      str(sorted(set(files) ^ set(registered_files))))
    for path in set(files) & set(registered_files):
        if digest(files[path]) != registered_files[path]["sha256"]:
            errors.append("Changed formal file: " + path)
    rows = {r["name"]: r for r in evidence["declarations"]}
    if len(rows) != len(evidence["declarations"]):
        errors.append("Duplicate elaborated declaration names")
    local = {n: r for n, r in rows.items() if r["module"].split(".")[0] in ["RDF11", "Audit"]}
    registered = {r["name"]: r for r in registry["declarations"]}
    if set(local) != set(registered):
        errors.append("Declaration inventory mismatch: " +
                      str(sorted(set(local) ^ set(registered))))
    claims = {r["id"]: r for r in catalogue["claims"]}
    known_refs = set(claims) | {r["id"] for r in catalogue["dispositions"]}
    for doc in catalogue["documents"]:
        cursor = 0
        for atom in doc["atoms"]:
            if atom["start"] != cursor or not cursor < atom["end"] <= doc["scalars"]:
                errors.append("Invalid source partition: " + doc["id"])
            if not atom["refs"] or set(atom["refs"]) - known_refs:
                errors.append("Unknown source disposition/reference: " + doc["id"])
            cursor = atom["end"]
        if cursor != doc["scalars"]:
            errors.append("Uncovered source suffix: " + doc["id"])
    if questions is None:
        questions = json.loads((ROOT / "catalogue/open-questions.json").read_text())["questions"]
    passages = {p["id"] for p in catalogue["passages"]}
    for question in questions:
        if set(question["claim_ids"]) - set(claims):
            errors.append("Unknown claim in source question: " + question["id"])
        if set(question["passage_ids"]) - passages:
            errors.append("Unknown passage in source question: " + question["id"])
        if set(question["lean"]) - set(local):
            errors.append("Unknown Lean binding in source question: " + question["id"])
    foundations = {r["id"]: r for r in registry["foundations"]}
    def check_foundation(fid, stack):
        if fid in stack:
            errors.append("Cyclic foundation grounding: " + fid)
            return
        for dep in foundations[fid]["requires"]:
            if dep in foundations:
                check_foundation(dep, stack | {fid})
            elif dep not in claims:
                errors.append("Unknown foundation grounding: " + dep)
    for fid in foundations:
        check_foundation(fid, set())
    for n, r in local.items():
        owner = registered.get(n)
        if not owner:
            continue
        if any(owner[k] != r[k] for k in ["module", "kind", "type"]):
            errors.append("Changed declaration signature: " + n)
        if not owner["grounds"]:
            errors.append("Ungrounded local declaration: " + n)
        for ground in owner["grounds"]:
            if ground not in claims and ground not in foundations:
                errors.append("Unknown grounding reference: " + ground)
        if owner["role"] not in ["source_mapping", "proof_support", "engineering_refinement",
                                 "foundation", "coverage_certificate"]:
            errors.append("Unknown declaration role: " + n)
        if r["unsafe"]:
            errors.append("Unsafe local declaration: " + n)
        if r["kind"] == "axiom":
            errors.append("Local axiom: " + n)
        if set(r["axioms"]) - set(registry["allowed_axioms"]):
            errors.append("Unapproved axioms: " + n)
    for r in rows.values():
        for dep in r["dependencies"]:
            if dep not in rows:
                errors.append("Missing elaborated dependency: " + dep)
        if r["name"] not in local and r["module"] not in registry["foundation_modules"]:
            errors.append("Unknown foundation module: " + r["module"])
    if evidence["lean_version"] != registry["lean_version"]:
        errors.append("Lean version changed")
    for claim in claims.values():
        mapping = claim["cleanroom_mapping"]
        if mapping:
            for binding in mapping["bindings"]:
                if binding["lean"] not in local:
                    errors.append("Unresolved claim binding: " + binding["lean"])
                elif claim["id"] not in registered[binding["lean"]]["grounds"]:
                    errors.append("Missing reverse mapping: " + binding["lean"])
            if not claim["passages"]:
                errors.append("Mapped claim lacks source passage: " + claim["id"])
    return sorted(set(errors))

def complete_coverage_errors(catalogue):
    errors = []
    if any(not d["accepted_accountability_certificate"] for d in catalogue["documents"]):
        errors.append("No accepted source-accountability certificate")
    if any(a["disposition"] == "unresolved" for d in catalogue["documents"] for a in d["atoms"]):
        errors.append("Unresolved source characters remain")
    if any(c["extraction_review"] != "accepted" for c in catalogue["claims"]):
        errors.append("Source-to-claim expert reviews pending")
    if any(c["formalization_review"] != "accepted" or not c["cleanroom_mapping"]
           for c in catalogue["claims"]):
        errors.append("Claim-to-Lean mappings or expert reviews incomplete")
    errors.append("Published-artifact refinement has not been established")
    errors.append("Generalized-instance source-scope question awaits expert adjudication")
    return errors

def run_logged(args, logfile, env):
    with (ROOT / "artifacts" / logfile).open("w") as stream:
        result = subprocess.run(args, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{' '.join(args)} failed; see artifacts/{logfile}")

def main():
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    for path, expected in produce().items():
        if (ROOT / path).read_bytes() != expected.encode("utf-8"):
            raise RuntimeError("Stale source catalogue/certificate: " + path)
    run_logged(["lake", "build"], "build.log", env)
    run_logged(["lake", "env", "lean", "Audit/Export.lean"], "audit-build.log", env)
    registry = json.loads((ROOT / "catalogue/registry.json").read_text())
    evidence = json.loads((ROOT / "artifacts/declarations.json").read_text())
    catalogue = json.loads((ROOT / "catalogue/claims.json").read_text())
    errors = validate(registry, evidence, catalogue)
    complete_errors = complete_coverage_errors(catalogue)
    report = {
        "build_and_registry": "pass" if not errors else "fail",
        "errors": errors,
        "local_declarations": len(registry["declarations"]),
        "dependency_closure_declarations": len(evidence["declarations"]),
        "mapped_claim_records_including_partial": sum(c["cleanroom_mapping"] is not None
                                                     for c in catalogue["claims"]),
        "preliminary_claim_records": len(catalogue["claims"]),
        "accepted_extraction_reviews": 0, "accepted_formalization_reviews": 0,
        "complete_coverage": False, "complete_coverage_blockers": complete_errors,
        "file_hashes": {p: digest(f) for p, f in formal_files().items()},
        "registry_sha256": digest(ROOT / "catalogue/registry.json"),
        "catalogue_sha256": digest(ROOT / "catalogue/claims.json"),
        "dependencies_sha256": digest(ROOT / "artifacts/declarations.json"),
        "allowed_axioms": registry["allowed_axioms"]
    }
    (ROOT / "artifacts/verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in
                      ["file_hashes", "registry_sha256", "catalogue_sha256", "dependencies_sha256"]},
                     indent=2))
    return 1 if errors else (2 if "--require-complete" in sys.argv and complete_errors else 0)

if __name__ == "__main__":
    raise SystemExit(main())

