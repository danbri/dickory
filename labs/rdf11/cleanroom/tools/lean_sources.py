#!/usr/bin/env python3
"""Presentation evidence: extract checked source using Lean's declaration ranges.

This is a trusted viewer tool, not a new RDF definition or fidelity proof. The
stdin command reads compiler metadata without adding files to the formal library.
"""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess


RANGES_COMMAND = r'''
import RDF11
import Audit
import Lean
open Lean Elab Command
elab "#viewer_source_ranges" : command => do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (Name.mkSimple "RDF11").isPrefixOf m ||
          (Name.mkSimple "Audit").isPrefixOf m then
        if let some r ← findDeclarationRanges? n then
          rows := rows.push <| Json.mkObj [
            ("name", toJson n.toString),
            ("start", toJson r.range.pos),
            ("end", toJson r.range.endPos)]
  liftIO <| IO.println (Json.arr rows).compress
#viewer_source_ranges
'''


def source_excerpt(text, start, end):
    """Lean Position uses one-based lines and zero-based Unicode scalar columns."""
    lines = text.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))

    def offset(pos):
        line, col = pos["line"], pos["column"]
        if not 1 <= line <= len(lines) or not 0 <= col <= len(lines[line - 1].rstrip("\r\n")):
            raise ValueError(f"Invalid Lean source position: {pos}")
        return offsets[line - 1] + col

    a, b = offset(start), offset(end)
    if b <= a:
        raise ValueError("Empty or reversed Lean declaration range")
    return text[a:b]


def extract_sources(root, evidence, required):
    registry = json.loads((root / "catalogue/registry.json").read_text())
    files = {}
    for item in registry["files"]:
        raw = (root / item["path"]).read_bytes()
        if sha256(raw).hexdigest() != item["sha256"]:
            raise ValueError("Unverified Lean source: " + item["path"])
        files[item["path"]] = {"text": raw.decode("utf-8"), "sha256": item["sha256"]}

    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=root, env=env,
                         input=RANGES_COMMAND, text=True, capture_output=True, check=True)
    ranges = {r["name"]: r for r in json.loads(run.stdout)}
    declarations = {}
    for row in evidence["declarations"]:
        path = row["module"].replace(".", "/") + ".lean"
        if path not in files:
            continue
        entry = {k: row[k] for k in ("name", "module", "kind", "type", "dependencies")}
        entry["path"] = path
        if row["name"] in ranges:
            r = ranges[row["name"]]
            entry.update(start=r["start"], end=r["end"])
            entry["code"] = source_excerpt(files[path]["text"], r["start"], r["end"])
        declarations[row["name"]] = entry

    missing = sorted(n for n in required if not declarations.get(n, {}).get("code"))
    if missing:
        raise ValueError("Mapped Lean declarations lack source ranges: " + ", ".join(missing))

    revision = os.environ.get("GITHUB_SHA")
    if not revision:
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected a pinned Git revision for source links")
    return {"declarations": declarations, "files": files, "revision": revision,
            "source_url": f"https://github.com/danbri/dickory/blob/{revision}/labs/rdf11/cleanroom/"}
