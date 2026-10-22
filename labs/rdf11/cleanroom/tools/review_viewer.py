#!/usr/bin/env python3
"""Offline annotated specification and Lean review prototype. Never records or fabricates approvals."""
from pathlib import Path
import json
from source_catalogue import ROOT
from lean_sources import extract_sources
from rendered_source import reading_copy
from viewer_glosses import attach_glosses

catalogue = json.loads((ROOT / "catalogue/claims.json").read_text())
evidence = json.loads((ROOT / "artifacts/declarations.json").read_text())
questions = json.loads((ROOT / "catalogue/open-questions.json").read_text())["questions"]
needed = {b["lean"] for c in catalogue["claims"] if c["cleanroom_mapping"]
          for b in c["cleanroom_mapping"]["bindings"]}
needed |= {n for q in questions for n in q["lean"]}
lean = extract_sources(ROOT, evidence, needed)
attach_glosses(lean, catalogue, ROOT)
payload = {"documents": catalogue["documents"], "claims": catalogue["claims"],
           "passages": catalogue["passages"], "questions": questions,
           "lean": lean,
           "sources": {d["id"]: (ROOT / d["path"]).read_bytes().decode("utf-8")
                       for d in catalogue["documents"]}}
payload["rendered"] = {d["id"]: reading_copy(payload["sources"][d["id"]], [p for p in catalogue["passages"] if p["source"] == d["id"]]) for d in catalogue["documents"]}
template = r"""<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>RDF 1.1 → Lean · draft source review</title>
<style>__CSS__</style>
<header><h1>RDF 1.1 → Lean: source and claim review</h1>
<p id="coverage"></p><p>Read the annotated document or its exact source; inspect claims, checked Lean and expandable English explanations.</p>
<div id="identity"></div></header>
<nav><label>Source <select id="document"></select></label>
<label>Mapping status <select id="mapping-filter"><option value="all">All claims</option><option value="mapped">Mapped</option><option value="partial">Partial</option><option value="unmapped">Unmapped</option></select></label>
<label>Search claims <input id="search" type="search" placeholder="e.g. instance, blank, IEXT"></label>
<label class="claim-picker">Claim <select id="claim"><option value="">Choose a claim…</option></select></label><span id="matches" role="status"></span></nav>
<div class="legend"><span class="badge mapped">Mapped</span><span class="badge partial">Partial</span><span class="badge unmapped">Unmapped</span> · blue outline: selected claim · plain background: no passage association
<p>Colours describe associated claim mappings, not coverage of every statement in a passage. “Mapped” is not expert approval. All reviews are pending.</p></div>
<main><section id="source-pane"><div class="tabs" role="tablist" aria-label="Specification display">
<button id="rendered-tab" role="tab" aria-selected="true" aria-controls="rendered">Rendered document</button>
<button id="raw-tab" role="tab" aria-selected="false" aria-controls="source" tabindex="-1">Original HTML</button></div>
<iframe id="rendered" title="Annotated specification reading view" sandbox="allow-same-origin" referrerpolicy="no-referrer" role="tabpanel"></iframe>
<pre id="source" hidden role="tabpanel" aria-label="Original source characters"></pre></section><section id="details">
Select a claim or click a highlighted passage. The rendered reading copy adapts styling and disables external resources; the original HTML tab preserves every source character.</section></main>
<script id="data" type="application/json">__PAYLOAD__</script>
<script>
__JS__
</script></html>"""
encoded = json.dumps(payload, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
out = template.replace("__CSS__", (ROOT / "tools/viewer.css").read_text()).replace("__JS__", (ROOT / "tools/viewer.js").read_text()).replace("__PAYLOAD__", encoded)
(ROOT / "artifacts/source-review.html").write_bytes(out.encode("utf-8"))
print("Generated artifacts/source-review.html (offline annotated reading view)")

