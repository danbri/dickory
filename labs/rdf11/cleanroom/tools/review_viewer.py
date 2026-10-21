#!/usr/bin/env python3
"""Offline, raw-source review prototype. Never records or fabricates approvals."""
from pathlib import Path
import json
from source_catalogue import ROOT

catalogue = json.loads((ROOT / "catalogue/claims.json").read_text())
evidence = json.loads((ROOT / "artifacts/declarations.json").read_text())
questions = json.loads((ROOT / "catalogue/open-questions.json").read_text())["questions"]
needed = {b["lean"] for c in catalogue["claims"] if c["cleanroom_mapping"]
          for b in c["cleanroom_mapping"]["bindings"]}
needed |= {n for q in questions for n in q["lean"]}
types = {r["name"]: r["type"] for r in evidence["declarations"] if r["name"] in needed}
payload = {"documents": catalogue["documents"], "claims": catalogue["claims"],
           "passages": catalogue["passages"], "types": types, "questions": questions,
           "sources": {d["id"]: (ROOT / d["path"]).read_bytes().decode("utf-8")
                       for d in catalogue["documents"]}}
template = r"""<!doctype html>
<html lang="en"><meta charset="utf-8">
<title>RDF 1.1 → Lean · draft source review</title>
<style>
*{box-sizing:border-box}body{margin:0;font:15px/1.5 system-ui;color:#172c39;background:#f6f7f4}
header{padding:18px 24px;background:#163c4c;color:white}h1{font-size:22px;margin:0}
header p{margin:6px 0}nav{padding:12px 24px;background:white;display:flex;gap:14px;flex-wrap:wrap}
select{max-width:90vw;padding:7px}main{display:grid;grid-template-columns:55% 45%;height:76vh}
#source{white-space:pre-wrap;overflow:auto;padding:20px;margin:0;font:12px/1.55 monospace;overflow-wrap:anywhere}
#details{overflow:auto;padding:20px;background:white;border-left:1px solid #ccd5d6}
.atom{cursor:pointer}.atom:hover{outline:1px solid #29758c}.associated{background:#fff0ba}
.active{background:#a7e3db}article{border-bottom:1px solid #ccd5d6;padding-bottom:16px;margin-bottom:20px}
h2{font-size:17px;margin:0 0 8px}h3{font-size:14px}code,pre{overflow-wrap:anywhere}
details pre{white-space:pre-wrap;font-size:12px}#identity{font:11px monospace;overflow-wrap:anywhere}
.status{font-size:13px;color:#765319}a{color:#17647d}@media(max-width:800px){main{grid-template-columns:1fr;height:auto}#source{height:45vh}}
</style>
<header><h1>RDF 1.1 → Lean: source and claim review</h1>
<p>Draft · 34 initial mappings among 195 preliminary claims · expert approvals pending</p>
<p>This prototype shows the original HTML as raw source. Highlighting means association, not complete extraction or accepted formalization.</p>
<div id="identity"></div></header>
<nav><label>Source <select id="document"></select></label>
<label>Claim <select id="claim"><option value="">Choose a claim…</option></select></label></nav>
<main><pre id="source" aria-label="Original source characters"></pre><section id="details">
Click any source range to inspect its claim associations, or select a claim.</section></main>
<script id="data" type="application/json">__PAYLOAD__</script>
<script>
"use strict";
const data=JSON.parse(document.getElementById("data").textContent);
const docSelect=document.getElementById("document"), claimSelect=document.getElementById("claim");
const source=document.getElementById("source"), detail=document.getElementById("details");
const claims=new Map(data.claims.map(c=>[c.id,c]));
function element(tag,text){const e=document.createElement(tag);if(text!==undefined)e.textContent=text;return e}
for(const d of data.documents){const o=element("option",d.id==="mt"?"RDF 1.1 Semantics":"RDF 1.1 Concepts");o.value=d.id;docSelect.append(o)}
for(const c of data.claims){const o=element("option",c.id+(c.cleanroom_mapping?" · mapped/partial":" · unmapped"));o.value=c.id;claimSelect.append(o)}
function showClaim(id){
 const c=claims.get(id);
 if(!c){detail.append(element("p","Unresolved source range: no claim extraction has been assigned."));return}
 const a=element("article");a.append(element("h2",c.id),element("p",c.paraphrase));
 a.append(element("p","Source status: "+c.source_status+" · "+c.category));
 const link=element("a","Publisher’s section");link.href=c.source_url;link.target="_blank";link.rel="noreferrer";a.append(link);
 for(const q of data.questions.filter(q=>q.claim_ids.includes(id))){
  const box=element("details");box.append(element("summary","Open source question: "+q.id));
  box.append(element("p",q.summary),element("p","Expert adjudication pending; not a declared erratum."));
  box.append(element("pre",q.example.instance+"  (true)\n"+q.example.generalized_graph+"  (false)"));
  for(const n of q.lean){const d=element("details");d.append(element("summary",n),element("pre",data.types[n]));box.append(d)}
  a.append(box);
 }
 const m=c.cleanroom_mapping;
 if(!m){a.append(element("p","Lean mapping not started."));detail.append(a);return}
 a.append(element("h3","Explicit English / symbol bindings"),element("p",m.symbol_linked_english));
 a.append(element("p","Mapping relation: "+m.relation));
 if(m.limitations)a.append(element("p","Boundary: "+m.limitations));
 const status=element("p","Extraction review: pending. Formalization review: pending. Package refinement: absent.");
 status.className="status";a.append(status);
 for(const b of m.bindings){
  const d=element("details");d.append(element("summary",b.lean));
  d.append(element("pre",data.types[b.lean]||"Missing declaration"));a.append(d);
 }
 detail.append(a);
}
function render(selectedClaim){
 const d=data.documents.find(x=>x.id===docSelect.value), chars=Array.from(data.sources[d.id]);
 document.getElementById("identity").textContent=d.sha256+" · "+d.scalars+" Unicode scalars · SHA-256";
 source.replaceChildren();let active=null;
 d.atoms.forEach((a,index)=>{
  const e=element("span",chars.slice(a.start,a.end).join(""));
  e.className="atom"+(a.disposition!=="unresolved"?" associated":"");
  e.dataset.atom=String(index);e.title="["+a.start+", "+a.end+") · "+a.refs.join(", ");
  if(selectedClaim&&a.refs.includes(selectedClaim)){e.classList.add("active");active=active||e}
  e.onclick=()=>{
   detail.replaceChildren(element("h2","Source range ["+a.start+", "+a.end+")"),
                          element("p","Unicode scalars · "+a.disposition));
   for(const id of a.refs)showClaim(id);
  };
  source.append(e);
 });
 if(active)active.scrollIntoView({block:"center"});
}
docSelect.onchange=()=>render("");
claimSelect.onchange=()=>{
 const id=claimSelect.value;if(!id)return;
 const passage=data.passages.find(p=>p.claims.includes(id));
 if(passage)docSelect.value=passage.source;
 render(id);detail.replaceChildren();showClaim(id);
};
render("");
</script></html>"""
encoded = json.dumps(payload, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
out = template.replace("__PAYLOAD__", encoded)
(ROOT / "artifacts/source-review.html").write_bytes(out.encode("utf-8"))
print("Generated artifacts/source-review.html (offline raw-source prototype)")

