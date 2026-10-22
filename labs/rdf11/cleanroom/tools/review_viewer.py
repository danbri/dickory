#!/usr/bin/env python3
"""Offline, raw-source review prototype. Never records or fabricates approvals."""
from pathlib import Path
import json
from source_catalogue import ROOT
from lean_sources import extract_sources

catalogue = json.loads((ROOT / "catalogue/claims.json").read_text())
evidence = json.loads((ROOT / "artifacts/declarations.json").read_text())
questions = json.loads((ROOT / "catalogue/open-questions.json").read_text())["questions"]
needed = {b["lean"] for c in catalogue["claims"] if c["cleanroom_mapping"]
          for b in c["cleanroom_mapping"]["bindings"]}
needed |= {n for q in questions for n in q["lean"]}
lean = extract_sources(ROOT, evidence, needed)
payload = {"documents": catalogue["documents"], "claims": catalogue["claims"],
           "passages": catalogue["passages"], "questions": questions,
           "lean": lean,
           "sources": {d["id"]: (ROOT / d["path"]).read_bytes().decode("utf-8")
                       for d in catalogue["documents"]}}
template = r"""<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>RDF 1.1 → Lean · draft source review</title>
<style>
*{box-sizing:border-box}body{margin:0;font:15px/1.5 system-ui;color:#172c39;background:#f6f7f4}
header{padding:18px 24px;background:#163c4c;color:white}h1{font-size:22px;margin:0}
header p{margin:6px 0}nav{padding:12px 24px;background:white;display:flex;gap:14px;flex-wrap:wrap}
nav label{display:flex;flex-direction:column;gap:4px;min-width:0;max-width:100%}nav label:last-child{flex:1 1 25rem}
select{max-width:100%;min-width:0;padding:7px}main{display:grid;grid-template-columns:minmax(0,35%) minmax(0,65%);height:76vh}
#source{white-space:pre-wrap;overflow:auto;padding:20px;margin:0;font:12px/1.55 monospace;overflow-wrap:anywhere}
#details{overflow:auto;padding:20px;background:white;border-left:1px solid #ccd5d6}
.atom{cursor:pointer}.atom:hover{outline:1px solid #29758c}.associated{background:#fff0ba}
.active{background:#a7e3db}article{border-bottom:1px solid #ccd5d6;padding-bottom:16px;margin-bottom:20px}
h2{font-size:17px;margin:0 0 8px}h3{font-size:14px}code,pre{overflow-wrap:anywhere}
details pre{white-space:pre-wrap;font-size:12px}#identity{font:11px monospace;overflow-wrap:anywhere}
.lean-declaration{margin:18px 0;padding:16px;border:1px solid #ccd5d6;border-radius:5px;background:#f8fafb;min-width:0}
.lean-declaration h4{margin:0 0 8px;font-size:15px;overflow-wrap:anywhere}
.lean-code{white-space:pre-wrap;overflow-wrap:anywhere;font:14px/1.65 ui-monospace,SFMono-Regular,Consolas,monospace;background:#edf3f6;padding:14px;border-left:3px solid #29758c}
.source-link,.context-note{font-size:13px}.lean-declaration details{margin-top:10px}summary{cursor:pointer}
.lean-declaration details .lean-declaration{background:white}.mapping-note{margin:6px 0;color:#35586b}
.status{font-size:13px;color:#765319}a{color:#17647d}@media(max-width:800px){main{grid-template-columns:1fr;height:auto}#source{height:30vh}#details{border-left:0;padding:14px}}
</style>
<header><h1>RDF 1.1 → Lean: source and claim review</h1>
<p>Draft · 34 initial mappings among 195 preliminary claims · expert approvals pending</p>
<p>Select a claim to read its English mapping and actual Lean definitions or proofs. The left pane shows the archived specification as raw HTML.</p>
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
function leanDeclaration(name,ancestors=[]){
 const row=data.lean.declarations[name],box=element("section");box.className="lean-declaration";box.dataset.lean=name;
 box.append(element("h4",name));
 if(!row){box.append(element("p","No local source recorded for this declaration."));return box}
 const link=element("a",row.path+(row.start?":"+row.start.line:""));
 link.className="source-link";link.href=data.lean.source_url+row.path;
 if(row.start)link.href+="#L"+row.start.line+"-L"+(row.end.column===0?row.end.line-1:row.end.line);
 link.target="_blank";link.rel="noreferrer";box.append(link);
 if(row.code){const code=element("pre");code.className="lean-code";code.append(element("code",row.code));box.append(code)}
 else box.append(element("p","Compiler-generated declaration without a separate source range; open its defining file above."));
 const type=element("details");type.append(element("summary","Elaborated type"),element("pre",row.type));box.append(type);
 const context=element("details");context.append(element("summary","Full source context: imports, namespaces and surrounding definitions"));
 context.append(element("p","Source SHA-256: "+data.lean.files[row.path].sha256));
 context.append(element("pre",data.lean.files[row.path].text));box.append(context);
 const local=row.dependencies.filter(n=>n!==name&&data.lean.declarations[n]);
 if(local.length){
  const deps=element("details");deps.className="dependencies";
  deps.append(element("summary","Uses "+local.length+" local declaration"+(local.length===1?"":"s")+" — inspect their Lean"));
  let loaded=false;deps.addEventListener("toggle",()=>{
   if(!deps.open||loaded)return;loaded=true;
   for(const n of local){
    if(ancestors.includes(n))deps.append(element("p",n+" (already shown above)"));
    else deps.append(leanDeclaration(n,[...ancestors,name]));
   }
  });box.append(deps);
 }
 const external=row.dependencies.filter(n=>!data.lean.declarations[n]);
 if(external.length){const deps=element("details");deps.append(element("summary","Standard-library / foundation dependencies ("+external.length+")"),element("pre",external.join("\n")));box.append(deps)}
 return box;
}
for(const d of data.documents){const o=element("option",d.id==="mt"?"RDF 1.1 Semantics":"RDF 1.1 Concepts");o.value=d.id;docSelect.append(o)}
for(const c of data.claims){const o=element("option",c.id+(c.cleanroom_mapping?" · mapped/partial":" · unmapped"));o.value=c.id;claimSelect.append(o)}
function appendQuestions(a,id){
 for(const q of data.questions.filter(q=>q.claim_ids.includes(id))){
  const box=element("details");box.append(element("summary","Open source question: "+q.id));
  box.append(element("p",q.summary),element("p","Expert adjudication pending; not a declared erratum."));
  box.append(element("pre",q.example.instance+"  (true)\n"+q.example.generalized_graph+"  (false)"));
  for(const n of q.lean)box.append(leanDeclaration(n));
  a.append(box);
 }
}
function showClaim(id){
 const c=claims.get(id);
 if(!c){detail.append(element("p","Unresolved source range: no claim extraction has been assigned."));return}
 const a=element("article");a.append(element("h2",c.id),element("p",c.paraphrase));
 a.append(element("p","Source status: "+c.source_status+" · "+c.category));
 const link=element("a","Publisher’s section");link.href=c.source_url;link.target="_blank";link.rel="noreferrer";a.append(link);
 const m=c.cleanroom_mapping;
 if(!m){a.append(element("p","Lean mapping not started."));appendQuestions(a,id);detail.append(a);return}
 a.append(element("h3","Explicit English / symbol bindings"),element("p",m.symbol_linked_english));
 a.append(element("h3","Actual Lean 4"));
 const note=element("p","These are excerpts from the checked source, including definition bodies and proofs. Open a file or its full context for imports and namespaces.");
 note.className="context-note";a.append(note);
 for(const b of m.bindings){
  const binding=element("p",b.symbol+" ↔ "+b.lean);binding.className="mapping-note";a.append(binding,leanDeclaration(b.lean));
 }
 a.append(element("p","Mapping relation: "+m.relation));
 if(m.limitations)a.append(element("p","Boundary: "+m.limitations));
 const status=element("p","Extraction review: pending. Formalization review: pending. Package refinement: absent.");
 status.className="status";a.append(status);
 appendQuestions(a,id);
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
function selectClaim(id,updateHash=true){
 if(!claims.has(id))return;
 claimSelect.value=id;
 const passage=data.passages.find(p=>p.claims.includes(id));
 if(passage)docSelect.value=passage.source;
 render(id);detail.replaceChildren();showClaim(id);
 detail.scrollTop=0;
 if(updateHash)history.replaceState(null,"","#claim="+encodeURIComponent(id));
}
docSelect.onchange=()=>{claimSelect.value="";detail.replaceChildren(element("p","Click any source range to inspect its claims."));history.replaceState(null,"",location.pathname+location.search);render("")};
claimSelect.onchange=()=>selectClaim(claimSelect.value);
function fromHash(){const id=new URLSearchParams(location.hash.slice(1)).get("claim");if(claims.has(id))selectClaim(id,false);else render("")}
window.addEventListener("hashchange",fromHash);fromHash();
</script></html>"""
encoded = json.dumps(payload, ensure_ascii=False).replace("<", "\\u003c").replace("&", "\\u0026")
out = template.replace("__PAYLOAD__", encoded)
(ROOT / "artifacts/source-review.html").write_bytes(out.encode("utf-8"))
print("Generated artifacts/source-review.html (offline raw-source prototype)")

