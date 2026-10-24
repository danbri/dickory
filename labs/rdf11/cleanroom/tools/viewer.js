"use strict";
const data=JSON.parse(document.getElementById("data").textContent);
const docSelect=document.getElementById("document"), claimSelect=document.getElementById("claim");
const source=document.getElementById("source"), detail=document.getElementById("details");
const claims=new Map(data.claims.map(c=>[c.id,c]));
const frame=document.getElementById("rendered"), filter=document.getElementById("mapping-filter"), search=document.getElementById("search");
const passages=new Map(data.passages.map(p=>[p.id,p]));
let selectedClaim="", view="rendered", renderedDocument="";
function mappingStatus(c){return !c?.cleanroom_mapping?"unmapped":c.cleanroom_mapping.relation.startsWith("partial")||c.cleanroom_mapping.relation==="proved_illustration"?"partial":"mapped"}
function rangeStatus(refs){const states=refs.filter(id=>claims.has(id)).map(id=>mappingStatus(claims.get(id)));return !states.length?"":states.includes("unmapped")?"unmapped":states.includes("partial")?"partial":"mapped"}
const labels={mapped:"Mapped",partial:"Partial",unmapped:"Unmapped"};
const mapped=data.claims.filter(c=>c.cleanroom_mapping).length;
document.getElementById("coverage").textContent="Draft · "+mapped+" mappings, including partial, among "+data.claims.length+" preliminary claims · 0 expert approvals";
function matches(c){const q=search.value.trim().toLowerCase();return (filter.value==="all"||mappingStatus(c)===filter.value)&&(!q||[c.id,c.paraphrase,c.cleanroom_mapping?.symbol_linked_english||""].join(" ").toLowerCase().includes(q))}
function claimOptions(){
 claimSelect.replaceChildren(element("option","Choose a claim…"));claimSelect.firstChild.value="";
 const list=data.claims.filter(matches);
 for(const c of list){const o=element("option",c.id+" · "+mappingStatus(c));o.value=c.id;claimSelect.append(o)}
 claimSelect.value=list.some(c=>c.id===selectedClaim)?selectedClaim:"";
 document.getElementById("matches").textContent=list.length+" of "+data.claims.length+" claims"+(selectedClaim&&!list.some(c=>c.id===selectedClaim)?" · selected claim outside filter":"");
}
function badge(c){const b=element("span",labels[mappingStatus(c)]);b.className="badge "+mappingStatus(c);return b}
function dimmed(refs){return (filter.value!=="all"||search.value.trim())&&!refs.some(id=>claims.has(id)&&matches(claims.get(id)))}
function showRange(refs,title){detail.replaceChildren(element("h2",title));for(const id of refs)showClaim(id)}
function element(tag,text){const e=document.createElement(tag);if(text!==undefined)e.textContent=text;return e}
function leanDeclaration(name,ancestors=[]){
 const row=data.lean.declarations[name],box=element("section");box.className="lean-declaration";box.dataset.lean=name;
 box.append(element("h4",name));
 if(!row){box.append(element("p","No local source recorded for this declaration."));return box}
 const link=element("a",row.path+(row.start?":"+row.start.line:""));
 link.className="source-link";link.href=data.lean.source_url+row.path;
 if(row.start)link.href+="#L"+row.start.line+"-L"+(row.end.column===0?row.end.line-1:row.end.line);
 link.target="_blank";link.rel="noreferrer";box.append(link);
 const gloss=element("details");gloss.className="gloss";
 gloss.append(element("summary","ⓘ Plain-English explanation"));
 gloss.append(element("p",row.gloss.text),element("small",row.gloss.note));box.append(gloss);
 if(row.source_context_declaration){const note=element("p","Field shown in its containing structure: "+row.source_context_declaration);note.className="source-context-note";box.append(note)}
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
claimOptions();
function appendQuestions(a,id){
 for(const q of data.questions.filter(q=>q.claim_ids.includes(id))){
  const box=element("details");box.append(element("summary","Open source question: "+q.id));
  box.append(element("p",q.summary),element("p","Expert adjudication pending; not a declared erratum."));
  if(q.example?.instance && q.example?.generalized_graph)
   box.append(element("pre",q.example.instance+"  (true)\n"+q.example.generalized_graph+"  (false)"));
  if(q.review_question)box.append(element("p",q.review_question));
  if(q.implementation_policy)box.append(element("p",q.implementation_policy));
  for(const n of q.lean)box.append(leanDeclaration(n));
  a.append(box);
 }
}
function appendConnections(article,id){
 const links=data.connections[id];if(!links)return;
 const box=element("details");box.className="claim-connections";
 box.append(element("summary","Connected claims: "+links.uses.length+" used, "+links.used_by.length+" using this mapping"));
 box.append(element("p","These links follow checked declaration dependencies or shared bindings. They do not certify the English mappings or imply equivalence of claims."));
 for(const [kind,title] of [["uses","Uses declarations mapped in"],["used_by","Declarations used by"],["shared","Shares declaration bindings with"]]){
  if(!links[kind].length)continue;
  box.append(element("h3",title));const list=element("ul");
  for(const edge of links[kind]){
   const li=element("li"),link=element("a",edge.claim);link.href="#claim="+encodeURIComponent(edge.claim);
   link.onclick=e=>{e.preventDefault();selectClaim(edge.claim)};
   li.append(link,element("p",(edge.path||edge.declarations).join(" → ")));list.append(li);
  }box.append(list);
 }
 article.append(box);
}
function showClaim(id){
 const c=claims.get(id);
 if(!c){detail.append(element("p","Unresolved source range: no claim extraction has been assigned."));return}
 const a=element("article");a.append(element("h2",c.id),badge(c),element("p",c.paraphrase));
 a.append(element("p","Source status: "+c.source_status+" · "+c.category));
 const link=element("a","Publisher’s section");link.href=c.source_url;link.target="_blank";link.rel="noreferrer";a.append(link);
 const m=c.cleanroom_mapping;
 if(!m){
  a.append(element("p","Lean mapping not started."));
  if(c.formalization_note)a.append(element("p","Scope note: "+c.formalization_note));
  appendQuestions(a,id);detail.append(a);return;
 }
 a.append(element("h3","Explicit English / symbol bindings"),element("p",m.symbol_linked_english));
 appendConnections(a,id);
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
function decorateRendered(scroll=false){
 if(renderedDocument!==docSelect.value||!frame.contentDocument?.body)return;
 const doc=frame.contentDocument;
 for(const node of doc.querySelectorAll("[data-passages]")){
  const ps=node.dataset.passages.split(" ").map(id=>passages.get(id));
  const refs=[...new Set(ps.flatMap(p=>p.claims))];
  node.className="annotation "+rangeStatus(refs)+(selectedClaim&&refs.includes(selectedClaim)?" active":"")+(dimmed(refs)?" dim":"");
  node.tabIndex=0;node.setAttribute("role","button");
  node.title=refs.join(", ")+" · source "+ps.map(p=>"["+p.start+", "+p.end+")").join(", ");
  node.setAttribute("aria-label","Inspect "+refs.join(", "));
 }
 if(scroll&&view==="rendered")doc.querySelector(".active")?.scrollIntoView({block:"center"});
}
function loadRendered(d){
 if(renderedDocument===d.id){decorateRendered(true);return}
 renderedDocument=d.id;
 frame.onload=()=>{
  const doc=frame.contentDocument;
  doc.body.addEventListener("click",event=>{
   const node=event.target.closest("[data-passages]");
   if(node){event.preventDefault();const ps=node.dataset.passages.split(" ").map(id=>passages.get(id));
    showRange([...new Set(ps.flatMap(p=>p.claims))],"Annotated passage" );
   }else if(!event.target.closest("a[href]"))showRange([],"No located claim passage here — use Original HTML to inspect exact character ranges.");
  });
  doc.body.addEventListener("keydown",event=>{if((event.key==="Enter"||event.key===" ")&&event.target.matches("[data-passages]")){event.preventDefault();event.target.click()}});
  decorateRendered(true);
 };
 frame.srcdoc='<!doctype html><html lang="en"><head><meta charset="utf-8"><meta http-equiv="Content-Security-Policy" content="default-src \'none\'; style-src \'unsafe-inline\'"><style>body{font:16px/1.65 Georgia,serif;color:#24333e;padding:22px;margin:0;overflow-wrap:anywhere}h1,h2,h3,h4{font-family:system-ui;line-height:1.3}table{border-collapse:collapse;width:100%;font-size:14px}td,th{border:1px solid #a8b5bd;padding:8px}pre{white-space:pre-wrap;font-size:13px}a{color:#17647d}.annotation{cursor:pointer;border-left:4px solid transparent;padding-left:8px}.mapped{background:#e3f3ec;border-color:#2c8066}.partial{background:#fff3d3;border-color:#a4780b}.unmapped{background:#f5e7f1;border-color:#9c5c89}.active{outline:3px solid #165bb6;outline-offset:2px}.dim{opacity:.4}.annotation:hover,.annotation:focus{outline:2px solid #165bb6}blockquote{margin:12px}img{max-width:100%}</style></head><body>'+data.rendered[d.id]+'</body></html>';
}
function render(){
 const d=data.documents.find(x=>x.id===docSelect.value), chars=Array.from(data.sources[d.id]);
 document.getElementById("identity").textContent=d.sha256+" · "+d.scalars+" Unicode scalars · SHA-256";
 source.replaceChildren();let active=null;
 d.atoms.forEach((a,index)=>{
  const e=element("span",chars.slice(a.start,a.end).join(""));
  e.className="atom "+rangeStatus(a.refs)+(dimmed(a.refs)?" dim":"");
  e.dataset.atom=String(index);e.title="["+a.start+", "+a.end+") · "+a.refs.join(", ");
  if(selectedClaim&&a.refs.includes(selectedClaim)){e.classList.add("active");active=active||e}
  e.onclick=()=>showRange(a.refs,"Source range ["+a.start+", "+a.end+") · Unicode scalars · "+a.disposition);
  source.append(e);
 });
 if(active&&view==="raw")active.scrollIntoView({block:"center"});
 loadRendered(d);
}
function selectClaim(id,updateHash=true){
 if(!claims.has(id))return;
 selectedClaim=id;claimOptions();
 const passage=data.passages.find(p=>p.claims.includes(id));
 if(passage)docSelect.value=passage.source;
 render();detail.replaceChildren();showClaim(id);detail.scrollTop=0;
 if(updateHash)history.replaceState(null,"","#claim="+encodeURIComponent(id));
}
function setView(next){
 view=next;source.hidden=view!=="raw";frame.hidden=view!=="rendered";
 for(const name of ["rendered","raw"]){const tab=document.getElementById(name+"-tab");tab.setAttribute("aria-selected",String(view===name));tab.tabIndex=view===name?0:-1}
 if(view==="raw")source.querySelector(".active")?.scrollIntoView({block:"center"});else decorateRendered(true);
}
for(const name of ["rendered","raw"]){const tab=document.getElementById(name+"-tab");tab.onclick=()=>setView(name);tab.onkeydown=e=>{if(["ArrowLeft","ArrowRight","Home","End"].includes(e.key)){e.preventDefault();const next=e.key==="Home"?"rendered":e.key==="End"?"raw":view==="raw"?"rendered":"raw";setView(next);document.getElementById(next+"-tab").focus()}}}
filter.onchange=()=>{claimOptions();render()};search.oninput=()=>{claimOptions();render()};
docSelect.onchange=()=>{selectedClaim="";claimOptions();detail.replaceChildren(element("p","Click a passage to inspect its claims."));history.replaceState(null,"",location.pathname+location.search);render()};
claimSelect.onchange=()=>selectClaim(claimSelect.value);
function fromHash(){const id=new URLSearchParams(location.hash.slice(1)).get("claim");if(claims.has(id))selectClaim(id,false);else{selectedClaim="";claimOptions();render()}}
window.addEventListener("hashchange",fromHash);fromHash();
