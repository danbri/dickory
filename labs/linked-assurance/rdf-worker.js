// A short-lived, killable Factoidal evaluation worker.
// The UI applies a hard wall-clock deadline by terminating this worker.
// Errors and timeouts are never silently turned into "false" RDF results.
let engine;
async function getEngine(){
 if(!engine)engine=await import("https://danbri.github.io/factoidal/npm/factoidal/browser.js");
 return engine;
}
self.onmessage=async ({data:m})=>{
 if(m.kind!=="evaluate")return;
 const started=performance.now();
 try{
  const mod=await getEngine();
  const opts={output:"json",...(m.regime==="RDFS"?{entail:"RDFS"}:{}),...(m.format?{format:m.format}:{})};
  const outcomes=[];
  for(const item of m.queries){
    const r=await mod.query(m.dataset,item.text,opts);
    if(item.kind==="ask"){
      if(typeof r?.boolean!=="boolean")throw Error("Unrecognised SPARQL ASK format");
      outcomes.push({name:item.name,kind:item.kind,boolean:r.boolean});
    }else{
      if(!Array.isArray(r?.results?.bindings))throw Error("Unrecognised SPARQL SELECT format");
      outcomes.push({name:item.name,kind:item.kind,bindings:r.results.bindings,vars:r.head?.vars||[]});
    }
  }
  postMessage({kind:"completed",requestId:m.requestId,outcomes,ms:performance.now()-started});
 }catch(e){
  postMessage({kind:"fault",requestId:m.requestId,error:String(e?.message||e),ms:performance.now()-started});
 }
};