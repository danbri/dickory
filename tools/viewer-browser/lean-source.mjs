import {chromium} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
const cases=[
 {name:'theorem and computation',execution:'compiled',environment:'core',source:'module\npublic import Init\n@[expose] public section\ndef next (n : Nat) := n + 1\ntheorem next_zero : next 0 = 1 := by rfl\n#eval next 41\n'},
 {name:'false theorem',execution:'compile_rejected',environment:'core',source:'import Init\nexample : (1 : Nat) = 2 := by rfl\n'},
 {name:'policy support import',execution:'compiled',environment:'workbench',source:'module\npublic import Workbench\nopen LinkedAssurance\nexample (e : Evidence) (s : OperationalState) (h : ready e s = true) : permitRequirements e s := ready_sound e s h\n'}
];
const reports=[];
try{
 for(const item of cases){
  const browser=await chromium.launch({headless:true,args:['--enable-features=WebMCP']});
  try{
   const page=await browser.newPage();page.setDefaultTimeout(180000);
   await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/?headless=1');
   assert(await page.evaluate(()=>crossOriginIsolated));
   await page.waitForFunction(()=>!!window.__linkedAssuranceHeadless);
   const record=await page.evaluate(async input=>{
    const {createBrowserDispatcher}=await import('./headless-webmcp.js');
    const {registerWebMCP,invokeNativeWebMCP}=await import('./profile/webmcp.js');
    const dispatcher=await createBrowserDispatcher({enabledTools:['linked_assurance_compile_lean']});
    const registration=await registerWebMCP(dispatcher);
    if(!registration.registered)throw Error('Native WebMCP is required; no direct fallback.');
    try{
      return await invokeNativeWebMCP('linked_assurance_compile_lean',{source:input.source,environment:input.environment,budgetMs:120000,includeArtifacts:true});
    }finally{registration.dispose();}
   },item);
   assert.equal(record.status,'completed',JSON.stringify(record));
   const result=record.result;
   assert.equal(result.execution,item.execution,JSON.stringify(result));
   assert.equal(result.sourceSha256,createHash('sha256').update(item.source).digest('hex'));
   assert.equal(result.compiler.host,'browser-wasm');
   assert.equal(result.proof.policyContractChecked,false);
   if(item.execution==='compiled'){
    const file=result.artifacts.find(f=>f.name==='Script.olean');assert(file);
    const bytes=Buffer.from(file.base64,'base64');assert.equal(bytes.length,file.bytes);
    assert.equal(createHash('sha256').update(bytes).digest('hex'),file.sha256);
    assert.equal(bytes.subarray(0,4).toString(),'olea');
   }else{assert.deepEqual(result.artifacts,[]);assert(result.diagnostics.some(d=>d.severity==='error'));}
   const {artifacts,...summary}=result;
   reports.push({name:item.name,nativeWebMCP:true,browser:browser.version(),...summary,artifacts:artifacts.map(({base64,...meta})=>meta)});
   console.log(item.name+': '+result.execution);
  }finally{await browser.close();}
 }
}finally{
 const out=new URL('../../labs/linked-assurance/artifacts/source-browser-checks.json',import.meta.url);
 await fs.mkdir(new URL('.',out),{recursive:true});
 await fs.writeFile(out,JSON.stringify({status:reports.length===cases.length?'pass':'incomplete',reports},null,2)+'\n');
}
