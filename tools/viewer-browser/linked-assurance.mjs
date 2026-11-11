// Browser integration with the actual pinned Factoidal WASM, served from npm ci.
// No compiler-success or RDF-answer stubs are used.
import {chromium} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import http from 'node:http';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const repo=fileURLToPath(new URL('../../',import.meta.url));
const root=path.resolve(process.env.LINKED_SITE_ROOT||repo);
const types={'.html':'text/html','.js':'text/javascript','.mjs':'text/javascript','.css':'text/css','.json':'application/json','.wasm':'application/wasm'};
const server=http.createServer(async(req,res)=>{
 try{
  let p=path.resolve(root,'.'+decodeURIComponent(new URL(req.url,'http://local').pathname));
  if(!p.startsWith(root+path.sep))throw Error('outside root');
  if((await fs.stat(p)).isDirectory())p=path.join(p,'index.html');
  res.setHeader('Content-Type',types[path.extname(p)]||'text/plain');res.end(await fs.readFile(p));
 }catch{res.writeHead(404);res.end('Not found');}
});
await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
const base=`http://127.0.0.1:${server.address().port}`;
const browser=await chromium.launch({headless:true});
const out=path.join(repo,'labs/linked-assurance/artifacts');await fs.mkdir(out,{recursive:true});
try{
 const context=await browser.newContext({viewport:{width:1440,height:1050}});
 await context.route('https://cdn.jsdelivr.net/npm/@factoidal/core@0.35.1/**',async route=>{
  const rel=new URL(route.request().url()).pathname.split('/@factoidal/core@0.35.1/')[1];
  const p=path.resolve(repo,'labs/linked-assurance/node_modules/@factoidal/core',rel);
  assert(p.startsWith(path.resolve(repo,'labs/linked-assurance/node_modules/@factoidal/core')+path.sep));
  await route.fulfill({body:await fs.readFile(p),headers:{'Content-Type':types[path.extname(p)]||'application/octet-stream','Access-Control-Allow-Origin':'*','Cross-Origin-Resource-Policy':'cross-origin'}});
 });
 const page=await context.newPage(),errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto(base+'/labs/linked-assurance/');
 await page.waitForFunction(()=>document.querySelector('#leanEditor').value.includes('def policy'));
 assert.match(await page.locator('#compilerState').textContent(),/First use/);
 await page.click('#compile');await page.waitForFunction(()=>!document.querySelector('#compile').disabled);
 assert.match(await page.locator('#compilerReport').textContent(),/cross-origin isolation/);
 const evaluate=async()=>{
  await page.click('#evaluate');await page.waitForFunction(()=>document.querySelector('#execution').textContent!=='Running');
  return JSON.parse(await page.locator('#rdfReport').textContent());
 };
 await page.fill('#budget','60000');
 let r=await evaluate();assert.equal(r.execution,'completed');assert(r.explanation.entailed);
 assert.equal(r.context.runtimeVersion,'0.35.1');assert.match(await page.locator('#decision').textContent(),/Not run/);
 await page.selectOption('#scope','data');r=await evaluate();assert.equal(r.claims[0].answer,false);
 await page.selectOption('#scope','default');r=await evaluate();assert.equal(r.dataset.selectedQuads,0);
 await page.selectOption('#scope','union');
 for(const id of ['offer','event','artifact','alert']){
  await page.click(`[data-id="${id}"]`);r=await evaluate();assert.equal(r.execution,'completed');assert.equal(r.claims[0].answer,true);
 }
 await page.selectOption('#variant','invalid');r=await evaluate();assert.equal(r.execution,'parserError');assert.deepEqual(r.claims,[]);
 await page.click('[data-id="vocabulary"]');await page.selectOption('#regime','OWL-DL');r=await evaluate();assert.equal(r.execution,'unsupported');
 await page.selectOption('#regime','RDFS');await page.fill('#budget','1');r=await evaluate();assert.equal(r.execution,'timeout');assert.deepEqual(r.claims,[]);
 assert.equal(await page.locator('#knowledge').textContent(),'Not established');
 await page.fill('#budget','60000');r=await evaluate();
 await page.click('#prepare');await page.waitForFunction(()=>document.querySelector('#fixture').textContent.includes('def adaptedEvidence'));
 assert.match(await page.locator('#credentialState').textContent(),/signature verified/);
 assert.equal(JSON.parse(await page.locator('#manifest').textContent()).policyExecution.executed,false);
 await page.locator('#rdfEditor').fill((await page.locator('#rdfEditor').inputValue())+'\n# edit');
 assert.equal(await page.locator('#knowledge').textContent(),'Not evaluated');
 await page.click('#runPolicy');assert.match(await page.locator('#status').textContent(),/Compile the current policy/);
 await page.screenshot({path:path.join(out,'workbench-desktop.png'),fullPage:true});
 await page.setViewportSize({width:390,height:844});
 assert(await page.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth));
 await page.screenshot({path:path.join(out,'workbench-mobile.png'),fullPage:true});
 // Test the actual navigation-header shim on a host that supplies no COOP/COEP.
 await page.click('#isolate');await page.waitForFunction(()=>crossOriginIsolated,{},{timeout:30000});
 assert(await page.evaluate(()=>typeof SharedArrayBuffer==='function'));
 assert.deepEqual(errors,[]);
 const report={status:'pass',runtime:'@factoidal/core 0.35.1 actual WASM; local npm bytes',
  checks:['5 examples execute in worker','explicit graph scope','parser rejection','unsupported regime','hard timeout','stale result clearing','no policy result without compile','compiler unavailable on plain origin','service-worker isolation after reload','desktop and mobile layout'],
  wasmCompiler:'Not executed in this fast suite; linked-probe.mjs is the separate compiler integration check.'};
 await fs.writeFile(path.join(out,'browser-checks.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report,null,2));
}finally{await browser.close();await new Promise(resolve=>server.close(resolve));}
