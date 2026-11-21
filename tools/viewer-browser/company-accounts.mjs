// Browser integration for the SWAD-Europe archived source and Lean UI.
// Uses the *actual* generated 54-source HTML, no mock data, served from _site.
import {chromium, webkit} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import http from 'node:http';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

const repo=fileURLToPath(new URL('../../',import.meta.url));
const root=path.resolve(process.env.LINKED_SITE_ROOT||repo);
const types={'.html':'text/html','.js':'text/javascript','.css':'text/css','.json':'application/json','.wasm':'application/wasm'};
const server=http.createServer(async(req,res)=>{
  try{
    let p=path.resolve(root,'.'+decodeURIComponent(new URL(req.url,'http://local').pathname));
    if(!p.startsWith(root+path.sep)) throw Error('outside root');
    if((await fs.stat(p)).isDirectory())p=path.join(p,'index.html');
    res.setHeader('Content-Type',types[path.extname(p)]||'text/plain');
    res.end(await fs.readFile(p));
  }catch{res.writeHead(404);res.end('Not found');}
});
await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
const url='http://127.0.0.1:'+server.address().port+'/labs/company-accounts/';
const browser=await chromium.launch({headless:true});
try{
  const page=await browser.newPage({viewport:{width:1300,height:960}});
  const errors=[];
  page.on('pageerror',e=>errors.push(e.message));
  await page.goto(url);
  await page.waitForFunction(()=>document.querySelector('#leanCode')?.value.includes('namespace SWADAccounts'));
  assert.match(await page.locator('#archiveStatus').textContent(),/51 test-directory files \+ 3 linked documents/);
  assert.equal(await page.locator('#rule option').count(),11);
  assert.equal(await page.locator('#sourceFile option').count(),54);
  assert.equal(await page.locator('#sourceCount').textContent(),'54');

  // Verify all archival bytes, their exact sizes and SHA-256 in the actual
  // published page, complementing Python's separate build-time byte audit.
  const audit=await page.evaluate(async()=>{
    const archive=JSON.parse(document.getElementById('inlineArchive').textContent);
    let errors=[];
    for(const f of archive.files){
      let bytes;
      if(f.encoding==='base64') bytes=Uint8Array.from(atob(f.base64),c=>c.charCodeAt(0));
      else if(f.encoding==='latin-1') bytes=Uint8Array.from(f.text,c=>c.charCodeAt(0));
      else bytes=new TextEncoder().encode(f.text);
      if(bytes.byteLength!==f.bytes) errors.push(f.name+': size');
      const hash=[...new Uint8Array(await crypto.subtle.digest('SHA-256',bytes))]
        .map(x=>x.toString(16).padStart(2,'0')).join('');
      if(hash!==f.sha256) errors.push(f.name+': sha256');
    }
    return {count:archive.files.length,errors};
  });
  assert.deepEqual(audit,{count:54,errors:[]});
  await page.selectOption('#rule','8');
  assert.match(await page.locator('#ruleTitle').textContent(),/Acid-test ratio/);
  assert.match(await page.locator('#ruleFinding').textContent(),/includes stock|adds stock/);
  assert((await page.locator('#n3Code').textContent()).length>40);
  assert((await page.locator('#mathCode').textContent()).length>40);
  await page.selectOption('#sourceFile','tests/xml_company_facts_tests.zip');
  assert.match(await page.locator('#fileMeta').textContent(),/SHA-256 [a-f0-9]{64}/);
  assert.match(await page.locator('#sourceText').textContent(),/Binary ZIP/);
  await page.selectOption('#sourceFile','reports.xml');
  assert((await page.locator('#sourceText').textContent()).length>100);
  assert.deepEqual(errors,[]);
  // Isolation is needed for the shared real WASM compiler. Test the SW's
  // scoped registration, activation and COOP/COEP handshake after reload.
  await page.click('#enableIsolation');
  await page.waitForFunction(()=>crossOriginIsolated===true,{},{timeout:30000});
  assert(await page.evaluate(()=>typeof SharedArrayBuffer==='function'));
  assert.match(await page.locator('#isolationStatus').textContent(),/shared memory ready/);
  assert.deepEqual(errors,[]);
  assert.match(await page.locator('#proofStatus').textContent(),/native Lean proofs verified during the site build/);
  let mobileBrowser;
  try {
    mobileBrowser=await webkit.launch({headless:true});
    const mobileContext=await mobileBrowser.newContext({
      viewport:{width:390,height:844},
      isMobile:true,hasTouch:true,
      userAgent:'Mozilla/5.0 (iPhone; CPU iPhone OS 26_1 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/26.0 Mobile/15E148 Safari/604.1'
    });
    const mobilePage=await mobileContext.newPage(),mobileErrors=[],compilerFetches=[];
    mobilePage.on('pageerror',e=>mobileErrors.push(e.message));
    mobilePage.on('request',request=>{
      if(/lean\.wasm|toolchain-4\.33\.1|lean-lib\.tar\.gz/.test(request.url())) compilerFetches.push(request.url());
    });
    await mobilePage.goto(url);
    await mobilePage.waitForFunction(()=>document.querySelector('#proofStatus')?.textContent.includes('PUBLISHED CI PROOF VERIFIED'));
    assert.match(await mobilePage.locator('#proofMode').textContent(),/CI-native proof record/);
    assert.equal(await mobilePage.locator('#enableIsolation').isVisible(),false);
    assert.equal(await mobilePage.locator('#runProofs').textContent(),'Inspect published Lean proof record');
    await mobilePage.click('#runProofs');
    await mobilePage.waitForFunction(()=>document.querySelector('#proofStatus').textContent.includes('CI PROOFS: seven'));
    assert.match(await mobilePage.locator('#diagnostics').textContent(),/native Lean 4\.33\.1 CI check/);
    await mobilePage.click('#runNegative');
    await mobilePage.waitForFunction(()=>document.querySelector('#proofStatus').textContent.includes('CI NEGATIVE TEST'));
    assert.match(await mobilePage.locator('#diagnostics').textContent(),/REJECTED by native Lean CI/);
    const source=await mobilePage.locator('#leanCode').inputValue();
    await mobilePage.locator('#leanCode').fill(source+'\n-- unverified mutation');
    await mobilePage.click('#runProofs');
    assert.match(await mobilePage.locator('#proofStatus').textContent(),/EDITED SOURCE — NOT VERIFIED/);
    assert.match(await mobilePage.locator('#diagnostics').textContent(),/No Lean compilation or theorem check/);
    await mobilePage.click('#resetCode');
    assert.match(await mobilePage.locator('#proofStatus').textContent(),/CI PROOFS: seven/);
    assert.deepEqual(compilerFetches,[],'Mobile path must not download or initialise the failing WASM compiler');
    assert.deepEqual(mobileErrors,[]);
    assert(await mobilePage.evaluate(()=>document.documentElement.scrollWidth<=window.innerWidth));
  } finally {
    if(mobileBrowser) await mobileBrowser.close();
  }
  console.log(JSON.stringify({status:'pass',checks:['54 embedded historical sources byte-verifiable in Chromium',
    'all 11 archived rule comparisons render', 'original ZIP and reports.xml inspectable',
    'source editor loads actual Lean file', 'scoped isolation enables SharedArrayBuffer',
    'iPhone WebKit displays SHA-matched native proof evidence, rejects edits, and never loads WASM'],sourceCount:audit.count},null,2));
}finally{
  await browser.close();
  await new Promise(resolve=>server.close(resolve));
}
