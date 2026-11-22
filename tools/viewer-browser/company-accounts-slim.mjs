// Execute the REAL, same-origin Lean 4.33.1 WASM worker in WebKit's
// mobile-like engine, not a mocked Lean parser or prechecked certificate.
import {webkit} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import http from 'node:http';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

const repo=path.resolve(fileURLToPath(new URL('../../',import.meta.url)));
const types={'.html':'text/html','.js':'text/javascript','.mjs':'text/javascript',
  '.json':'application/json','.css':'text/css','.wasm':'application/wasm'};
const server=http.createServer(async(req,res)=>{
  try{
    let p=path.resolve(repo,'.'+decodeURIComponent(new URL(req.url,'http://127.0.0.1').pathname));
    if(!p.startsWith(repo+path.sep)) throw Error('outside test root');
    res.setHeader('Content-Type',types[path.extname(p)]||'application/octet-stream');
    res.end(await fs.readFile(p));
  }catch{res.writeHead(404);res.end('Not found');}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin='http://127.0.0.1:'+server.address().port;
const browser=await webkit.launch({headless:true});
try{
  const page=await browser.newPage({
    viewport:{width:390,height:844},isMobile:true,hasTouch:true,
    userAgent:'Mozilla/5.0 (iPhone; CPU iPhone OS 26_1 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/26.0 Mobile/15E148 Safari/604.1'
  });
  const errors=[];
  page.on('pageerror',e=>errors.push(String(e)));
  await page.goto(origin+'/labs/company-accounts/tools/inline-smoke.html');
  await page.evaluate(async()=>{
    const reg=await navigator.serviceWorker.register('../coi-sw.js',
      {scope:'../',updateViaCache:'none'});
    await reg.update();
    const worker=reg.installing||reg.waiting||reg.active;
    if(!worker)throw Error('No COOP/COEP shim');
    if(worker.state!=='activated')await new Promise(resolve=>{
      worker.addEventListener('statechange',()=>{
        if(worker.state==='activated')resolve();
      });
    });
    if(navigator.serviceWorker.controller!==worker)
      await new Promise(resolve=>navigator.serviceWorker.addEventListener('controllerchange',resolve,{once:true}));
  });
  await page.reload();
  await page.waitForFunction(()=>crossOriginIsolated&&typeof SharedArrayBuffer==='function',
    {},{timeout:30000});
  const result=await page.evaluate(async()=>{
    const {checkMobileLean}=await import('../inline-lean-host.js');
    const source=await (await fetch('../lean/Accounts.lean')).text();
    const simple=await checkMobileLean([
      'import Init',
      'theorem inline_probe : (2 + 2 : Nat) = 4 := by rfl',
      '#print axioms inline_probe',
      '#eval Lean.versionString'
    ].join('\n'));
    const positive=await checkMobileLean(source+'\n#eval Lean.versionString');
    const negative=await checkMobileLean(source+
      '\nexample : SWADAccounts.sameExactValue (SWADAccounts.acidTest SWADAccounts.fixture) '+
      '(SWADAccounts.archivedN3AcidTest SWADAccounts.fixture) = true := by decide\n');
    return {
      version:positive.compilerVersion,
      simple:{accepted:simple.accepted,runtimeFault:simple.runtimeFault,
        diagnostics:simple.diagnostics.slice(0,4000),exitCode:simple.exitCode},
      positive:{accepted:positive.accepted,runtimeFault:positive.runtimeFault,
        diagnostics:positive.diagnostics.slice(0,4000),exitCode:positive.exitCode},
      negative:{accepted:negative.accepted,runtimeFault:negative.runtimeFault,
        diagnostics:negative.diagnostics.slice(0,4000),exitCode:negative.exitCode},
    };
  },{timeout:300000});
  console.log(JSON.stringify(result,null,2));
  assert.equal(result.simple.exitCode,0,
    'Minimal Lean proof must pass before assessing the full model');
  assert.equal(result.simple.runtimeFault,false);
  assert.equal(result.simple.accepted,true);
  assert.equal(result.positive.exitCode,0);
  assert.equal(result.positive.runtimeFault,false);
  assert.equal(result.positive.accepted,true);
  assert.match(result.positive.diagnostics,/4\.33\.1/);
  assert.equal(result.negative.runtimeFault,false);
  assert.equal(result.negative.accepted,false);
  assert.notEqual(result.negative.exitCode,0);
  assert.match(result.negative.diagnostics,/error|failed|not provable|tactic/i);
  assert.deepEqual(errors,[]);
  console.log('Verified real full Accounts.lean + false theorem in isolated WebKit worker');
}finally{
  await browser.close();
  await new Promise(resolve=>server.close(resolve));
}
