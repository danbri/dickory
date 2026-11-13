// Exercise the actual Pages header shim, including replacement of its old policy.
import {chromium,webkit} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import http from 'node:http';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const repo=fileURLToPath(new URL('../../',import.meta.url));
const root=path.resolve(process.env.LINKED_SITE_ROOT||repo);
const types={'.html':'text/html','.js':'text/javascript','.css':'text/css','.json':'application/json'};
let legacy=false;
const server=http.createServer(async(req,res)=>{
  try{
    if(req.url.startsWith('/labs/linked-assurance/cached-worker.js')){
      res.setHeader('Content-Type','text/javascript');res.setHeader('Cache-Control','no-cache');
      res.setHeader('ETag','"worker-v1"');res.setHeader('Last-Modified','Wed, 11 Nov 2026 00:00:00 GMT');
      if(req.headers['if-none-match']||req.headers['if-modified-since']){res.writeHead(304);res.end();}
      else res.end('onmessage=()=>postMessage(42);');
      return;
    }
    if(req.url.startsWith('/labs/linked-assurance/empty-response')){
      res.writeHead(Number(new URL(req.url,'http://local').searchParams.get('status')));res.end();return;
    }
    let file=path.resolve(root,'.'+decodeURIComponent(new URL(req.url,'http://local').pathname));
    if(!file.startsWith(root+path.sep))throw Error('outside root');
    if((await fs.stat(file)).isDirectory())file=path.join(file,'index.html');
    let body=await fs.readFile(file);
    if(legacy&&file.endsWith('/coi-sw.js'))body=Buffer.from(body.toString().replace("headers.set('Cross-Origin-Embedder-Policy','require-corp')","headers.set('Cross-Origin-Embedder-Policy','credentialless')"));
    res.setHeader('Content-Type',types[path.extname(file)]||'text/plain');
    res.setHeader('Cache-Control','no-store');res.end(body);
  }catch{res.writeHead(404);res.end('Not found');}
});
await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
const url=`http://127.0.0.1:${server.address().port}/labs/linked-assurance/#learn`;
const checks=[];
try{
  for(const [name,engine] of Object.entries({chromium,webkit})){
    const browser=await engine.launch({headless:true});
    try{
      for(const upgrade of [false,true]){
        legacy=upgrade;
        const context=await browser.newContext(),page=await context.newPage();
        await page.goto(url);
        await page.waitForFunction(()=>document.querySelector('#tutorialEditor').value.length>0);
        if(upgrade){
          await page.evaluate(async()=>{
            await navigator.serviceWorker.register('./coi-sw.js',{scope:'./'});
            await navigator.serviceWorker.ready;
          });
          await page.waitForFunction(()=>!!navigator.serviceWorker.controller);
          await page.reload();
        }
        const before=await page.evaluate(()=>({isolated:crossOriginIsolated,shared:typeof SharedArrayBuffer==='function'}));
        if(upgrade&&name==='webkit')assert.equal(before.isolated,false,'The old credentialless shim reproduces the WebKit failure');
        legacy=false;
        await Promise.all([
          page.waitForNavigation(),
          page.evaluate(()=>{import('./compiler-banner.js').then(m=>m.enableIsolation());})
        ]);
        await page.waitForFunction(()=>crossOriginIsolated&&typeof SharedArrayBuffer==='function');
        const after=await page.evaluate(async()=>{
          const response=await fetch('./coi-sw.js');
          const shared=new SharedArrayBuffer(4);
          const workerUrl=URL.createObjectURL(new Blob(['onmessage=e=>{new Int32Array(e.data)[0]=42;postMessage({isolated:crossOriginIsolated,shared:typeof SharedArrayBuffer==="function"})}'],{type:'text/javascript'}));
          const worker=new Worker(workerUrl);
          const result=await new Promise((resolve,reject)=>{
            const timer=setTimeout(()=>{worker.terminate();reject(Error('Shared-memory worker timed out'));},10000);
            worker.onmessage=e=>{clearTimeout(timer);resolve(e.data);};
            worker.onerror=e=>{clearTimeout(timer);reject(Error(e.message));};worker.postMessage(shared);
          });
          worker.terminate();URL.revokeObjectURL(workerUrl);
          return {coep:response.headers.get('Cross-Origin-Embedder-Policy'),worker:result,value:new Int32Array(shared)[0]};
        });
        assert.equal(after.coep,'require-corp');assert.equal(after.worker.isolated,true);assert.equal(after.worker.shared,true);assert.equal(after.value,42);
        const cachedWorkers=await page.evaluate(async()=>{
          const results=[];
          for(let i=0;i<2;i++){
            const worker=new Worker('./cached-worker.js');
            try{results.push(await new Promise((resolve,reject)=>{
              const timer=setTimeout(()=>reject(Error('Cached worker timed out')),10000);
              worker.onmessage=e=>{clearTimeout(timer);resolve(e.data);};worker.onerror=e=>{clearTimeout(timer);reject(Error(e.message||'Cached worker failed'));};worker.postMessage(null);
            }));}finally{worker.terminate();}
          }
          for(const status of [204,205,304]){
            const response=await fetch('./empty-response?status='+status);
            if(response.status!==status||await response.text()!=='')throw Error('Bodyless response failed: '+status);
          }
          return results;
        });
        assert.deepEqual(cachedWorkers,[42,42]);
        checks.push({browser:name,version:browser.version(),scenario:upgrade?'replace old helper':'first setup',before,after,cachedWorkers,bodylessStatuses:[204,205,304]});
        console.log(name+': '+(upgrade?'old helper updated':'first setup')+'; page and worker share memory');
        await context.close();
      }
    }finally{await browser.close();}
  }
  await fs.writeFile(new URL('../../labs/linked-assurance/artifacts/isolation-browser-checks.json',import.meta.url),JSON.stringify({status:'pass',checks},null,2)+'\n');
}finally{await new Promise(resolve=>server.close(resolve));}
