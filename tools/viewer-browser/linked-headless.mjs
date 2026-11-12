#!/usr/bin/env node
// Headless Chromium CLI: Factoidal executes inside a real browser Web Worker.
// Node here drives Playwright, not the RDF calculation.
import {chromium} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import http from 'node:http';
import path from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {runNodeCase,parseArgs} from '../../labs/linked-assurance/tools/headless/node-runner.mjs';
import {makeCase,parity,listCases} from '../../labs/linked-assurance/headless-contract.js';

const repo=path.resolve(fileURLToPath(new URL('../../',import.meta.url)));
const root=path.resolve(process.env.LINKED_SITE_ROOT||repo);
const types={'.html':'text/html; charset=utf-8','.js':'text/javascript; charset=utf-8',
  '.mjs':'text/javascript; charset=utf-8','.json':'application/json',
  '.wasm':'application/wasm','.css':'text/css'};
async function serve(){
  const server=http.createServer(async(req,res)=>{
    try{
      const uri=new URL(req.url,'http://localhost');
      let file=path.resolve(root,'.'+decodeURIComponent(uri.pathname));
      if(!file.startsWith(root+path.sep))throw Error('Path outside document root');
      if((await fs.stat(file)).isDirectory())file=path.join(file,'index.html');
      res.setHeader('Content-Type',types[path.extname(file)]||'application/octet-stream');
      res.end(await fs.readFile(file));
    }catch{res.statusCode=404;res.end('Not found');}
  });
  await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  return {server,url:'http://127.0.0.1:'+server.address().port+'/labs/linked-assurance/?headless=1'};
}
async function routeFactoidal(context){
  await context.route('https://cdn.jsdelivr.net/npm/@factoidal/core@0.35.1/**',async route=>{
    try{
      const tail=new URL(route.request().url()).pathname.split('/@factoidal/core@0.35.1/')[1];
      if(!tail)throw Error('Invalid package path');
      const base=path.resolve(repo,'labs/linked-assurance/node_modules/@factoidal/core');
      const file=path.resolve(base,tail);
      if(!file.startsWith(base+path.sep))throw Error('Path outside pinned package');
      await route.fulfill({status:200,body:await fs.readFile(file),
        headers:{'Content-Type':types[path.extname(file)]||'application/octet-stream',
          'Access-Control-Allow-Origin':'*','Cross-Origin-Resource-Policy':'cross-origin'}});
    }catch{await route.abort('failed');}
  });
}
export async function runBrowserCase(input={}){
  const {identity}=makeCase(input);
  const {server,url}=await serve();
  const browser=await chromium.launch({headless:true,args:['--enable-features=WebMCP']});
  try{
    const context=await browser.newContext();
    await routeFactoidal(context);
    const page=await context.newPage();
    await page.goto(url,{waitUntil:'domcontentloaded'});
    await page.waitForFunction(()=>!!window.__linkedAssuranceHeadless,{timeout:15000});
    // Native WebMCP invocation if available. Fallback uses the identical
    // handler but is explicitly marked as non-WebMCP (no false advertising).
    const fromPage=await page.evaluate(async args=>{
      const m=document.modelContext;
      if(m?.getTools&&m?.executeTool){
        const tools=await m.getTools();
        const target=tools.find(t=>t.name==='linked_assurance_evaluate');
        if(target){
          const raw=await m.executeTool(target,args,{signal:new AbortController().signal});
          return {mode:'native-WebMCP',
            outcome:typeof raw==='string'?JSON.parse(raw):raw,
            nativeRegistered:true};
        }
      }
      return {mode:'direct-browser-handler',
        outcome:await window.__linkedAssuranceHeadless.run(args),
        nativeRegistered:false};
    },input);
    const session=await context.newCDPSession(page);
    const cdp=await session.send('Browser.getVersion');
    const identityProbe=await page.evaluate(()=>({
      windowType:typeof window,documentType:typeof document,
      userAgent:navigator.userAgent,webAssembly:typeof WebAssembly,
      workerAPI:typeof Worker,locationOrigin:location.origin
    }));
    assert.equal(identityProbe.windowType,'object');
    assert.equal(identityProbe.documentType,'object');
    assert.match(cdp.product,/Chrome|Chromium|HeadlessChrome/);
    assert.equal(fromPage.outcome.attestation.runtime,'chromium-page-worker');
    return {
      case:identity,observation:fromPage.outcome.observation,
      attestation:{
        runtime:'chromium-page-worker',launcher:'playwright.chromium',
        invocation:fromPage.mode,nativeWebMCP:fromPage.nativeRegistered,
        browserProduct:cdp.product,protocolVersion:cdp.protocolVersion,
        ...identityProbe
      }
    };
  }finally{
    await browser.close();
    await new Promise(resolve=>server.close(resolve));
  }
}
export async function compareCase(input={}){
  const [node,browser]=await Promise.all([runNodeCase(input),runBrowserCase(input)]);
  const comparison=parity(node,browser);
  const distinctRuntimes=node.attestation.runtime==='node'&&
    node.attestation.documentType==='undefined'&&
    browser.attestation.runtime==='chromium-page-worker'&&
    browser.attestation.documentType==='object'&&
    /Chrome|Chromium/.test(browser.attestation.browserProduct);
  return {case:node.case,distinctRuntimes,equivalence:comparison,
    runtimeEvidence:{node:node.attestation,browser:browser.attestation}};
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
  try{
    const args=process.argv.slice(2);
    const mode=args.includes('--compare')?'compare':args.includes('--list')?'list':'browser';
    const opts=parseArgs(args.filter(x=>!['--compare','--list'].includes(x)));
    const result=mode==='list'?{cases:listCases()}:
      mode==='compare'?await compareCase(opts):await runBrowserCase(opts);
    process.stdout.write(JSON.stringify(result)+'\n');
    if(mode==='compare'&&(!result.distinctRuntimes||!result.equivalence.equivalent))process.exitCode=1;
  }catch(e){process.stderr.write(String(e.stack||e)+'\n');process.exitCode=1;}
}
