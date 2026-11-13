#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
// Strict native WebMCP by default. Direct dispatch is a labelled diagnostic mode.
import {chromium} from 'playwright';
import fs from 'node:fs/promises';
import http from 'node:http';
import path from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {runNodeCase,parseArgs} from '../../labs/linked-assurance/tools/headless/node-runner.mjs';
import {parity} from '../../labs/linked-assurance/headless-contract.js';
const repo=fileURLToPath(new URL('../../',import.meta.url));
const types={'.html':'text/html','.js':'text/javascript','.mjs':'text/javascript','.json':'application/json','.css':'text/css','.wasm':'application/wasm'};
async function serve(){
 const root=path.resolve(process.env.LINKED_SITE_ROOT||repo);
 const server=http.createServer(async(req,res)=>{
  try{
   let file=path.resolve(root,'.'+decodeURIComponent(new URL(req.url,'http://local').pathname));
   if(!file.startsWith(root+path.sep))throw Error('outside root');
   if((await fs.stat(file)).isDirectory())file=path.join(file,'index.html');
   res.setHeader('Cross-Origin-Opener-Policy','same-origin');res.setHeader('Cross-Origin-Embedder-Policy','require-corp');
   res.setHeader('Content-Type',types[path.extname(file)]||'application/octet-stream');res.end(await fs.readFile(file));
  }catch{res.writeHead(404);res.end();}
 });
 await new Promise((r,j)=>{server.once('error',j);server.listen(0,'127.0.0.1',r);});
 return {server,url:'http://127.0.0.1:'+server.address().port+'/labs/linked-assurance/?headless=1'};
}
export async function runBrowserTool(name,args={},options={}){
 const {server,url}=await serve();let browser;
 try{
  browser=await chromium.launch({headless:true,args:['--enable-features=WebMCP']});
  const context=await browser.newContext();
  await context.route('https://cdn.jsdelivr.net/npm/@factoidal/core@0.35.1/**',async route=>{
   const base=path.resolve(repo,'labs/linked-assurance/node_modules/@factoidal/core');
   const suffix=new URL(route.request().url()).pathname.split('/@factoidal/core@0.35.1/')[1];
   const file=path.resolve(base,suffix||'');
   if(!file.startsWith(base+path.sep)){await route.abort();return;}
   await route.fulfill({body:await fs.readFile(file),headers:{'Content-Type':types[path.extname(file)]||'application/octet-stream','Access-Control-Allow-Origin':'*','Cross-Origin-Resource-Policy':'cross-origin'}});
  });
  const page=await context.newPage();page.setDefaultTimeout(240000);
  await page.goto(url,{waitUntil:'domcontentloaded'});
  await page.waitForFunction(()=>!!window.__linkedAssuranceHeadless);
  const capability=await page.evaluate(async()=>{
   const h=window.__linkedAssuranceHeadless,ready=await h.ready;
   return {registered:ready.registration.registered,names:ready.registration.names||[],
    host:'browser',windowType:typeof window,documentType:typeof document,workerAPI:typeof Worker,userAgent:navigator.userAgent};
  });
  const cdp=await context.newCDPSession(page),version=await cdp.send('Browser.getVersion');
  if(!/Chrome|Chromium/.test(version.product)||capability.documentType!=='object')throw Error('Missing real Chromium identity');
  if(!capability.registered&&!options.direct)throw Error('native_webmcp_unavailable: '+version.product+'; direct fallback is forbidden');
  const result=await page.evaluate(async({name,args,direct})=>direct?
   window.__linkedAssuranceHeadless.invokeDirect(name,args):window.__linkedAssuranceHeadless.invokeNative(name,args),{name,args,direct:options.direct===true});
  return {...result,runtime:{...result.runtime,invocation:options.direct?'direct-browser-handler':'native-WebMCP',browserProduct:version.product,protocolVersion:version.protocolVersion,...capability}};
 }finally{
  await browser?.close();server.closeAllConnections();await new Promise(r=>server.close(r));
 }
}
export async function runBrowserCase(input={},options={}){
 const envelope=await runBrowserTool('linked_assurance_evaluate',input,options);
 if(envelope.status!=='completed')throw Error(JSON.stringify(envelope));
 return {...envelope.result,attestation:{...envelope.result.attestation,...envelope.runtime}};
}
export async function compareCase(input={}){
 const node=await runNodeCase(input),browser=await runBrowserCase(input);
 return {case:node.case,distinctRuntimes:node.attestation.documentType==='undefined'&&browser.attestation.documentType==='object',
  equivalence:parity(node,browser),runtimeEvidence:{node:node.attestation,browser:browser.attestation}};
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 try{
  const argv=process.argv.slice(2);let result;
  if(argv.includes('--tool')){
   const get=k=>{const i=argv.indexOf(k);return i<0?undefined:argv[i+1];};
   const input=get('--input')?JSON.parse(await fs.readFile(get('--input'),'utf8')):{};
   result=await runBrowserTool(get('--tool'),input,{direct:argv.includes('--direct')});
  }else{
   const args=parseArgs(argv.filter(x=>!['--compare','--direct'].includes(x)));
   result=argv.includes('--compare')?await compareCase(args):await runBrowserCase(args,{direct:argv.includes('--direct')});
   if(result.equivalence&&!result.equivalence.equivalent)process.exitCode=1;
  }
  process.stdout.write(JSON.stringify(result)+'\n');if(result.status&&result.status!=='completed')process.exitCode=1;
 }catch(e){process.stderr.write(String(e)+'\n');process.exitCode=/native_webmcp_unavailable/.test(String(e))?3:1;}
}
