// Exercise the actual hello page, optionally sampling new macOS WebContent
// processes. RSS is a desktop measurement, not an estimate of an iPhone limit.
import {chromium,webkit} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {execFileSync} from 'node:child_process';
const engine=process.env.LEAN_BROWSER||'webkit',upstream=process.argv.includes('--upstream-glue');
const site=process.env.LINKED_SITE_URL||'http://127.0.0.1:8082';
const processes=()=>process.platform==='darwin'?execFileSync('ps',['-axo','pid=,rss=,comm='],{encoding:'utf8'}).split('\n').flatMap(line=>{
  const m=line.match(/^\s*(\d+)\s+(\d+)\s+(.+)$/);return m&&/WebKit.WebContent/.test(m[3])?[{pid:Number(m[1]),rssKiB:Number(m[2])}]:[];
}):[];
const before=new Set(processes().map(p=>p.pid));let peakRssKiB=0;
const sampler=setInterval(()=>{const rss=processes().filter(p=>!before.has(p.pid)).reduce((n,p)=>n+p.rssKiB,0);peakRssKiB=Math.max(peakRssKiB,rss);},500);
const browser=await ({chromium,webkit}[engine]).launch({headless:true});
try{
  const page=await browser.newPage();page.setDefaultTimeout(240000);
  page.on('pageerror',e=>console.log('Page error:',e.message));
  page.on('console',m=>{if(m.type()==='error')console.log('Browser:',m.text().slice(0,300));});
  if(upstream)await page.route('**/compiler-assets.json',async route=>{const manifest=await (await route.fetch()).json();delete manifest['lean.js'].browser;await route.fulfill({json:manifest});});
  await page.goto(site+'/labs/linked-assurance/tools/hello/');
  if(!await page.evaluate(()=>crossOriginIsolated)){
    await page.locator('#compilerSetupTools').evaluate(x=>x.open=true);await page.click('#setupLean');await page.waitForFunction(()=>crossOriginIsolated);
  }
  const started=Date.now();await page.click('#run');
  const timer=setInterval(async()=>{try{console.log(await page.locator('#status').textContent(),'peak WebContent RSS MiB:',Math.round(peakRssKiB/1024));}catch{}},10000);
  try{await page.waitForFunction(()=>!document.querySelector('#run').disabled);}finally{clearInterval(timer);}
  const status=await page.locator('#status').textContent(),cases=JSON.parse(await page.locator('#result').textContent());
  assert.match(status,/All checks passed/,JSON.stringify(cases)+'\n'+status);
  const report={status:'pass',engine,browser:browser.version(),glue:upstream?'upstream':'compact',milliseconds:Date.now()-started,peakWebContentRssMiB:peakRssKiB/1024,cases};
  if(process.argv.includes('--tasks')){
    console.log('Checking execution on the preloaded task worker…');
    const task=await page.evaluate(async()=>{const {checkLean}=await import('../../lean-host.js');return checkLean('#eval (Task.spawn fun _ => (6 * 7 : Nat)).get');});
    assert(task.accepted,JSON.stringify(task));assert.match(task.stdout,/"data":"42"/);
    assert(task.memory.taskWorkers>0);report.taskCheck=task;
    report.peakWithTaskRssMiB=peakRssKiB/1024;
  }
  await fs.writeFile(new URL('../../labs/linked-assurance/artifacts/startup-'+engine+(upstream?'-upstream':'')+'.json',import.meta.url),JSON.stringify(report,null,2)+'\n');
  console.log(JSON.stringify({...report,cases:cases.map(({name,accepted})=>({name,accepted}))}));
}finally{clearInterval(sampler);await browser.close();}
