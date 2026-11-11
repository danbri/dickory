import {chromium} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
const browser=await chromium.launch({headless:true});
try {
 const page=await browser.newPage();page.setDefaultTimeout(240000);
 await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/');
 if(!await page.evaluate(()=>crossOriginIsolated)){
  await page.click('#isolate');await page.waitForFunction(()=>crossOriginIsolated);
 }
 await page.waitForFunction(()=>document.querySelector('#leanEditor').value.includes('def policy'));
 await page.fill('#budget','60000');
 const source=await page.locator('#leanEditor').inputValue();
 console.log('Compiling support and policy with real browser Lean…');
 await page.click('#compile');await page.waitForFunction(()=>!document.querySelector('#compile').disabled);
 const compileText=await page.locator('#compilerReport').textContent();
 assert(compileText.startsWith('{'),compileText);
 const compiled=JSON.parse(compileText);
 assert.equal(compiled.contractChecked,true,JSON.stringify(compiled));
 const checks=[];
 async function run(name,decision,attacker){
  console.log('Running '+name);const start=Date.now();
  await page.click('#runPolicy');await page.waitForFunction(()=>document.querySelector('#decision').textContent!=='Not run');
  assert.equal(await page.locator('#decision').textContent(),decision);
  assert.match(await page.locator('#policyRunSummary').textContent(),new RegExp('Result: '+decision));
  assert.match(await page.locator('#compilerState').textContent(),/Finished:/);
  if(attacker)assert.equal(await page.locator('#attackOutcome').textContent(),attacker);
  const record=JSON.parse(await page.locator('#manifest').textContent());
  assert.equal(record.policyExecution.sourceSha256,compiled.sourceSha256);
  assert.equal(record.policyExecution.executed,true);
  checks.push({name,decision,milliseconds:Date.now()-start,fixtureSha256:record.policyExecution.fixtureSha256});
 }
 await run('baseline','permit');
 await page.fill('#clock','2026-11-13T12:00:00Z');await run('expired credential','deny');
 await page.fill('#clock','2026-11-11T12:00:00Z');await page.fill('#signature','verified');await run('signature spoof','deny');
 await page.selectOption('#regime','OWL-DL');await run('unsupported regime','defer');
 await page.selectOption('#regime','RDFS');await page.click('[data-id="alert"]');await run('false alarm','protectiveShutdown','achieved');
 console.log('Checking rejected proof mutation…');
 await page.fill('#leanEditor',source.replace('else if ready e s then .permit else .deny','else .permit'));
 await page.click('#compile');await page.waitForFunction(()=>!document.querySelector('#compile').disabled);
 const rejected=JSON.parse(await page.locator('#compilerReport').textContent());assert.equal(rejected.contractChecked,false);
 await page.click('#runPolicy');assert.match(await page.locator('#status').textContent(),/Compile the current policy/);
 const report={status:'pass',browser:browser.version(),compiler:compiled.compilerVersion,compiled,checks,rejected};
 await fs.writeFile('../../labs/linked-assurance/artifacts/policy-browser-checks.json',JSON.stringify(report,null,2)+'\n');
 console.log(JSON.stringify({status:report.status,compiler:report.compiler,checks}));
} finally {await browser.close();}
