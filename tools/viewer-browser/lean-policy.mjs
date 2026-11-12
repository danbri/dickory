import {chromium} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {runNativePolicyCase} from '../../labs/linked-assurance/tools/headless/policy-runner.mjs';
const browser=await chromium.launch({headless:true});
try {
 const page=await browser.newPage();page.setDefaultTimeout(240000);
 await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/');
 await page.waitForFunction(()=>document.querySelector('#leanEditor').value.includes('def policy'));
 await page.fill('#budget','60000');
 const source=await page.locator('#leanEditor').inputValue();
 console.log('Checking and running the policy with one button, including first-use setup…');
 await page.click('#checkPolicy');
 await page.waitForFunction(()=>document.querySelector('#decision').textContent!=='Not run' || /did not accept|could not finish|timed out/.test(document.querySelector('#policyRunSummary').textContent),{},{timeout:360000});
 assert.equal(await page.locator('#decision').textContent(),'permit',await page.locator('#compilerState').textContent());
 await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
 const compiled=JSON.parse(await page.locator('#manifest').textContent()).compile;
 assert.equal(compiled.contractChecked,true,JSON.stringify(compiled));
 assert.equal(await page.locator('#leanEditor').inputValue(),source,'First-use reload preserves policy source');
 await page.locator('.advancedTools,.operations').evaluateAll(xs=>xs.forEach(x=>x.open=true));
 const checks=[];
 let lastRecord=null;
 async function run(name,decision,attacker){
  console.log('Running '+name);const start=Date.now();
  await page.click('#checkPolicy');await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
  assert.equal(await page.locator('#decision').textContent(),decision);
  assert.match(await page.locator('#policyRunSummary').textContent(),new RegExp('Result: '+decision));
  assert.match(await page.locator('#compilerState').textContent(),/Finished:/);
  if(attacker)assert.equal(await page.locator('#attackOutcome').textContent(),attacker);
  const record=JSON.parse(await page.locator('#manifest').textContent());
  lastRecord=record;
  assert.equal(record.policyExecution.sourceSha256,compiled.sourceSha256);
  assert.equal(record.policyExecution.executed,true);
  checks.push({name,decision,milliseconds:Date.now()-start,fixtureSha256:record.policyExecution.fixtureSha256});
 }
 await run('baseline','permit');
 const nodeBaseline=await runNativePolicyCase({scenario:'vocabulary',scope:'union',regime:'RDFS'});
 assert.equal(nodeBaseline.policy.decision,lastRecord.policyExecution.decision);
 assert.equal(nodeBaseline.policy.attacker,lastRecord.policyExecution.attacker);
 assert.equal(nodeBaseline.fixtureSha256,lastRecord.identities.fixtureSha256);
 assert.equal(nodeBaseline.rdfObservation.context.selectedGraphSha256,lastRecord.rdf.context.selectedGraphSha256);
 checks.push({name:'native Node vs Chromium baseline',decision:nodeBaseline.policy.decision,fixtureSha256:nodeBaseline.fixtureSha256,
   node:nodeBaseline.attestation.nativeLean,browser:compiled.compilerVersion});
 await page.fill('#clock','2026-11-13T12:00:00Z');await run('expired credential','deny');
 await page.fill('#clock','2026-11-11T12:00:00Z');await page.fill('#signature','verified');await run('signature spoof','deny');
 await page.selectOption('#regime','OWL-DL');await run('unsupported regime','defer');
 await page.selectOption('#regime','RDFS');await page.selectOption('#scenarioChoice','alert');await run('false alarm','protectiveShutdown','achieved');
 const nodeAlert=await runNativePolicyCase({scenario:'alert',scope:'union',regime:'RDFS'});
 assert.equal(nodeAlert.policy.decision,lastRecord.policyExecution.decision);
 assert.equal(nodeAlert.policy.attacker,lastRecord.policyExecution.attacker);
 assert.equal(nodeAlert.fixtureSha256,lastRecord.identities.fixtureSha256);
 checks.push({name:'native Node vs Chromium false-alarm attack',decision:nodeAlert.policy.decision,
   attacker:nodeAlert.policy.attacker,fixtureSha256:nodeAlert.fixtureSha256});
 console.log('Checking rejected proof mutation…');
 await page.fill('#leanEditor',source.replace('else if ready e s then .permit else .deny','else .permit'));
 await page.click('#checkPolicy');await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
 const rejected=JSON.parse(await page.locator('#compilerReport').textContent());assert.equal(rejected.contractChecked,false);
 assert.match(await page.locator('#policyRunSummary').textContent(),/did not accept this proof/);
 assert.match(await page.locator('#compilerState').textContent(),/does not by itself establish that the claim is false/);
 await page.click('#runPolicy');assert.match(await page.locator('#status').textContent(),/Compile the current policy/);
 const report={status:'pass',browser:browser.version(),compiler:compiled.compilerVersion,compiled,checks,rejected};
 await fs.writeFile('../../labs/linked-assurance/artifacts/policy-browser-checks.json',JSON.stringify(report,null,2)+'\n');
 console.log(JSON.stringify({status:report.status,compiler:report.compiler,checks}));
} finally {await browser.close();}
