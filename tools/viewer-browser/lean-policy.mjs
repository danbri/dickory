import {chromium,webkit} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
const engine=process.env.LEAN_BROWSER||'chromium';
if(!['chromium','webkit'].includes(engine))throw Error('Unsupported LEAN_BROWSER: '+engine);
const browser=await ({chromium,webkit}[engine]).launch({headless:true});
let statusTimer;
try {
 const page=await browser.newPage();page.setDefaultTimeout(240000);
 page.on('requestfailed',request=>console.log('Request failed:',request.url(),request.failure()?.errorText));
 page.on('console',message=>{if(message.type()==='error')console.log('Browser error:',message.text().slice(0,1200));});
 let lastStatus='';statusTimer=setInterval(async()=>{try{const status=await page.locator('#compilerState').textContent({timeout:1000});if(status!==lastStatus){lastStatus=status;console.log('Compiler: '+status);}}catch{}},15000);
 await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/');
 await page.waitForFunction(()=>document.querySelector('#leanEditor').value.includes('def policy'));
 await page.fill('#budget','60000');
 const source=await page.locator('#leanEditor').inputValue();
 console.log('Checking and running the policy with one button, including first-use setup…');
 await page.click('#checkPolicy');
 await page.waitForFunction(()=>document.querySelector('#decision').textContent!=='Not run' || /did not accept|could not finish|could not complete|timed out/.test(document.querySelector('#policyRunSummary').textContent),{},{timeout:360000});
 assert.equal(await page.locator('#decision').textContent(),'permit',(await page.locator('#compilerState').textContent())+'\n'+(await page.locator('#compilerReport').textContent())+'\n'+(await page.locator('#compilerBrowserDetails').textContent()));
 await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
 const compiled=JSON.parse(await page.locator('#manifest').textContent()).compile;
 assert.equal(compiled.contractChecked,true,JSON.stringify(compiled));
 assert.equal(compiled.verificationLocation,'site build');
 assert.match(await page.locator('#decisionNote').textContent(),/during the site build/);
 assert.equal(await page.locator('#leanEditor').inputValue(),source,'First-use reload preserves policy source');
 await page.locator('.advancedTools,.operations').evaluateAll(xs=>xs.forEach(x=>x.open=true));
 const checks=[];
 async function run(name,decision,attacker){
  console.log('Running '+name);const start=Date.now();
  await page.click('#checkPolicy');await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
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
 await page.selectOption('#regime','RDFS');await page.selectOption('#scenarioChoice','alert');await run('false alarm','protectiveShutdown','achieved');
 let editedPolicy=null;
 if(engine==='chromium'){
  console.log('Checking a valid policy edit locally…');
  await page.fill('#leanEditor',source+'\n-- Local compilation regression.\n');await page.click('#checkPolicy');
  await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
  editedPolicy=JSON.parse(await page.locator('#manifest').textContent()).compile;
  assert.equal(editedPolicy.contractChecked,true);assert.equal(editedPolicy.verificationLocation,'browser');
  assert.equal(await page.locator('#decision').textContent(),'protectiveShutdown');
 }
 console.log('Checking rejected proof mutation…');
 await page.fill('#leanEditor',source.replace('else if ready e s then .permit else .deny','else .permit'));
 await page.click('#checkPolicy');await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
 const raw=await page.locator('#compilerReport').textContent();let rejected;
 if(engine==='webkit'&&!raw.startsWith('{')){
  assert.match(raw,/Maximum call stack size exceeded/);
  assert.match(await page.locator('#policyRunSummary').textContent(),/could not complete/);
  assert.match(await page.locator('#compilerState').textContent(),/No proof result was produced/);
  rejected={contractChecked:false,runtimeLimit:true,diagnostics:raw};
 }else{
  rejected=JSON.parse(raw);assert.equal(rejected.contractChecked,false);
  assert.match(await page.locator('#policyRunSummary').textContent(),/did not accept this proof/);
  assert.match(await page.locator('#compilerState').textContent(),/does not by itself establish that the claim is false/);
 }
 assert.equal(await page.locator('#decision').textContent(),'Not run');
 await page.click('#runPolicy');assert.match(await page.locator('#status').textContent(),/Compile the current policy/);
 console.log('Restoring and running the published policy after the failed edit…');
 await page.click('#resetPolicy');await page.click('#checkPolicy');
 await page.waitForFunction(()=>!document.querySelector('#checkPolicy').disabled);
 assert.equal(await page.locator('#decision').textContent(),'protectiveShutdown');
 assert.equal(JSON.parse(await page.locator('#manifest').textContent()).compile.verificationLocation,'site build');
 const report={status:'pass',browser:browser.version(),engine,compiler:compiled.compilerVersion,compiled,checks,editedPolicy,rejected,recoveredPublishedPolicy:true};
 await fs.writeFile('../../labs/linked-assurance/artifacts/'+(engine==='chromium'?'policy-browser-checks.json':'policy-webkit-checks.json'),JSON.stringify(report,null,2)+'\n');
 console.log(JSON.stringify({status:report.status,compiler:report.compiler,checks}));
} finally {clearInterval(statusTimer);await browser.close();}
