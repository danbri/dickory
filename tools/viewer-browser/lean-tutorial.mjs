import {chromium} from 'playwright';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {lessons} from '../../labs/linked-assurance/tutorial-lessons.js';
const browser=await chromium.launch({headless:true});
try{
  const page=await browser.newPage();page.setDefaultTimeout(240000);
  const errors=[];page.on('pageerror',e=>errors.push(e.message));
  await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/#learn');
  if(!await page.evaluate(()=>crossOriginIsolated)){
    await page.fill('#tutorialEditor','-- keep my edit\n#eval 42');
    await page.click('#setupLean');await page.waitForFunction(()=>crossOriginIsolated);
    assert.match(await page.locator('#tutorialEditor').inputValue(),/keep my edit/);
    await page.click('#tutorialReset');
  }
  assert(await page.locator('#tutorialPanel').isVisible());assert(!await page.locator('#workbenchPanel').isVisible());
  await page.setViewportSize({width:390,height:844});
  assert(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth));
  await page.screenshot({path:'../../labs/linked-assurance/artifacts/tutorial-mobile.png',fullPage:true});
  await page.setViewportSize({width:1280,height:1000});
  await page.screenshot({path:'../../labs/linked-assurance/artifacts/tutorial-desktop.png',fullPage:true});
  console.log('Downloading and saving real Lean compiler assets…');
  await page.click('#downloadLean');
  await page.waitForFunction(()=>document.querySelector('#downloadLean').textContent==='Lean machinery ready');
  await page.reload();
  await page.waitForFunction(()=>document.querySelector('#downloadLean').textContent==='Load saved Lean 4 machinery');
  let assetRequests=0;
  await page.route('**/artifacts/toolchain-4.33.1/**',route=>{assetRequests++;return route.abort();});
  await page.click('#downloadLean');
  await page.waitForFunction(()=>document.querySelector('#downloadLean').textContent==='Lean machinery ready');
  assert.equal(assetRequests,0,'Cached compiler must not request assets again');
  const checks=[];
  for(const lesson of lessons){
    await page.evaluate(id=>location.hash='learn/'+id,lesson.id);
    await page.waitForFunction(title=>document.querySelector('#lessonTitle').textContent===title,lesson.title);
    console.log('Tutorial: '+lesson.id);
    await page.click('#tutorialRun');
    await page.waitForFunction(()=>!document.querySelector('#tutorialRun').disabled);
    const result=JSON.parse(await page.locator('#tutorialRaw').textContent());
    assert.equal(result.accepted,lesson.expected!=='reject',JSON.stringify({lesson:lesson.id,result}));
    checks.push({id:lesson.id,accepted:result.accepted});
    if(lesson.solution){
      await page.fill('#tutorialEditor',lesson.solution);await page.click('#tutorialRun');
      await page.waitForFunction(()=>!document.querySelector('#tutorialRun').disabled);
      assert.equal(JSON.parse(await page.locator('#tutorialRaw').textContent()).accepted,true);
    }
  }
  await page.fill('#tutorialEditor','theorem placeholder : False := by\n  sorry\n');await page.click('#tutorialRun');
  await page.waitForFunction(()=>!document.querySelector('#tutorialRun').disabled);
  assert.match(await page.locator('#tutorialStatus').textContent(),/placeholder/,await page.locator('#tutorialRaw').textContent());
  await page.fill('#tutorialEditor','#eval 42');assert.equal(await page.locator('#tutorialRaw').textContent(),'');
  await page.click('#tutorialRun');await page.waitForFunction(()=>!document.querySelector('#tutorialRun').disabled);
  assert.match(await page.locator('#tutorialOutput').textContent(),/42/);
  await page.click('#workbenchTab');await page.locator('#workbenchPanel').waitFor({state:'visible'});
  await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/tools/hello/');
  console.log('Checking hello-world page with the shared compiler cache…');
  await page.waitForFunction(()=>document.querySelector('#downloadLean').textContent==='Load saved Lean 4 machinery');
  await page.click('#run');await page.waitForFunction(()=>!document.querySelector('#run').disabled);
  assert.match(await page.locator('#status').textContent(),/All checks passed/,await page.locator('#result').textContent());
  assert.equal(assetRequests,0);
  assert.equal(errors.length,0,errors.join('\n'));
  const report={status:'pass',browser:browser.version(),checks,cacheReloadAssetRequests:assetRequests,rejectedPlaceholder:true,helloPage:true};
  await fs.writeFile('../../labs/linked-assurance/artifacts/tutorial-browser-checks.json',JSON.stringify(report,null,2)+'\n');
  console.log(JSON.stringify(report));
}finally{await browser.close();}
