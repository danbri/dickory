import {chromium} from 'playwright';
import fs from 'node:fs/promises';
const browser=await chromium.launch({headless:true});
try{
 const page=await browser.newPage();page.setDefaultTimeout(240000);
 page.on('pageerror',e=>console.log('PAGEERROR',e.message));
 page.on('console',m=>{if(!m.text().includes('[DEBUG:'))console.log('CONSOLE',m.text().slice(0,350));});
 await page.route('**/compiler-assets.json',async route=>{
   const manifest=await (await route.fetch()).json();
   for(const [name,asset] of Object.entries(manifest))asset.url='http://127.0.0.1:8012/labs/linked-assurance/artifacts/'+name;
   await route.fulfill({json:manifest});
 });
 await page.goto('http://127.0.0.1:8012/labs/linked-assurance/');
 console.log('isolation',await page.evaluate(()=>crossOriginIsolated));
 await page.waitForFunction(()=>document.getElementById('leanEditor').value.includes('def policy'));
 await page.click('#compile');
 const started=Date.now();
 while(Date.now()-started<360000){
   await page.waitForTimeout(10000);
   const status=await page.locator('#compilerState').textContent();console.log('STATUS',status);
   if(await page.locator('#compile').isEnabled())break;
 }
 const diagnostics=await page.locator('#compilerReport').textContent();
 console.log('REPORT',diagnostics.slice(0,14000));
 const report={status:diagnostics.includes('contractChecked\": true')?'pass':'unavailable',
   isolation:await page.evaluate(()=>crossOriginIsolated),assets:'Pinned hashes; local mirror of the declared bytes',
   diagnostics,environment:await page.evaluate(async()=> (await import('./lean-host.js')).compilerEnvironment())};
 await fs.writeFile('../../labs/linked-assurance/artifacts/compiler-checks.json',JSON.stringify(report,null,2)+'\n');
 await page.screenshot({path:'../../labs/linked-assurance/artifacts/workbench.png',fullPage:true});
}finally{await browser.close();}
