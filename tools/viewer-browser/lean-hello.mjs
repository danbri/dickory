import {chromium} from 'playwright';
import fs from 'node:fs/promises';
import {createHash} from 'node:crypto';
const browser=await chromium.launch({headless:true});
const artifacts=new URL('../../labs/linked-assurance/artifacts/',import.meta.url);
try{
  const page=await browser.newPage();
  page.on('console',m=>{if(m.type()==='error')console.log('Browser:',m.text().slice(0,300));});
  await page.goto((process.env.LINKED_SITE_URL||'http://127.0.0.1:8081')+'/labs/linked-assurance/');
  if(!await page.evaluate(()=>crossOriginIsolated)){
    await page.click('#isolate');await page.waitForFunction(()=>crossOriginIsolated);
  }
  await page.exposeFunction('helloProgress',s=>console.log('Checking '+s));
  const result=await page.evaluate(()=>new Promise((resolve,reject)=>{
    if(!crossOriginIsolated)return reject(Error('Page is not cross-origin isolated'));
    let ticks=0;const heartbeat=setInterval(()=>ticks++,100);
    const worker=new Worker('./tools/hello/browser-worker.js');
    const finish=()=>{clearInterval(heartbeat);clearTimeout(timer);worker.terminate();};
    const timer=setTimeout(()=>{finish();reject(Error('Hello-world timeout'));},240000);
    worker.onerror=e=>{finish();reject(Error(e.message));};
    worker.onmessage=({data})=>{
      if(data.progress){window.helloProgress(data.progress);return;}
      finish();if(data.error)reject(Error(data.error));else resolve({...data,uiHeartbeatTicks:ticks});
    };
  }));
  const hashes={};for(const name of ['lean.js','lean.wasm'])hashes[name]=createHash('sha256').update(await fs.readFile(new URL('toolchain-4.33.1/bin/'+name,artifacts))).digest('hex');
  const report={...result,browser:browser.version(),leanCommit:'4f9018a62ead9be0ffd652021d5afc8501e92253',hashes};
  await fs.writeFile(new URL('hello-browser-checks.json',artifacts),JSON.stringify(report,null,2)+'\n');
  console.log(JSON.stringify({...report,cases:report.cases.map(({name,milliseconds,exitCode})=>({name,milliseconds,exitCode}))}));
}finally{await browser.close();}
