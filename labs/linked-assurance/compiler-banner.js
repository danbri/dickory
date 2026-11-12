import {prepareCompilerFiles,releasePreparedCompilerFiles,compilerFilesSaved,onCompilerDownload,clearCompilerCache} from './compiler-cache.js';
import {compilerEnvironment,compilerUnavailableReason,compilerRunSnapshot} from './lean-host.js';

function waitForChange(target,event,ready,message){
  return new Promise((resolve,reject)=>{
    const cleanup=()=>{clearTimeout(timer);target.removeEventListener(event,check);};
    const check=()=>{if(ready()){cleanup();resolve();}};
    const timer=setTimeout(()=>{cleanup();reject(Error(message));},15000);
    target.addEventListener(event,check);check();
  });
}

export async function enableIsolation(){
  if(window.self!==window.top)throw Error('Open this page directly in Safari or a desktop browser. An embedded page cannot enable isolation for its containing app.');
  if(!navigator.serviceWorker)throw Error('This browser cannot install the isolation helper. Open this HTTPS URL directly in Safari or a desktop browser.');
  const registration=await navigator.serviceWorker.register(new URL('./coi-sw.js',import.meta.url),{scope:new URL('./',import.meta.url).href,updateViaCache:'none'});
  await registration.update();
  const worker=registration.installing||registration.waiting||registration.active;
  if(!worker)throw Error('The browser did not install the isolation helper.');
  await waitForChange(worker,'statechange',()=>worker.state==='activated','The updated isolation helper did not activate. Try opening this page in a new browser tab.');
  await waitForChange(navigator.serviceWorker,'controllerchange',()=>navigator.serviceWorker.controller===worker,'The isolation helper could not take control of this page. Try opening it in a new browser tab.');
  try{sessionStorage.setItem('linked-assurance-isolation-attempted','1');}catch{}
  window.dispatchEvent(new Event('lean-before-reload'));location.reload();
}

export function mountCompilerBanner(target){
  target.classList.add('compilerBanner');
  target.innerHTML=`<div><strong>Lean 4.33.1 · on this device</strong>
    <p>About 184 MB, saved for future visits. You can prepare it now, or let your first policy check do this. First setup takes a few minutes; later runs reuse the machinery.</p>
    <p id="compilerBrowserState" role="status"></p>
    <p id="compilerDownloadState" role="status">Compiler files have not been loaded in this tab.</p>
    <p id="compilerRunState" role="status"></p>
    <details><summary>Browser details</summary><button id="copyCompilerDetails" class="secondary">Copy diagnostics</button><span id="compilerCopyState" role="status"></span><pre id="compilerBrowserDetails"></pre></details></div>
    <div class="downloadActions"><button id="downloadLean">Download Lean 4 machinery · 184 MB</button>
    <details id="compilerSetupTools"><summary>Advanced setup</summary><button id="setupLean" class="secondary">Enable browser isolation and reload</button>
    <button id="clearLeanCache" class="secondary">Clear saved compiler files</button><p>Browsers may clear saved files when storage is tight.</p></details></div>`;
  const status=target.querySelector('#compilerDownloadState'),download=target.querySelector('#downloadLean'),setup=target.querySelector('#setupLean');
  const env=compilerEnvironment();
  const updateDetails=()=>{
    const e=compilerEnvironment(),run=compilerRunSnapshot();
    target.querySelector('#compilerBrowserDetails').textContent=JSON.stringify({browser:navigator.userAgent,secureContext:e.secureContext,embedded:e.embedded,crossOriginIsolated:e.isolated,SharedArrayBuffer:e.sharedMemory,serviceWorkerAvailable:e.serviceWorkerAvailable,serviceWorkerControlled:e.serviceWorkerControlled,run},null,2);
    const current=run.current;
    target.querySelector('#compilerRunState').textContent=current?current.status==='running'?`${current.activity}: ${current.phase}`:`${current.activity}: ${current.status}${current.error?' — '+current.error.split('\n')[0]:''}.`:
      run.previous?.status==='running'?`The previous check did not finish before this page loaded. Last stage: ${run.previous.phase}. This can follow a manual reload or the browser stopping the tab. No automatic retry has started.`:'';
  };
  updateDetails();window.addEventListener('lean-runtime-status',updateDetails);
  target.querySelector('#copyCompilerDetails').onclick=async()=>{
    updateDetails();
    try{await navigator.clipboard.writeText(target.querySelector('#compilerBrowserDetails').textContent);target.querySelector('#compilerCopyState').textContent=' Copied.';}
    catch{target.querySelector('#compilerCopyState').textContent=' Select and copy the details below.';}
  };
  let attempted=false;try{attempted=sessionStorage.getItem('linked-assurance-isolation-attempted')==='1';}catch{}
  target.querySelector('#compilerBrowserState').textContent=env.isolated&&env.sharedMemory?'Browser isolation and shared memory are available.':attempted?'Setup ran, but this browser still cannot run Lean. '+compilerUnavailableReason():'Running Lean needs browser isolation and shared memory. Setup checks these before downloading.';
  let active=false;
  const report=text=>{status.textContent=text;};
  onCompilerDownload(text=>{active=true;report(text);if(text.startsWith('Lean 4.33.1 files ready')){download.textContent='Compiler files ready';download.disabled=true;}});
  compilerFilesSaved().then(saved=>{if(saved&&!active){download.textContent='Load saved Lean 4 machinery';report('Saved compiler files found on this device. Their integrity is checked when loaded.');}});
  download.onclick=async()=>{
    active=true;download.disabled=true;
    try{
      if(!globalThis.crossOriginIsolated){sessionStorage.setItem('linked-assurance-resume-download','1');report('Setting up the browser runtime. Reloading once, then downloading…');await enableIsolation();return;}
      const unavailable=compilerUnavailableReason();if(unavailable)throw Error(unavailable);
      const files=await prepareCompilerFiles(report);
      if(files.cache.persistentCacheAvailable)releasePreparedCompilerFiles();
    }catch(e){sessionStorage.removeItem('linked-assurance-resume-download');report('Setup or download failed: '+e.message);download.disabled=false;download.textContent='Retry Lean setup';}
  };
  setup.hidden=globalThis.crossOriginIsolated===true;
  setup.onclick=async()=>{setup.disabled=true;try{report('Enabling compiler isolation; this page will reload once…');await enableIsolation();}catch(e){report(e.message);setup.disabled=false;}};
  target.querySelector('#clearLeanCache').onclick=async()=>{
    try{await clearCompilerCache();active=true;download.disabled=false;download.textContent='Download Lean 4 machinery · 184 MB';report('Saved files cleared. A compiler already running in this tab can continue.');}
    catch(e){report(e.message);}
  };
  if(sessionStorage.getItem('linked-assurance-resume-download')){
    sessionStorage.removeItem('linked-assurance-resume-download');
    if(globalThis.crossOriginIsolated)download.click();else report('No compiler download started: '+compilerUnavailableReason());
  }
}
