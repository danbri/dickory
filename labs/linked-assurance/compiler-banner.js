import {prepareCompilerFiles,compilerFilesSaved,onCompilerDownload,clearCompilerCache} from './compiler-cache.js';

export async function enableIsolation(){
  if(!navigator.serviceWorker)throw Error('Service workers unavailable. Use the supplied local server with --isolate.');
  const registration=await navigator.serviceWorker.register(new URL('./coi-sw.js',import.meta.url),{scope:new URL('./',import.meta.url).href});
  await navigator.serviceWorker.ready;
  if(!navigator.serviceWorker.controller)await new Promise((resolve,reject)=>{
    const done=()=>{clearTimeout(timer);resolve();};
    const timer=setTimeout(()=>{navigator.serviceWorker.removeEventListener('controllerchange',done);reject(Error('Isolation setup is taking longer than expected. Reload this page.'));},10000);
    navigator.serviceWorker.addEventListener('controllerchange',done,{once:true});
  });
  if(registration.active){window.dispatchEvent(new Event('lean-before-reload'));location.reload();}
}

export function mountCompilerBanner(target){
  target.classList.add('compilerBanner');
  target.innerHTML=`<div><strong>Lean 4.33.1 · on this device</strong>
    <p>About 184 MB, saved for future visits. You can prepare it now, or let your first policy check do this. First setup takes a few minutes; later runs reuse the machinery.</p>
    <p id="compilerDownloadState" role="status">Compiler files have not been loaded in this tab.</p></div>
    <div class="downloadActions"><button id="downloadLean">Download Lean 4 machinery · 184 MB</button>
    <details id="compilerSetupTools"><summary>Advanced setup</summary><button id="setupLean" class="secondary">Enable browser isolation and reload</button>
    <button id="clearLeanCache" class="secondary">Clear saved compiler files</button><p>Browsers may clear saved files when storage is tight.</p></details></div>`;
  const status=target.querySelector('#compilerDownloadState'),download=target.querySelector('#downloadLean'),setup=target.querySelector('#setupLean');
  let active=false;
  const report=text=>{status.textContent=text;};
  onCompilerDownload(text=>{active=true;report(text);if(text.startsWith('Lean 4.33.1 files ready')){download.textContent='Compiler files ready';download.disabled=true;}});
  compilerFilesSaved().then(saved=>{if(saved&&!active){download.textContent='Load saved Lean 4 machinery';report('Saved compiler files found on this device. Their integrity is checked when loaded.');}});
  download.onclick=async()=>{
    active=true;download.disabled=true;
    try{
      if(!globalThis.crossOriginIsolated){sessionStorage.setItem('linked-assurance-resume-download','1');report('Setting up the browser runtime. Reloading once, then downloading…');await enableIsolation();return;}
      await prepareCompilerFiles(report);
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
    if(globalThis.crossOriginIsolated)download.click();else report('Browser isolation was not enabled. Open Advanced setup to retry.');
  }
}
