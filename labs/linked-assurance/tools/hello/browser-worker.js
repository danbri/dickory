// Same programs and compiler bytes as node.cjs; no policy/application bridge.
let diagnostics=[];
const runtime=new URL('../../artifacts/toolchain-4.33.1/',location.href).href;
var Module={
  INITIAL_MEMORY:2048*1024*1024,noInitialRun:true,noExitRuntime:true,
  mainScriptUrlOrBlob:runtime+'bin/lean.js',locateFile:n=>runtime+'bin/'+n,
  print:text=>{if(text.startsWith('{'))try{const d=JSON.parse(text);if(d.severity)diagnostics.push(d);}catch{}},
  printErr:text=>{if(!/^\[(PROFILE|DEBUG|WASM)/.test(text))console.log(text);},
  preRun:[()=>{for(const d of ['/bin','/lib/lean','/workspace'])Module.FS.mkdirTree(d);Module.FS.chdir('/workspace');}],
  onAbort:why=>postMessage({error:String(why)}),
  onRuntimeInitialized:async()=>{
    try{
      const listing=await (await fetch(new URL('../../artifacts/toolchain-4.33.1-files.json',location.href))).json();
      const files=listing.filter(f=>f.name.startsWith('lib/lean/'));let i=0;
      postMessage({progress:'Loading matching Init library'});
      await Promise.all(Array.from({length:8},async()=>{while(i<files.length){const f=files[i++];
        const r=await fetch(runtime+f.name);if(!r.ok)throw Error('Library fetch failed: '+f.name);
        const bytes=new Uint8Array(await r.arrayBuffer());if(bytes.length!==f.bytes)throw Error('Wrong file size: '+f.name);
        const p='/'+f.name;Module.FS.mkdirTree(p.slice(0,p.lastIndexOf('/')));Module.FS.writeFile(p,bytes,{canOwn:true});
      }}));
      Module.ENV.LEAN_PATH='/lib/lean';leanHello.initialize(Module);
      const cases=await leanHello.run(Module,()=>{const d=diagnostics;diagnostics=[];return d;},name=>postMessage({progress:name}));
      postMessage({status:'pass',cases});
    }catch(e){postMessage({error:String(e.stack||e)});}
  }
};
importScripts('./checks.js',runtime+'bin/lean.js');
