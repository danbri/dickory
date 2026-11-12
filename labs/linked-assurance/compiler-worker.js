// Lean 4.33.1 wasm32 host. Initialization follows cauli/lean4's Apache-2.0
// tests/wasm/browser-worker.js at 4f9018a62ead9be0ffd652021d5afc8501e92253.
let config,ready=false,stdout=[],stderr=[],compilerMemory;
const initialMemoryBytes=64*1024*1024;
const send=(type,fields={})=>postMessage({type,...fields});
const describeError=e=>[e?.message||String(e),e?.stack].filter(Boolean).join('\n');
const fail=e=>send('error',{error:describeError(e),stdout:stdout.join('\n'),stderr:stderr.join('\n'),context:{workerName:self.name,pthread:typeof ENVIRONMENT_IS_PTHREAD==='undefined'?null:ENVIRONMENT_IS_PTHREAD,exitStatus:typeof EXITSTATUS==='undefined'?null:EXITSTATUS}});
function output(target,line){
  if(/^\[(PROFILE|DEBUG|WASM)/.test(line)){send('activity');return;}
  target.push(line);
}
function string(s){const p=Module.stringToNewUTF8(s),o=Module._lean_mk_string(p);Module._free(p);return o;}
function ioValue(r){
  if((Module.getValue(r+7,'i8')&255)!==0){Module._lean_io_result_show_error(r);throw Error('Lean IO failure');}
  const box=Module.getValue(r+8,'i32')>>>0;
  return Module.getValue(box+8,'i32')>>>0;
}
function done(exitCode,runtimeFault=false){
  const artifacts=[];
  if(exitCode===0&&config.exportPrefix){
    for(const name of Module.FS.readdir('/lib/lean'))
      if(name.startsWith(config.exportPrefix+'.'))artifacts.push({name,data:Module.FS.readFile('/lib/lean/'+name)});
  }
  send('result',{stdout:stdout.join('\n'),stderr:stderr.join('\n'),exitCode,artifacts,runtimeFault,
    memory:{initialBytes:initialMemoryBytes,linearBytes:compilerMemory.buffer.byteLength}});
}
function invokeMain(args){
  // Call Lean's exported shell entry point inside this existing browser worker.
  // Unlike callMain, this preserves exceptions instead of swallowing the
  // Emscripten unwind sentinel and returning an undefined exit status.
  const all=['lean',...args],strings=all.map(s=>Module.stringToNewUTF8(s)),argv=Module._malloc(4*(all.length+1));
  strings.forEach((s,i)=>Module.setValue(argv+4*i,s,'i32'));Module.setValue(argv+4*all.length,0,'i32');
  return Module.ccall('lean_main','number',['number','number'],[all.length,argv]);
}
function compile(source,path){
  stdout=[];stderr=[];
  try {done(ioValue(Module._lean_wasm_compile(string(source),string(path))));}
  catch(e){stderr.push(describeError(e));done(1,true);}
}
function boot(){
  send('progress',{phase:'Allocating Lean shared memory (64 MiB to start)…'});
  compilerMemory=new WebAssembly.Memory({initial:initialMemoryBytes/65536,maximum:65536,shared:true});
  self.Module={
    // Match the pinned distribution's 64 MiB default. Its allocator grows memory
    // when needed; reserving 2 GiB up front needlessly excludes mobile browsers.
    wasmMemory:compilerMemory,INITIAL_MEMORY:initialMemoryBytes,noInitialRun:true,noExitRuntime:true,
    mainScriptUrlOrBlob:config.pthreadUrl,
    locateFile:name=>name.endsWith('.wasm')?config.wasmUrl:name,
    print:line=>output(stdout,line),printErr:line=>output(stderr,line),
    preRun:[()=>{
      for(const d of ['/bin','/lib/lean','/workspace'])Module.FS.mkdirTree(d);
      for(const f of config.files){const p='/lib/lean/'+f.name;Module.FS.mkdirTree(p.slice(0,p.lastIndexOf('/')));Module.FS.writeFile(p,f.data instanceof Uint8Array?f.data:new Uint8Array(f.data),{canOwn:true});}
      config.files=[];Module.ENV.LEAN_PATH='/lib/lean';
      // Already off the UI thread; run the shell in this worker.
      Module.ENV.LEAN_MAIN_USE_THREAD='0';Module.FS.chdir('/workspace');
      if(!config.persistent)Module.FS.writeFile(config.path,config.source);
    }],
    onAbort:fail,
    onRuntimeInitialized:()=>setTimeout(()=>{
      try {
        send('progress',{phase:config.persistent?'Lean runtime initialised; preparing the reusable session…':'Lean runtime initialised; processing '+config.path.split('/').pop()+'…'});
        if(config.persistent){
          Module._lean_initialize_runtime_module();Module._lean_initialize();
          Module._lean_io_mark_end_initialization();Module._lean_init_task_manager_using(1);Module._lean_enable_initializer_execution();
          const r=Module._lean_init_search_path();
          if((Module.getValue(r+7,'i8')&255)!==0)throw Error('Lean search path initialization failed');
          Module._emscripten_runtime_keepalive_push?.();ready=true;send('ready');
        }else{
          let exitCode;
          try{exitCode=invokeMain(['-j1','-DElab.async=false',...config.flags,config.path]);}
          catch(e){if(typeof e.status==='number')exitCode=e.status;else throw e;}
          if(typeof exitCode!=='number')throw Error('Compiler did not return an exit status');
          done(exitCode);
        }
      }catch(e){
        if(e==='unwind'){
          // A failed pthread yields so its error can reach this worker's event
          // loop. Preserve that error instead of reporting the unwind sentinel.
          setTimeout(()=>fail('Lean worker unwound without reporting a compilation result.'),1000);
        }else fail(e);
      }
    },0)
  };
  send('progress',{phase:'Loading and compiling the WebAssembly machinery…'});
  importScripts(config.jsUrl);
  // Keep one task worker; the pinned glue eagerly creates a pool of four.
  // Shrink it before the async WASM initialization starts the preRun loader.
  for(const worker of PThread.unusedWorkers.splice(1))worker.terminate();
}
self.onmessage=({data})=>{
  if(data.type==='boot'){config=data;try{boot();}catch(e){fail(e);}}
  else if(data.type==='compile'&&ready)compile(data.source,data.path);
};
self.addEventListener('error',event=>{fail(event.error||event.message);event.preventDefault();});
