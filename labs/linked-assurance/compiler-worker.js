// Lean 4.33.1 wasm32 host. Initialization follows cauli/lean4's Apache-2.0
// tests/wasm/browser-worker.js at 4f9018a62ead9be0ffd652021d5afc8501e92253.
let config,ready=false,stdout=[],stderr=[];
const send=(type,fields={})=>postMessage({type,...fields});
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
function done(exitCode){
  const artifacts=[];
  if(exitCode===0&&config.exportPrefix){
    for(const name of Module.FS.readdir('/lib/lean'))
      if(name.startsWith(config.exportPrefix+'.'))artifacts.push({name,data:Module.FS.readFile('/lib/lean/'+name)});
  }
  send('result',{stdout:stdout.join('\n'),stderr:stderr.join('\n'),exitCode,artifacts});
}
function invokeMain(args){
  if(typeof Module.callMain==='function')return Module.callMain(args);
  const all=['lean',...args],strings=all.map(s=>Module.stringToNewUTF8(s)),argv=Module._malloc(4*(all.length+1));
  strings.forEach((s,i)=>Module.setValue(argv+4*i,s,'i32'));Module.setValue(argv+4*all.length,0,'i32');
  return Module.ccall('main','number',['number','number'],[all.length,argv]);
}
function compile(source,path){
  stdout=[];stderr=[];
  try {done(ioValue(Module._lean_wasm_compile(string(source),string(path))));}
  catch(e){stderr.push(String(e.stack||e));done(1);}
}
function boot(){
  self.Module={
    INITIAL_MEMORY:2048*1024*1024,noInitialRun:true,noExitRuntime:true,
    mainScriptUrlOrBlob:config.jsUrl,
    locateFile:name=>name.endsWith('.wasm')?config.wasmUrl:name,
    print:line=>output(stdout,line),printErr:line=>output(stderr,line),
    preRun:[()=>{
      for(const d of ['/bin','/lib/lean','/workspace'])Module.FS.mkdirTree(d);
      for(const f of config.files){const p='/lib/lean/'+f.name;Module.FS.mkdirTree(p.slice(0,p.lastIndexOf('/')));Module.FS.writeFile(p,new Uint8Array(f.data),{canOwn:true});}
      config.files=[];Module.ENV.LEAN_PATH='/lib/lean';Module.FS.chdir('/workspace');
      if(!config.persistent)Module.FS.writeFile(config.path,config.source);
    }],
    onAbort:why=>send('error',{error:String(why)}),
    onRuntimeInitialized:()=>setTimeout(()=>{
      try {
        if(config.persistent){
          Module._lean_initialize_runtime_module();Module._lean_initialize();
          Module._lean_io_mark_end_initialization();Module._lean_init_task_manager();Module._lean_enable_initializer_execution();
          const r=Module._lean_init_search_path();
          if((Module.getValue(r+7,'i8')&255)!==0)throw Error('Lean search path initialization failed');
          Module._emscripten_runtime_keepalive_push?.();ready=true;send('ready');
        }else{
          let exitCode;
          try{exitCode=invokeMain([...config.flags,config.path]);}
          catch(e){if(typeof e.status==='number')exitCode=e.status;else throw e;}
          if(typeof exitCode!=='number')throw Error('Compiler did not return an exit status');
          done(exitCode);
        }
      }catch(e){send('error',{error:String(e.stack||e)});}
    },0)
  };
  importScripts(config.jsUrl);
}
self.onmessage=({data})=>{
  if(data.type==='boot'){config=data;try{boot();}catch(e){send('error',{error:String(e.stack||e)});}}
  else if(data.type==='compile'&&ready)compile(data.source,data.path);
};
