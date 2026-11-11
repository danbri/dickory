const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const {createRequire}=require('node:module'),{createHash}=require('node:crypto');
require('./checks.js');
const root=path.resolve(__dirname,'../../artifacts/toolchain-4.33.1'),bin=path.join(root,'bin');
const walk=dir=>fs.readdirSync(dir,{withFileTypes:true}).flatMap(e=>e.isDirectory()?walk(path.join(dir,e.name)):[path.join(dir,e.name)]);
let diagnostics=[];
const timeout=setTimeout(()=>{console.error('Hello-world compiler timeout');process.exit(1);},240000);
const Module={
  INITIAL_MEMORY:2048*1024*1024,noInitialRun:true,noExitRuntime:true,locateFile:n=>path.join(bin,n),
  print:text=>{if(text.startsWith('{'))try{const d=JSON.parse(text);if(d.severity)diagnostics.push(d);}catch{}},
  printErr:text=>{if(!/^\[(PROFILE|DEBUG|WASM)/.test(text))console.error(text);},
  preRun:[()=>{
    for(const d of [bin,'/lib/lean','/workspace'])Module.FS.mkdirTree(d);
    for(const f of walk(path.join(root,'lib/lean'))){
      const dest='/lib/lean/'+path.relative(path.join(root,'lib/lean'),f);
      Module.FS.mkdirTree(path.dirname(dest));Module.FS.writeFile(dest,fs.readFileSync(f),{canOwn:true});
    }
    Module.ENV.LEAN_PATH='/lib/lean';Module.FS.chdir('/workspace');
  }],
  onRuntimeInitialized:()=>setImmediate(async()=>{
    try{
      leanHello.initialize(Module);
      const cases=await leanHello.run(Module,()=>{const d=diagnostics;diagnostics=[];return d;},n=>console.log('Checking '+n));
      const runtime=globalThis.Deno?'Deno '+Deno.version.deno:'Node '+process.version;
      const report={status:'pass',runtime,leanCommit:'4f9018a62ead9be0ffd652021d5afc8501e92253',
        hashes:Object.fromEntries(['lean.js','lean.wasm'].map(n=>[n,createHash('sha256').update(fs.readFileSync(path.join(bin,n))).digest('hex')])),cases};
      fs.writeFileSync(path.join(root,'..',globalThis.Deno?'hello-deno-checks.json':'hello-node-checks.json'),JSON.stringify(report,null,2)+'\n');
      console.log(JSON.stringify({status:report.status,runtime,cases:cases.map(({name,milliseconds,exitCode})=>({name,milliseconds,exitCode}))}));
      clearTimeout(timeout);process.exit(0);
    }catch(e){console.error(e);process.exit(1);}
  }),onAbort:why=>{console.error(why);process.exit(1);}
};
const filename=path.join(bin,'lean.js');globalThis.__linkedHelloModule=Module;
vm.compileFunction('Module=globalThis.__linkedHelloModule;\n'+fs.readFileSync(filename,'utf8'),
  ['exports','require','module','__filename','__dirname'],{filename})({},createRequire(filename),{exports:{}},filename,bin);
