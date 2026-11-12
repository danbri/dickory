// Build published modules with the browser's exact wasm32 compiler, not native oleans.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const {createRequire}=require('node:module'),{createHash}=require('node:crypto');
if(Number(process.versions.node.split('.')[0])<26)throw Error('Use Node 26 or newer for this compiler: older V8 releases reject its WASM export count.');
const lab=path.resolve(__dirname,'..'),root=path.join(lab,'artifacts/toolchain-4.33.1'),bin=path.join(root,'bin');
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const {policyAudit,auditContract,accepted}=require('../lean-host.js');
const moduleName=process.argv.includes('--policy')?'Policy':'Workbench';
const manifest=JSON.parse(fs.readFileSync(path.join(lab,'compiler-assets.json'),'utf8'));
for(const [name,asset] of Object.entries(manifest)){
  const bytes=fs.readFileSync(path.join(lab,asset.url));
  if(bytes.length!==asset.bytes||hash(bytes)!==asset.sha256)throw Error('Compiler integrity failure: '+name);
}
const source=fs.readFileSync(path.join(lab,'lean',moduleName+'.lean'));
const compiledSource=moduleName==='Policy'?Buffer.concat([source,Buffer.from(policyAudit)]):source;
const support=moduleName==='Policy'?JSON.parse(fs.readFileSync(path.join(lab,'artifacts/workbench-wasm.json'),'utf8')):null;
if(support&&(support.status!=='pass'||support.sourceSha256!==hash(fs.readFileSync(path.join(lab,'lean/Workbench.lean')))||Object.entries(manifest).some(([name,a])=>support.compilerSha256[name]!==a.sha256)))throw Error('Stale support bundle');
const scratch=fs.mkdtempSync('/tmp/dickory-support-');
fs.writeFileSync(path.join(scratch,moduleName+'.lean'),compiledSource);process.chdir(scratch);
const walk=dir=>fs.readdirSync(dir,{withFileTypes:true}).flatMap(e=>e.isDirectory()?walk(path.join(dir,e.name)):[path.join(dir,e.name)]);
const stdout=[],stderr=[];
const timeout=setTimeout(()=>{console.error('Support compiler timeout');process.exit(1);},240000);
const Module={
  INITIAL_MEMORY:64*1024*1024,noInitialRun:true,locateFile:n=>path.join(bin,n),
  print:line=>{if(!/^\[(PROFILE|DEBUG|WASM)/.test(line))stdout.push(line);},
  printErr:line=>{if(!/^\[(PROFILE|DEBUG|WASM)/.test(line))stderr.push(line);},
  preRun:[()=>{
    Module.FS.mkdirTree('/lib/lean');Module.FS.mkdirTree(bin);
    for(const file of walk(path.join(root,'lib/lean'))){
      const dest='/lib/lean/'+path.relative(path.join(root,'lib/lean'),file);
      Module.FS.mkdirTree(path.dirname(dest));Module.FS.writeFile(dest,fs.readFileSync(file),{canOwn:true});
    }
    for(const file of support?.files||[]){
      const bytes=Buffer.from(file.base64,'base64');if(hash(bytes)!==file.sha256)throw Error('Damaged support bundle');
      Module.FS.writeFile('/lib/lean/'+file.name,bytes,{canOwn:true});
    }
    Module.ENV.LEAN_PATH='/lib/lean';Module.ENV.LEAN_MAIN_USE_THREAD='0';
  }],
  onRuntimeInitialized:()=>setImmediate(()=>{
    try{
      const args=['lean','-j1','-DElab.async=false','--json','-o','/lib/lean/'+moduleName+'.olean',moduleName+'.lean'];
      const pointers=args.map(arg=>Module.stringToNewUTF8(arg)),argv=Module._malloc(4*(args.length+1));
      pointers.forEach((p,i)=>Module.setValue(argv+4*i,p,'i32'));Module.setValue(argv+4*args.length,0,'i32');
      let exitCode;
      try{exitCode=Module.ccall('lean_main','number',['number','number'],[args.length,argv]);}
      catch(e){if(typeof e?.status==='number')exitCode=e.status;else throw e;}
      const result={exitCode,stdout:stdout.join('\n'),stderr:stderr.join('\n')};
      if(!accepted(result))throw Error('Module check failed: '+[...stdout,...stderr].join('\n'));
      if(moduleName==='Policy'&&!['policy_contract','policy_pipeline_contract','adaptEvidence_contract'].every(name=>auditContract(result,'LinkedAssurance.'+name)))throw Error('Policy contract audit failed: '+result.stdout);
      const files=Module.FS.readdir('/lib/lean').filter(name=>name.startsWith(moduleName+'.')).map(name=>{
        const bytes=Buffer.from(Module.FS.readFile('/lib/lean/'+name));
        return {name,bytes:bytes.length,sha256:hash(bytes),base64:bytes.toString('base64')};
      });
      if(!files.some(f=>f.name===moduleName+'.olean'))throw Error('Compiler emitted no module');
      const bundle={status:'pass',sourceSha256:hash(source),compiledSourceSha256:hash(compiledSource),supportSha256:support?.sourceSha256,compilerSha256:Object.fromEntries(Object.entries(manifest).map(([n,a])=>[n,a.sha256])),result,files};
      fs.writeFileSync(path.join(lab,'artifacts',moduleName.toLowerCase()+'-wasm.json'),JSON.stringify(bundle)+'\n');
      console.log(JSON.stringify({status:'pass',sourceSha256:bundle.sourceSha256,files:files.map(({name,bytes,sha256})=>({name,bytes,sha256}))}));
      clearTimeout(timeout);fs.rmSync(scratch,{recursive:true});process.exit(0);
    }catch(e){console.error(e);process.exit(1);}
  }),onAbort:why=>{console.error(why);process.exit(1);}
};
const filename=path.join(bin,'lean.js');globalThis.__linkedSupportModule=Module;
vm.compileFunction('Module=globalThis.__linkedSupportModule;\n'+fs.readFileSync(filename,'utf8'),
  ['exports','require','module','__filename','__dirname'],{filename})({},createRequire(filename),{exports:{}},filename,bin);
