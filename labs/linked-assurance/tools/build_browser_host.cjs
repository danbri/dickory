#!/usr/bin/env node
// Compact only Emscripten's repetitive JS export wiring. The compiler WASM and
// library bytes stay unchanged. Refuse any input other than the pinned glue.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const assert=require('node:assert/strict'),{createHash}=require('node:crypto');
const lab=path.resolve(__dirname,'..'),hash=s=>createHash('sha256').update(s).digest('hex');
const source=fs.readFileSync(path.join(lab,'artifacts/toolchain-4.33.1/bin/lean.js'),'utf8');
assert.equal(hash(source),'79f6bb9f2bd66e1e13c2d3ebfbf73d8e755d7af0e318b15367b1e50c0923ef37');
const start=source.indexOf('function assignWasmExports('),end=source.indexOf('}',start)+1;
const declarations=source.lastIndexOf('var ',start),body=source.slice(source.indexOf('{',start)+1,end-1);
const outside=source.slice(0,declarations)+source.slice(end);
const identifiers=new Set(outside.match(/[\w$]+/g));
const records=body.split(';').filter(Boolean).map(statement=>{
  if(statement==='__indirect_function_table=wasmTable=wasmExports["__indirect_function_table"]')
    return {local:'wasmTable',symbol:'__indirect_function_table',statement};
  const m=statement.match(/^(\w+)=(?:Module\["(\w+)"\]=)?wasmExports\["(\w+)"\](\.value>>>0)?$/);
  assert(m,'Unrecognised generated export assignment: '+statement.slice(0,200));
  const [,local,publicName,symbol,global]=m;
  if(publicName)assert.equal(publicName,symbol==='__main_argc_argv'?'_main':'_'+symbol);
  return {local,publicName,symbol,global:!!global,statement};
});
assert.equal(records.length,105361);
assert.equal(new Set(records.map(r=>r.symbol)).size,records.length);

// Read the actual export table without compiling the 104 MB WASM at build time.
const binary=fs.readFileSync(path.join(lab,'artifacts/toolchain-4.33.1/bin/lean.wasm'));
assert.equal(hash(binary),'e24b3c712f59e983d7c805d5cc3faddd615398e820d27950834c9a3aa9e74151');
let pos=8;
function leb(){let n=0,shift=0,b;do{b=binary[pos++];n+=(b&127)*2**shift;shift+=7;}while(b&128);return n;}
const exportTable=new Map();
while(pos<binary.length){
  const section=binary[pos++],size=leb(),next=pos+size;
  if(section===7){for(let n=leb();n--;){const size=leb(),name=binary.toString('utf8',pos,pos+size);pos+=size;const kind=binary[pos++];leb();exportTable.set(name,kind);}}
  pos=next;
}
for(const r of records){assert(exportTable.has(r.symbol));assert.equal(r.global||false,exportTable.get(r.symbol)===3);}
const publicNames=new Set(records.filter(r=>r.publicName).map(r=>r.symbol));
const excluded=[...exportTable.keys()].filter(name=>!publicNames.has(name));
const retained=records.filter(r=>identifiers.has(r.local));
const compactBlock='var '+[...new Set([...retained.map(r=>r.local),'__indirect_function_table'])].join(',')+';'+
  'function assignWasmExports(wasmExports){'+
  'const excluded=new Set('+JSON.stringify(excluded)+');'+
  'for(const name of Object.keys(wasmExports)){if(excluded.has(name))continue;const value=wasmExports[name];'+
  'Module[name==="__main_argc_argv"?"_main":"_"+name]=value instanceof WebAssembly.Global?value.value>>>0:value;}'+
  retained.map(r=>r.statement+';').join('')+'}';

// Exhaustively compare every published binding and every glue-used local,
// including unsigned global conversions. This runs both assignment functions
// against the same export objects; no Lean theorem is accepted by this test.
const fakeExports=Object.fromEntries([...exportTable].map(([name,kind])=>[name,
  kind===3?new WebAssembly.Global({value:'i32'},-17):function(){}]));
function assign(block){const ctx=vm.createContext({Module:{},WebAssembly,exports:fakeExports});vm.runInContext(block+';assignWasmExports(exports);',ctx);return ctx;}
const original=assign(source.slice(declarations,end)),compact=assign(compactBlock);
assert.deepEqual(Object.keys(compact.Module).sort(),Object.keys(original.Module).sort());
for(const key of Object.keys(original.Module))assert.equal(compact.Module[key],original.Module[key],key);
for(const {local} of retained)assert.equal(compact[local],original[local],local);
const result=source.slice(0,declarations)+compactBlock+source.slice(end);
const output=path.join(lab,'artifacts/lean-browser.js');fs.writeFileSync(output,result);
const report={sourceSha256:hash(source),bytes:Buffer.byteLength(result),sha256:hash(result),exportBindings:publicNames.size,retainedLocals:retained.length};
fs.writeFileSync(path.join(lab,'artifacts/browser-host-checks.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report));
