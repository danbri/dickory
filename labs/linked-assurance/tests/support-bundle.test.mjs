import test from 'node:test';
import assert from 'node:assert/strict';
import {installSupportBundle} from '../lean-host.js';
import {sha256} from '../evidence.js';

test('fixed support transport rejects stale or damaged bundles before installing any file',async()=>{
  // Small transport fixture; actual module import and proof checks run in browsers.
  const bytes=new Uint8Array([1,2,3]),sourceSha256=await sha256('support source');
  const compilerSha256={'lean.wasm':await sha256('pinned compiler')};
  const original={status:'pass',sourceSha256,compilerSha256,files:[
    {name:'Workbench.olean',bytes:bytes.length,sha256:await sha256(bytes),base64:Buffer.from(bytes).toString('base64')}
  ]};
  const host=()=>({compilerSha256,libraryFiles:new Map()});
  const good=host();await installSupportBundle(good,original,sourceSha256);
  assert.deepEqual(good.libraryFiles.get('Workbench.olean'),bytes);assert.equal(good.supportSha256,sourceSha256);
  for(const mutate of [
    b=>b.status='fail',b=>b.sourceSha256='stale',b=>b.compilerSha256['lean.wasm']='wrong compiler',
    b=>b.files[0].sha256='damaged',b=>b.files[0].bytes++,b=>b.files[0].name='../Workbench.olean',
    b=>b.files.push({...b.files[0]}),b=>b.files=[],
    b=>b.files.push({...b.files[0],name:'Workbench.ir',sha256:'damaged second file'})
  ]){
    const bundle=structuredClone(original),lean=host();mutate(bundle);
    await assert.rejects(installSupportBundle(lean,bundle,sourceSha256));
    assert.equal(lean.libraryFiles.size,0);assert.equal(lean.supportSha256,undefined);
  }
});
