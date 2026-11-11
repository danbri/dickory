import test from 'node:test';
import assert from 'node:assert/strict';
import {loadCompilerAssets} from '../compiler-cache.js';
import {sha256} from '../evidence.js';

test('compiler cache avoids repeat downloads, checks cached bytes and replaces damage',async()=>{
  const bytes=new TextEncoder().encode('small fixture'),manifest={asset:{url:'./fixture.bin',bytes:bytes.length,sha256:await sha256(bytes)}};
  const saved=new Map(),storage={open:async()=>({match:async k=>saved.get(k)?.clone(),put:async(k,r)=>saved.set(k,r),delete:async k=>saved.delete(k)})};
  let downloads=0;const fetcher=async()=>{downloads++;return new Response(bytes);};
  const first=await loadCompilerAssets(manifest,()=>{},storage,fetcher);assert.equal(first.cache.downloadedBytes,bytes.length);
  const second=await loadCompilerAssets(manifest,()=>{},storage,fetcher);assert.equal(second.cache.cachedBytes,bytes.length);assert.equal(downloads,1);
  saved.set([...saved.keys()][0],new Response('bad bytes'));
  await loadCompilerAssets(manifest,()=>{},storage,fetcher);assert.equal(downloads,2);
  saved.clear();await assert.rejects(loadCompilerAssets(manifest,()=>{},storage,async()=>new Response('wrong download')),/checksum mismatch/);assert.equal(saved.size,0);
});
test('compiler still loads when persistent storage is unavailable',async()=>{
  const bytes=new TextEncoder().encode('fixture'),manifest={asset:{url:'./fixture.bin',bytes:bytes.length,sha256:await sha256(bytes)}};
  const result=await loadCompilerAssets(manifest,()=>{},{open:async()=>{throw Error('quota');}},async()=>new Response(bytes));
  assert.equal(result.cache.persistentCacheAvailable,false);assert.deepEqual(result.data.asset,bytes);
});
