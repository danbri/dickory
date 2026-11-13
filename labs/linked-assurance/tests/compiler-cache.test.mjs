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
test('streamed assets reject truncation and oversized bodies before cache admission',async()=>{
  const bytes=new Uint8Array([1,2,0,0]),manifest={asset:{url:'./fixture.bin',bytes:bytes.length,sha256:await sha256(bytes)}};
  const response=chunks=>new Response(new ReadableStream({start(c){for(const chunk of chunks)c.enqueue(new Uint8Array(chunk));c.close();}}));
  const good=await loadCompilerAssets(manifest,()=>{},undefined,async()=>response([[1],[2,0],[0]]));
  assert.deepEqual(good.data.asset,bytes);
  await assert.rejects(loadCompilerAssets(manifest,()=>{},undefined,async()=>response([[1,2]])),/checksum mismatch/);
  await assert.rejects(loadCompilerAssets(manifest,()=>{},undefined,async()=>response([[1,2,0,0],[3]])),/checksum mismatch/);
});
test('browser host bytes are verified separately from the pinned upstream compiler identity',async()=>{
  const bytes=new TextEncoder().encode('compact host'),digest=await sha256(bytes);
  const manifest={'lean.js':{url:'./upstream.js',bytes:999,sha256:'upstream-sha',browser:{url:'./compact.js',bytes:bytes.length,sha256:digest}}};
  const result=await loadCompilerAssets(manifest,()=>{},undefined,async url=>{assert(url.pathname.endsWith('/compact.js'));return new Response(bytes);});
  assert.equal(result.compilerSha256['lean.js'],'upstream-sha');assert.equal(result.runtimeSha256['lean.js'],digest);
  assert.equal(result.cache.totalBytes,bytes.length);
  await assert.rejects(loadCompilerAssets(manifest,()=>{},undefined,async()=>new Response('damaged')),/checksum mismatch/);
});
