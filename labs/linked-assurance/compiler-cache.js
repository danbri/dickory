import {sha256} from './evidence.js';

const cacheName='linked-assurance-lean-assets-v1';
const mb=n=>(n/1e6).toFixed(0)+' MB';
let prepared;
const listeners=new Set();
export function onCompilerDownload(listener){listeners.add(listener);return ()=>listeners.delete(listener);}
export async function prepareCompilerFiles(progress=()=>{}){
  const notify=message=>{progress(message);for(const listener of listeners)listener(message);};
  if(!prepared)prepared=(async()=>{
    const response=await fetch(new URL('./compiler-assets.json',import.meta.url));
    if(!response.ok)throw Error('Compiler manifest unavailable.');
    return loadCompilerAssets(await response.json(),notify);
  })().catch(e=>{prepared=null;throw e;});
  const result=await prepared;
  notify(result.cache.persistentCacheAvailable?'Lean 4.33.1 files ready · saved on this device.':'Lean 4.33.1 files ready for this tab · browser storage unavailable.');
  return result;
}
export async function compilerFilesSaved(){
  try{
    const response=await fetch(new URL('./compiler-assets.json',import.meta.url));
    if(!response.ok)return false;
    const manifest=await response.json(),cache=await globalThis.caches?.open(cacheName);
    if(!cache)return false;
    const keys=new Set((await cache.keys()).map(r=>r.url));
    return Object.values(manifest).every(asset=>keys.has(new URL('./__lean_cache__/'+(asset.browser||asset).sha256,import.meta.url).href));
  }catch{return false;}
}

// The Cache API keeps verified assets across visits. Drop this tab's raw copies
// once the caller has made its runtime blobs/library, or only wanted a download.
export function releasePreparedCompilerFiles(){prepared=null;}

// Content-addressed keys allow a new manifest to reuse unchanged assets. A
// cached response is still checked against the current pinned manifest.
export async function loadCompilerAssets(manifest,progress=()=>{},storage=globalThis.caches,fetcher=globalThis.fetch) {
  let cache;
  try {cache=await storage?.open(cacheName);}catch{/* Private mode / quota: run without disk caching. */}
  const runtime=Object.fromEntries(Object.entries(manifest).map(([name,a])=>[name,a.browser||a]));
  const total=Object.values(runtime).reduce((n,a)=>n+a.bytes,0),loaded=new Map();
  let downloaded=0,cached=0,cacheWritable=!!cache;
  const entries=[];
  for(const [name,a] of Object.entries(runtime))entries.push(await(async()=>{
    const url=new URL(a.url,import.meta.url),key=new URL('./__lean_cache__/'+a.sha256,import.meta.url).href;
    const valid=async bytes=>bytes.length===a.bytes && await sha256(bytes)===a.sha256;
    const hit=await cache?.match(key).catch(()=>null);
    if(hit){
      const bytes=new Uint8Array(await hit.arrayBuffer());
      if(await valid(bytes)){cached+=bytes.length;progress('Loading saved compiler: '+name+' ('+mb(bytes.length)+')');return [name,bytes];}
      await cache.delete(key).catch(()=>{});
      progress('Replacing a damaged saved compiler file: '+name);
    }
    const response=await fetcher(url);
    if(!response.ok)throw Error('Compiler asset unavailable: '+name);
    const bytes=new Uint8Array(a.bytes);let length=0,last=0;
    if(response.body){
      const reader=response.body.getReader();
      while(true){
        const {done,value}=await reader.read();if(done)break;
        if(length+value.length>bytes.length){await reader.cancel();throw Error('Compiler asset checksum mismatch: '+name+' (unexpected size)');}
        bytes.set(value,length);length+=value.length;loaded.set(name,length);
        if(Date.now()-last>400){last=Date.now();progress('Downloading compiler: '+mb([...loaded.values()].reduce((a,b)=>a+b,0))+' downloaded / '+mb(total)+' total (saved files reused)');}
      }
    }else{const value=new Uint8Array(await response.arrayBuffer());length=value.length;if(length===bytes.length)bytes.set(value);}
    progress('Checking compiler integrity: '+name);
    if(length!==a.bytes||!await valid(bytes))throw Error('Compiler asset checksum mismatch: '+name);
    downloaded+=bytes.length;
    if(cache)try{await cache.put(key,new Response(bytes,{headers:{'Content-Type':'application/octet-stream'}}));}catch{cacheWritable=false;}
    return [name,bytes];
  })());
  progress(cached===total?'Compiler files loaded from this device; integrity checks passed.':
    cacheWritable?'Compiler files verified and saved on this device.':'Compiler files verified; browser storage unavailable. Files may download again next visit.');
  return {data:Object.fromEntries(entries),compilerSha256:Object.fromEntries(Object.entries(manifest).map(([name,asset])=>[name,asset.sha256])),runtimeSha256:Object.fromEntries(Object.entries(runtime).map(([name,asset])=>[name,asset.sha256])),cache:{downloadedBytes:downloaded,cachedBytes:cached,totalBytes:total,persistentCacheAvailable:cacheWritable}};
}

export async function clearCompilerCache(){prepared=null;await globalThis.caches?.delete(cacheName);}
