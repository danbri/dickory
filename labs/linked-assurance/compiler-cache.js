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
    return Object.values(manifest).every(a=>keys.has(new URL('./__lean_cache__/'+a.sha256,import.meta.url).href));
  }catch{return false;}
}

// Content-addressed keys allow a new manifest to reuse unchanged assets. A
// cached response is still checked against the current pinned manifest.
export async function loadCompilerAssets(manifest,progress=()=>{},storage=globalThis.caches,fetcher=globalThis.fetch) {
  let cache;
  try {cache=await storage?.open(cacheName);}catch{/* Private mode / quota: run without disk caching. */}
  const total=Object.values(manifest).reduce((n,a)=>n+a.bytes,0),loaded=new Map();
  let downloaded=0,cached=0,cacheWritable=!!cache;
  const entries=await Promise.all(Object.entries(manifest).map(async([name,a])=>{
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
    const chunks=[];let length=0,last=0;
    if(response.body){
      const reader=response.body.getReader();
      while(true){
        const {done,value}=await reader.read();if(done)break;
        chunks.push(value);length+=value.length;loaded.set(name,length);
        if(Date.now()-last>400){last=Date.now();progress('Downloading compiler: '+mb([...loaded.values()].reduce((a,b)=>a+b,0))+' downloaded / '+mb(total)+' total (saved files reused)');}
      }
    }else{const value=new Uint8Array(await response.arrayBuffer());chunks.push(value);length=value.length;}
    const bytes=new Uint8Array(length);let offset=0;
    for(const chunk of chunks){bytes.set(chunk,offset);offset+=chunk.length;}
    progress('Checking compiler integrity: '+name);
    if(!await valid(bytes))throw Error('Compiler asset checksum mismatch: '+name);
    downloaded+=bytes.length;
    if(cache)try{await cache.put(key,new Response(bytes,{headers:{'Content-Type':'application/octet-stream'}}));}catch{cacheWritable=false;}
    return [name,bytes];
  }));
  progress(cached===total?'Compiler files loaded from this device; integrity checks passed.':
    cacheWritable?'Compiler files verified and saved on this device.':'Compiler files verified; browser storage unavailable. Files may download again next visit.');
  return {data:Object.fromEntries(entries),cache:{downloadedBytes:downloaded,cachedBytes:cached,totalBytes:total,persistentCacheAvailable:cacheWritable}};
}

export async function clearCompilerCache(){prepared=null;await globalThis.caches?.delete(cacheName);}
