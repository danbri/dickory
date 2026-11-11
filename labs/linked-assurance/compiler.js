import {gunzipSync} from './vendor/fflate.js';
import {sha256} from './evidence.js';

function untar(data){
  const files=new Map(),decode=new TextDecoder();
  const text=b=>decode.decode(b).split('\0')[0];
  for(let i=0;i+512<=data.length;){
    const h=data.subarray(i,i+512);if(h.every(b=>b===0))break;
    let name=text(h.subarray(0,100));const prefix=text(h.subarray(345,500));if(prefix)name=prefix+'/'+name;
    const size=parseInt(text(h.subarray(124,136)).trim(),8)||0;i+=512;
    if(name.startsWith('/')||name.split('/').includes('..')||i+size>data.length)throw Error('Invalid compiler library archive');
    if(h[156]===48||h[156]===0)files.set(name.replace(/^\.\//,''),data.slice(i,i+size));
    i+=Math.ceil(size/512)*512;
  }
  return files;
}
export class Lean4 {
  constructor({onProgress=()=>{},timeout=180000}={}){this.onProgress=onProgress;this.timeout=timeout;this.workers=new Set();this.libraryFiles=new Map();}
  async init(){
    const manifest=await (await fetch(new URL('./compiler-assets.json',import.meta.url))).json();
    const entries=await Promise.all(Object.entries(manifest).map(async([name,a])=>{
      this.onProgress('Loading Lean 4.33.1: '+name);
      const response=await fetch(new URL(a.url,import.meta.url));if(!response.ok)throw Error('Compiler asset unavailable: '+name);
      const bytes=new Uint8Array(await response.arrayBuffer());
      if(bytes.length!==a.bytes||await sha256(bytes)!==a.sha256)throw Error('Compiler asset checksum mismatch: '+name);
      return [name,bytes];
    }));
    const data=Object.fromEntries(entries);
    this.jsUrl=URL.createObjectURL(new Blob([data['lean.js']],{type:'text/javascript'}));
    this.wasmUrl=URL.createObjectURL(new Blob([data['lean.wasm']],{type:'application/wasm'}));
    this.libraryFiles=untar(gunzipSync(data['lean-lib.tar.gz']));
    const header=new TextDecoder().decode(this.libraryFiles.get('Init.olean')?.subarray(0,88));
    if(!header.includes('4.33.1')||!header.includes('4f9018a62ead9be0ffd652021d5afc8501e92253'))throw Error('Mismatched Init library');
  }
  spawn(config){
    const worker=new Worker(new URL('./compiler-worker.js',import.meta.url));this.workers.add(worker);
    const files=[...this.libraryFiles].map(([name,data])=>({name,data:data.slice()}));
    worker.postMessage({type:'boot',jsUrl:this.jsUrl,wasmUrl:this.wasmUrl,files,...config},files.map(f=>f.data.buffer));
    return worker;
  }
  stop(worker){worker.terminate();this.workers.delete(worker);}
  wait(worker,kind){
    return new Promise((resolve,reject)=>{
      const timer=setTimeout(()=>{cleanup();this.stop(worker);if(this.session===worker)this.session=null;reject(Error('Lean compiler timeout; worker terminated'));},this.timeout);
      const cleanup=()=>{clearTimeout(timer);worker.removeEventListener('message',message);worker.removeEventListener('error',error);};
      const error=e=>{cleanup();this.stop(worker);if(this.session===worker)this.session=null;reject(Error(e.message||e.error||'Compiler worker failed'));};
      const message=({data})=>{if(data.type==='error')error(data);else if(data.type===kind){cleanup();resolve(data);}};
      worker.addEventListener('message',message);worker.addEventListener('error',error);
    });
  }
  async run(source,{moduleName='Input',exportPrefix,flags=['--json'],persistent=false}={}){
    const path='/workspace/'+moduleName+'.lean';let worker;
    if(persistent){
      if(!this.session){worker=this.spawn({persistent:true});await this.wait(worker,'ready');this.session=worker;}
      worker=this.session;const pending=this.wait(worker,'result');worker.postMessage({type:'compile',source,path});
      return this.result(await pending);
    }
    worker=this.spawn({source,path,exportPrefix,flags,persistent:false});
    try{return this.result(await this.wait(worker,'result'));}finally{this.stop(worker);}
  }
  result(r){
    if(r.exitCode===0)for(const f of r.artifacts)this.libraryFiles.set(f.name,new Uint8Array(f.data));
    return {...r,artifacts:r.artifacts.map(f=>f.name)};
  }
  resetSession(){if(this.session){this.stop(this.session);this.session=null;}}
  dispose(){for(const worker of this.workers)worker.terminate();this.workers.clear();this.session=null;
    if(this.jsUrl)URL.revokeObjectURL(this.jsUrl);if(this.wasmUrl)URL.revokeObjectURL(this.wasmUrl);}
}
