import {runtime,evaluateRdf} from './evidence.js';
self.onmessage=async({data})=>{
  try {
    const api=await import(runtime.module);
    postMessage({kind:'result',result:await evaluateRdf(api,data)});
  } catch(e) {
    postMessage({kind:'result',result:{execution:e.labPhase==='parse'?'parserError':'engineFault',
      claims:[],error:String(e.message||e),errorCode:e.code||null}});
  }
};
