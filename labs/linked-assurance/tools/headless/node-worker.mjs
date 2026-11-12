// Real Node worker thread: no DOM, not a simulated browser.
import {parentPort,threadId,isMainThread} from 'node:worker_threads';
import * as api from '@factoidal/core';
import {evaluateRdf} from '../../evidence.js';
import {normalizeRdf} from '../../headless-contract.js';

parentPort.on('message',async({request})=>{
  try{
    const result=await evaluateRdf(api,request);
    parentPort.postMessage({
      kind:'result',observation:normalizeRdf(result),
      attestation:{runtime:'node',node:process.versions.node,
        executable:process.execPath,threadId,isMainThread,
        windowType:typeof globalThis.window,documentType:typeof globalThis.document}
    });
  }catch(e){
    parentPort.postMessage({
      kind:'result',
      observation:normalizeRdf({execution:e.labPhase==='parse'?'parserError':'engineFault'}),
      attestation:{runtime:'node',node:process.versions.node,
        executable:process.execPath,threadId,isMainThread,
        windowType:typeof globalThis.window,documentType:typeof globalThis.document},
      diagnostic:String(e?.message||e)
    });
  }
});
