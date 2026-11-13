// SPDX-License-Identifier: Apache-2.0
import {parentPort,threadId,isMainThread} from 'node:worker_threads';
import * as api from '@factoidal/core';
import {evaluateRdf} from '../../evidence.js';
import {normalizeRdf} from '../../headless-contract.js';
const attestation={runtime:'node',node:process.versions.node,executable:process.execPath,threadId,isMainThread,windowType:typeof globalThis.window,documentType:typeof globalThis.document};
parentPort.on('message',async({request})=>{
 try{parentPort.postMessage({kind:'result',observation:normalizeRdf(await evaluateRdf(api,request)),attestation});}
 catch(e){parentPort.postMessage({kind:'result',observation:normalizeRdf({execution:e.labPhase==='parse'?'parserError':'engineFault'}),attestation,diagnostic:String(e.message||e)});}
});
