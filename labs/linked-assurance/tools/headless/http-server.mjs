#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
import {createServer} from 'node:http';
import {pathToFileURL} from 'node:url';
import {createMcpHandler} from '@modelcontextprotocol/server';
import {toNodeHandler,localhostHostValidation,localhostOriginValidation} from '@modelcontextprotocol/node';
import {createServerFactory} from './mcp-factory.mjs';
export async function startHttp({port=0,config}={}){
 if(!Number.isInteger(port)||port<0||port>65535)throw Error('Invalid port');
 const handler=createMcpHandler(await createServerFactory('mcp-http',config));
 const endpoint=toNodeHandler(handler),host=localhostHostValidation(),origin=localhostOriginValidation();
 const server=createServer((req,res)=>{
  if(!host(req,res)||!origin(req,res))return;
  if((req.url||'').split('?')[0]!=='/mcp'){res.writeHead(404).end();return;}
  void Promise.resolve(endpoint(req,res)).catch(()=>{if(!res.headersSent)res.writeHead(500);res.end();});
 });
 await new Promise((resolve,reject)=>{server.once('error',reject);server.listen(port,'127.0.0.1',resolve);});
 return {url:'http://127.0.0.1:'+server.address().port+'/mcp',close:async()=>{
  await handler.close();server.closeAllConnections();await new Promise(r=>server.close(r));
 }};
}
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const server=await startHttp({port:Number(process.env.PORT||'3000')});
 console.error(JSON.stringify({event:'listening',url:server.url,protocol:'2026-07-28',scope:'loopback only; not a public authenticated deployment'}));
 process.on('SIGINT',()=>{void server.close();});process.on('SIGTERM',()=>{void server.close();});
}
