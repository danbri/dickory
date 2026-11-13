#!/usr/bin/env node
// SPDX-License-Identifier: Apache-2.0
import fs from 'node:fs/promises';
import {fileURLToPath} from 'node:url';
import {Client,StreamableHTTPClientTransport} from '@modelcontextprotocol/client';
import {StdioClientTransport} from '@modelcontextprotocol/client/stdio';
import {createNodeDispatcher} from './dispatcher.mjs';
import {PROTOCOLS} from '../../profile/core.js';
const opts={backend:'node',tool:'linked_assurance_cases'};
for(let i=2;i<process.argv.length;i+=2){const k=process.argv[i]?.slice(2);if(!['backend','tool','input','url'].includes(k)||!process.argv[i+1])throw Error('Use --backend node|mcp-stdio|mcp-http --tool NAME --input FILE.json');opts[k]=process.argv[i+1];}
const args=opts.input?JSON.parse(await fs.readFile(opts.input,'utf8')):{};
let client;
try{
 let result;
 if(opts.backend==='node')result=await(await createNodeDispatcher()).invoke(opts.tool,args);
 else{
  client=new Client({name:'dickory-profile-cli',version:'0.2.0'},{versionNegotiation:{mode:{pin:PROTOCOLS.mcp}}});
  let transport;
  if(opts.backend==='mcp-stdio')transport=new StdioClientTransport({command:process.execPath,args:[fileURLToPath(new URL('./mcp-server.mjs',import.meta.url))],stderr:'inherit'});
  else if(opts.backend==='mcp-http')transport=new StreamableHTTPClientTransport(new URL(opts.url||'http://127.0.0.1:3000/mcp'));
  else throw Error('Unknown backend. The Chromium CLI is tools/viewer-browser/linked-headless.mjs');
  await client.connect(transport);
  if(client.getProtocolEra()!=='modern')throw Error('Modern MCP negotiation required');
  const reply=await client.callTool({name:opts.tool,arguments:args});
  result=reply.structuredContent||{status:'transport_error',response:reply};
 }
 process.stdout.write(JSON.stringify(result)+'\n');if(result.status!=='completed')process.exitCode=1;
}catch(e){process.stderr.write(String(e)+'\n');process.exitCode=1;}finally{await client?.close();}
