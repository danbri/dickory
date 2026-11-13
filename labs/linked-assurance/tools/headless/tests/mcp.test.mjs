import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {Client,StreamableHTTPClientTransport} from '@modelcontextprotocol/client';
import {StdioClientTransport} from '@modelcontextprotocol/client/stdio';
import {startHttp} from '../http-server.mjs';
import {workbenchProfile} from '../../../profile/catalogue.js';
import {PROTOCOLS} from '../../../profile/core.js';
for(const binding of ['stdio','http'])test('MCP '+PROTOCOLS.mcp+' pinned over '+binding,{timeout:120000},async()=>{
 let http;
 const client=new Client({name:'dickory-modern-conformance',version:'0.2.0'},{versionNegotiation:{mode:{pin:PROTOCOLS.mcp}}});
 try{
  const transport=binding==='stdio'?new StdioClientTransport({command:process.execPath,args:[fileURLToPath(new URL('../mcp-server.mjs',import.meta.url))],stderr:'pipe'}):new StreamableHTTPClientTransport(new URL((http=await startHttp()).url));
  await client.connect(transport);assert.equal(client.getProtocolEra(),'modern','A successful legacy handshake is NOT this test');
  const list=await client.listTools();
  for(const def of workbenchProfile().tools){const found=list.tools.find(t=>t.name===def.name);assert(found);assert.deepEqual(found.inputSchema.properties,def.inputSchema.properties);}
  const r=await client.callTool({name:'linked_assurance_evaluate',arguments:{scenario:'vocabulary',scope:'union',regime:'RDFS',budgetMs:60000}});
  assert.notEqual(r.isError,true);const out=r.structuredContent;
  assert.equal(out.status,'completed');assert.equal(out.result.observation.execution,'completed');
  assert.equal(out.result.attestation.runtime,'node');assert.equal(out.result.attestation.documentType,'undefined');
  const bad=await client.callTool({name:'linked_assurance_evaluate',arguments:{scope:'typo'}}).catch(()=>({isError:true}));assert.equal(bad.isError,true);
 }finally{await client.close();await http?.close();}
});
test('HTTP is loopback with origin validation',{timeout:10000},async()=>{
 const server=await startHttp();
 try{const r=await fetch(server.url,{method:'POST',headers:{origin:'https://untrusted.example','content-type':'application/json'},body:'{}'});assert(r.status>=400);}
 finally{await server.close();}
});
