import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {Client} from '@modelcontextprotocol/client';
import {StdioClientTransport} from '@modelcontextprotocol/client/stdio';

test('MCP v2 stdio lists and executes the actual Node runner',{timeout:120000},async()=>{
  const transport=new StdioClientTransport({
    command:process.execPath,
    args:[fileURLToPath(new URL('../mcp-server.mjs',import.meta.url))],
    stderr:'pipe'
  });
  const client=new Client({name:'linked-assurance-headless-smoke',version:'0.1.0'});
  try{
    await client.connect(transport);
    const listing=await client.listTools();
    assert(listing.tools.some(t=>t.name==='linked_assurance_cases'));
    assert(listing.tools.some(t=>t.name==='linked_assurance_evaluate'));
    assert(listing.tools.some(t=>t.name==='linked_assurance_policy'));
    const reply=await client.callTool({
      name:'linked_assurance_evaluate',
      arguments:{scenario:'vocabulary',variant:'base',scope:'union',
        regime:'RDFS',budgetMs:60000}
    });
    assert.notEqual(reply.isError,true);
    const output=JSON.parse(reply.content.find(p=>p.type==='text').text);
    assert.equal(output.observation.execution,'completed');
    assert.equal(output.observation.claims[0].answer,true);
    assert.equal(output.attestation.runtime,'node');
    assert.equal(output.attestation.documentType,'undefined');
    assert.equal(output.attestation.windowType,'undefined');
    assert(Number.isInteger(output.attestation.threadId)&&output.attestation.threadId>0);
  }finally{await client.close();}
});
