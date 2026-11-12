#!/usr/bin/env node
// Real MCP v2 JSON-RPC server using stdio. stdout is protocol-only.
import {McpServer} from '@modelcontextprotocol/server';
import {serveStdio} from '@modelcontextprotocol/server/stdio';
import * as z from 'zod/v4';
import {listCases} from '../../headless-contract.js';
import {runNodeCase} from './node-runner.mjs';
import {runNativePolicyCase} from './policy-runner.mjs';

void serveStdio(()=>{
  const server=new McpServer({name:'dickory-linked-assurance-node',version:'0.1.0'});
  server.registerTool('linked_assurance_cases',{
    description:'List the available pinned RDF/Lean workbench cases.',
    inputSchema:z.object({})
  },async()=>({content:[{type:'text',text:JSON.stringify({cases:listCases()})}]}));
  server.registerTool('linked_assurance_evaluate',{
    description:'Execute Factoidal RDF entailment in a real Node.js worker thread with a hard deadline. Does not fabricate a policy proof.',
    inputSchema:z.object({
      scenario:z.string().default('vocabulary'),
      variant:z.string().default('base'),
      scope:z.enum(['default','data','ontology','union']).default('union'),
      regime:z.enum(['simple','RDFS']).default('RDFS'),
      budgetMs:z.number().int().min(1).max(120000).default(60000)
    })
  },async input=>{
    try{
      const result=await runNodeCase(input);
      return {content:[{type:'text',text:JSON.stringify(result)}]};
    }catch(e){return {isError:true,content:[{type:'text',text:String(e?.message||e)}]}}
  });
  server.registerTool('linked_assurance_policy',{
    description:'Run a pinned Factoidal RDF case, verify its demonstration credential and execute the real Lean Policy module using the native Lean compiler in Node.',
    inputSchema:z.object({
      scenario:z.string().default('vocabulary'),
      variant:z.string().default('base'),
      scope:z.enum(['default','data','ontology','union']).default('union'),
      regime:z.enum(['simple','RDFS']).default('RDFS'),
      budgetMs:z.number().int().min(1).max(120000).default(60000)
    })
  },async input=>{
    try{
      const result=await runNativePolicyCase(input);
      return {content:[{type:'text',text:JSON.stringify(result)}]};
    }catch(e){return {isError:true,content:[{type:'text',text:String(e?.message||e)}]}}
  });
  return server;
});
