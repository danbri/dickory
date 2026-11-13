// SPDX-License-Identifier: Apache-2.0
import {McpServer,fromJsonSchema} from '@modelcontextprotocol/server';
import {createNodeDispatcher} from './dispatcher.mjs';
import {resultSchema} from '../../profile/core.js';
export async function createServerFactory(transport='mcp-stdio',config){
 const dispatcher=await createNodeDispatcher(transport,config);
 if(!dispatcher.profile.transports.includes(transport))throw Error('Transport disabled by site profile: '+transport);
 return ()=>{
  const server=new McpServer({name:'dickory-linked-assurance',version:'0.2.0'});
  for(const tool of dispatcher.definitions())server.registerTool(tool.name,{
   description:tool.description,inputSchema:fromJsonSchema(tool.inputSchema),outputSchema:fromJsonSchema(resultSchema),
   annotations:{readOnlyHint:tool.annotations?.readOnlyHint===true,destructiveHint:tool.annotations?.consequentialHint!==false}
  },async(args,context)=>{
   const result=await dispatcher.invoke(tool.name,args,{signal:context?.signal});
   return {structuredContent:result,content:[{type:'text',text:JSON.stringify(result)}],...(result.status!=='completed'?{isError:true}:{})};
  });
  return server;
 };
}
