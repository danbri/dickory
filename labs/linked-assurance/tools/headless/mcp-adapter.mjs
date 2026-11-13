// SPDX-License-Identifier: Apache-2.0
// Generic site adapter; no Factoidal, Lean runtime or catalogue dependency.
import {McpServer,fromJsonSchema} from '@modelcontextprotocol/server';
import {resultSchema} from '../../profile/core.js';
export function mcpFactory(dispatcher,{name=dispatcher.profile.id,version='0.2.0'}={}){
 return ()=>{
  const server=new McpServer({name,version});
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
