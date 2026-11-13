// SPDX-License-Identifier: Apache-2.0
// WebMCP Draft 2026-11-12. No navigator aliases, emulation or network fallback.
import {resultSchema} from './core.js';
export async function registerWebMCP(dispatcher,{context=globalThis.document?.modelContext,exposedTo=[]}={}){
 if(!context||typeof context.registerTool!=='function')return {registered:false,reason:'native_webmcp_unavailable'};
 // Cross-origin exposure is an explicit host decision; default is same-origin.
 if(!Array.isArray(exposedTo)||exposedTo.some(o=>{try{const u=new URL(o);return u.origin!==o||u.protocol!=='https:'}catch{return true}}))throw Error('exposedTo must contain exact HTTPS origins');
 const controller=new AbortController(),names=[];
 try{
  for(const t of dispatcher.definitions()){
   if(!dispatcher.profile.transports.includes('webmcp'))break;
   await context.registerTool({name:t.name,description:t.description,inputSchema:t.inputSchema,outputSchema:resultSchema,
    annotations:{readOnlyHint:t.annotations?.readOnlyHint===true,untrustedContentHint:t.annotations?.untrustedContentHint!==false,consequentialHint:t.annotations?.consequentialHint!==false,debugging:t.annotations?.debugging===true},
    execute:(args,options)=>dispatcher.invoke(t.name,args,options)},
    {signal:controller.signal,...(exposedTo.length?{exposedTo}: {})});
   names.push(t.name);
  }
  return {registered:true,names,dispose:()=>controller.abort()};
 }catch(e){controller.abort();throw e;}
}
export async function invokeNativeWebMCP(name,args,{context=globalThis.document?.modelContext,signal}={}){
 if(!context?.getTools||!context?.executeTool)throw Error('native_webmcp_unavailable');
 const list=await context.getTools(),tool=list.find(t=>t.name===name&&(!t.origin||t.origin===globalThis.location?.origin));
 if(!tool)throw Error('native_webmcp_tool_unavailable: '+name);
 const raw=await context.executeTool(tool,args,{signal});
 if(typeof raw!=='string')throw Error('Native WebMCP returned a non-string result');
 return JSON.parse(raw);
}
