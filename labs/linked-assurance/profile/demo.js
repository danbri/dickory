import {defineProfile,createDispatcher} from './core.js';
import {registerWebMCP,invokeNativeWebMCP} from './webmcp.js';
const profile=defineProfile({id:'example-site',transports:['webmcp'],tools:[{
 name:'example_site.describe',description:'Describe the text supplied by the caller.',requires:[],
 inputSchema:{type:'object',properties:{text:{type:'string',maxLength:200},includeLength:{type:'boolean',default:true}},required:['text'],additionalProperties:false}
}]});
const dispatcher=createDispatcher({profile,transport:'webmcp',handlers:{
 'example_site.describe':({text,includeLength})=>({text,...(includeLength?{length:[...text].length}:{})})
}});
const show=r=>document.getElementById('out').textContent=JSON.stringify(r,null,2);
const registration=await registerWebMCP(dispatcher);show({profile:dispatcher.describe(),nativeWebMCP:registration.registered});
document.getElementById('call').onclick=async()=>show(await dispatcher.invoke('example_site.describe',{text:document.getElementById('text').value}));
document.getElementById('native').onclick=async()=>{try{show(await invokeNativeWebMCP('example_site.describe',{text:document.getElementById('text').value}));}catch(e){show({status:'unsupported',error:String(e)});}};
