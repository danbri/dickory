// SPDX-License-Identifier: Apache-2.0
// Transport-independent developer profile. This is NOT a new MCP protocol.
export const PROFILE_VERSION = 'dickory-tool-profile/1';
export const PROTOCOLS = Object.freeze({mcp:'2026-07-28',webmcpSnapshot:'2026-11-12'});
const owns=(o,k)=>Object.prototype.hasOwnProperty.call(o,k);
const plain=o=>o!==null&&typeof o==='object'&&!Array.isArray(o)&&
  [Object.prototype,null].includes(Object.getPrototypeOf(o));
const forbidden=new Set(['__proto__','constructor','prototype']);
const keywords=new Set(['type','properties','required','additionalProperties','items',
  'enum','minimum','maximum','minLength','maxLength','minItems','maxItems','description','title','default']);
const clone=x=>JSON.parse(JSON.stringify(x));
function fail(path,why){throw new TypeError(path+': '+why);}
function checkSchema(s,path='$',depth=0){
  if(depth>16||!plain(s))fail(path,'schema must be a bounded object');
  for(const k of Object.keys(s))if(!keywords.has(k))fail(path,'unsupported schema keyword '+k);
  if(!['object','array','string','integer','number','boolean','null'].includes(s.type))fail(path,'unsupported type');
  if(s.enum&&(!Array.isArray(s.enum)||!s.enum.length||s.enum.some(x=>x!==null&&typeof x==='object')))fail(path,'enum must contain primitive values');
  if(s.type==='object'){
    if(!plain(s.properties)||s.additionalProperties!==false)fail(path,'objects require properties and additionalProperties:false');
    const keys=Object.keys(s.properties);
    if(keys.length>100||keys.some(k=>forbidden.has(k)))fail(path,'invalid property names/count');
    if(s.required!==undefined&&(!Array.isArray(s.required)||new Set(s.required).size!==s.required.length||s.required.some(k=>!keys.includes(k))))fail(path,'invalid required list');
    for(const k of keys){
      checkSchema(s.properties[k],path+'.'+k,depth+1);
      if(s.required?.includes(k)&&owns(s.properties[k],'default'))fail(path+'.'+k,'required fields cannot have defaults in this profile');
    }
  }
  if(s.type==='array')checkSchema(s.items,path+'[]',depth+1);
  for(const key of ['minimum','maximum','minLength','maxLength','minItems','maxItems']){
    if(owns(s,key)&&(!Number.isFinite(s[key])||(['minLength','maxLength','minItems','maxItems'].includes(key)&&(!Number.isSafeInteger(s[key])||s[key]<0))))fail(path,'invalid '+key);
  }
  for(const [min,max] of [['minimum','maximum'],['minLength','maxLength'],['minItems','maxItems']])if(owns(s,min)&&owns(s,max)&&s[min]>s[max])fail(path,'inverted bounds');
  if(owns(s,'default'))decode(s,s.default,path,depth);
}
export function decode(schema,value,path='$',depth=0){
  if(depth>32)fail(path,'input nesting exceeds profile limit');
  let out;
  switch(schema.type){
    case 'object': {
      if(!plain(value))fail(path,'expected named argument object');
      if(Object.keys(value).some(k=>!owns(schema.properties,k)))fail(path,'unknown argument');
      out={};
      for(const key of Object.keys(schema.properties).sort()){
        const field=schema.properties[key];
        if(owns(value,key))out[key]=decode(field,value[key],path+'.'+key,depth+1);
        else if(schema.required?.includes(key))fail(path+'.'+key,'missing required argument');
        else if(owns(field,'default'))out[key]=decode(field,clone(field.default),path+'.'+key,depth+1);
      }
      break;
    }
    case 'array':
      if(!Array.isArray(value))fail(path,'expected array');
      if(value.length<(schema.minItems??0)||value.length>(schema.maxItems??100000))fail(path,'array bounds');
      out=Array.from(value,(x,i)=>decode(schema.items,x,path+'['+i+']',depth+1));break;
    case 'string':
      if(typeof value!=='string')fail(path,'expected string');
      if([...value].length<(schema.minLength??0)||[...value].length>(schema.maxLength??1000000))fail(path,'string bounds');
      out=value;break;
    case 'number':case 'integer':
      if(typeof value!=='number'||!Number.isFinite(value)||(schema.type==='integer'&&!Number.isSafeInteger(value)))fail(path,'expected finite '+schema.type);
      if(value<(schema.minimum??-Infinity)||value>(schema.maximum??Infinity))fail(path,'numeric bounds');
      out=Object.is(value,-0)?0:value;break;
    case 'boolean':if(typeof value!=='boolean')fail(path,'expected boolean');out=value;break;
    case 'null':if(value!==null)fail(path,'expected null');out=null;break;
    default:fail(path,'unsupported schema');
  }
  if(schema.enum&&!schema.enum.some(v=>v===out))fail(path,'value outside enum');
  return out;
}
function freeze(x){if(x&&typeof x==='object'){Object.values(x).forEach(freeze);Object.freeze(x);}return x;}
export function defineProfile({id,tools,enabledTools,transports=['mcp-stdio','mcp-http','webmcp'],maxInputBytes=1048576,maxBudgetMs=120000}){
  if(typeof id!=='string'||!id||!Array.isArray(tools)||tools.length>100)throw TypeError('Invalid profile');
  if(!Number.isSafeInteger(maxBudgetMs)||maxBudgetMs<1||maxBudgetMs>120000)throw TypeError('Invalid computation budget');
  if(!Number.isSafeInteger(maxInputBytes)||maxInputBytes<1)throw TypeError('Invalid input byte limit');
  if(!Array.isArray(transports)||new Set(transports).size!==transports.length||transports.some(t=>!['mcp-stdio','mcp-http','webmcp','local-cli'].includes(t)))throw TypeError('Invalid transport selection');
  const names=new Set();
  for(const tool of tools){
    if(!/^[A-Za-z0-9_.-]{1,128}$/.test(tool.name)||names.has(tool.name)||typeof tool.description!=='string'||!tool.description)throw TypeError('Invalid/duplicate tool');
    names.add(tool.name);checkSchema(tool.inputSchema);
    if(tool.budgetField&&(!owns(tool.inputSchema.properties||{},tool.budgetField)||tool.inputSchema.properties[tool.budgetField].type!=='integer'))throw TypeError('budgetField must name an integer parameter');
    if(tool.inputSchema.type!=='object')throw TypeError('Top-level arguments must be named');
    if(!Array.isArray(tool.requires)||tool.requires.some(k=>typeof k!=='string'||!k))throw TypeError('Invalid capabilities');
  }
  const enabled=enabledTools??[...names];
  if(!Array.isArray(enabled)||new Set(enabled).size!==enabled.length||enabled.some(n=>!names.has(n)))throw TypeError('Unknown/duplicate enabled tool');
  // Snapshot host-owned configuration; callers cannot change exposure after creation.
  return freeze(clone({version:PROFILE_VERSION,id,tools:tools.filter(t=>enabled.includes(t.name)),transports,maxInputBytes,maxBudgetMs}));
}
export const resultSchema={type:'object',properties:{
  profile:{type:'string'},tool:{type:'string'},status:{type:'string',enum:['completed','invalid_request','unsupported','cancelled','tool_error']},
  result:{type:'object'},error:{type:'object'},runtime:{type:'object'}
},required:['profile','tool','status','runtime']};
export function createDispatcher({profile,transport,capabilities=[],handlers,runtime={}}){
  const capable=new Set(capabilities),allowed=profile.transports.includes(transport);
  const available=t=>allowed&&t.requires.every(c=>capable.has(c))&&typeof handlers[t.name]==='function';
  const definitions=()=>profile.tools.map(t=>({...clone(t),available:available(t)}));
  const envelope=(tool,status,body)=>({profile:profile.version+':'+profile.id,tool,status,...body,runtime:{...runtime,transport}});
  return {
    profile,definitions,
    describe:()=>({id:profile.id,version:profile.version,protocols:PROTOCOLS,transport,capabilities:[...capable].sort(),tools:definitions()}),
    async invoke(name,input={},options={}){
      const t=profile.tools.find(t=>t.name===name);
      const error=(status,code,message)=>envelope(name,status,{error:{code,message}});
      if(!t||!available(t))return error('unsupported','unavailable','Tool is not enabled or its required capabilities are unavailable');
      if(options.signal?.aborted)return error('cancelled','aborted','Request cancelled before execution');
      let args;
      try{
        const bytes=new TextEncoder().encode(JSON.stringify(input)).length;
        if(bytes>profile.maxInputBytes)throw TypeError('Input exceeds profile byte limit');
        args=decode(t.inputSchema,input);
        if(t.budgetField&&(!Number.isSafeInteger(args[t.budgetField])||args[t.budgetField]>profile.maxBudgetMs))throw TypeError('Requested budget exceeds site profile');
      }catch(e){return error('invalid_request','invalid_arguments',String(e.message||e));}
      try{
        const result=await handlers[name](args,options);
        if(options.signal?.aborted)return error('cancelled','aborted','Request cancelled; late result discarded');
        if(!plain(result))throw Error('Tool must return an object');
        // No Promise.race here: cancellation is cooperative. Killable workers
        // implement hard budgets and report timeout in their application result.
        return envelope(name,'completed',{result});
      }catch(e){return options.signal?.aborted?error('cancelled','aborted','Request cancelled'):error('tool_error','execution_failed',String(e.message||e));}
    }
  };
}
