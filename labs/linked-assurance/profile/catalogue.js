// SPDX-License-Identifier: Apache-2.0
import {defineProfile,PROTOCOLS} from './core.js';
import {sourceTool} from './lean-source.js';
export {PROTOCOLS};
const object=(properties,required=[])=>({type:'object',properties,required,additionalProperties:false});
const enumeration=(values,value)=>({type:'string',enum:values,default:value});
export const caseInput=object({
  scenario:{type:'string',minLength:1,maxLength:80,default:'vocabulary'},
  variant:{type:'string',minLength:1,maxLength:80,default:'base'},
  scope:enumeration(['default','data','ontology','union'],'union'),
  regime:enumeration(['simple','RDFS'],'RDFS'),
  budgetMs:{type:'integer',minimum:1,maximum:120000,default:10000}
});
export const policyInput=object({...caseInput.properties,
  state:{...object({
    clock:{type:'string',maxLength:40,default:'2026-11-11T12:00:00Z'},
    secureTransportObserved:{type:'boolean',default:true},
    permissionGranted:{type:'boolean',default:true},
    attackerWantsInterruption:{type:'boolean',default:false},
    legitimateSession:{type:'boolean',default:false},
    credentialPayload:{type:'string',maxLength:65536},
    credentialSignature:{type:'string',maxLength:4096}
  }),default:{}}
});
const fixedTools=[
  {name:'linked_assurance_cases',description:'List the pinned RDF/Lean workbench cases.',inputSchema:object({}),requires:[]},
  {name:'linked_assurance_evaluate',description:'Run scoped RDF evaluation; timeout and parse failure are not negative semantic answers.',inputSchema:caseInput,requires:['rdf'],budgetField:'budgetMs'},
  {name:'linked_assurance_check_policy',description:'Check the fixed Policy.lean and its contract. This tool does not accept arbitrary untrusted Lean code.',inputSchema:object({}),requires:['lean-policy']},
  {name:'linked_assurance_policy',description:'Run scoped RDF evaluation, an explicit credential/state bundle and the checked Lean policy. A completed call may return deny, defer or attacker success.',inputSchema:policyInput,requires:['rdf','lean-policy'],budgetField:'budgetMs'}
].map(t=>({...t,annotations:{readOnlyHint:true,consequentialHint:false,untrustedContentHint:true,debugging:true}}));
export const tools=[...fixedTools,sourceTool];
// Compiling caller-supplied code is deliberately not enabled by a dependency update.
export const defaultConfig={id:'linked-assurance',enabledTools:fixedTools.map(t=>t.name),
  transports:['local-cli','mcp-stdio','mcp-http','webmcp'],maxInputBytes:1048576,maxBudgetMs:120000};
export function workbenchProfile(config={}){
  const allowed=new Set(Object.keys(defaultConfig));
  if(!config||typeof config!=='object'||Array.isArray(config)||Object.keys(config).some(k=>!allowed.has(k)))throw TypeError('Unknown site profile setting');
  return defineProfile({...defaultConfig,...config,tools});
}
