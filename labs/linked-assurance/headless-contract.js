// SPDX-License-Identifier: Apache-2.0
import {scenarios,variants} from './scenarios.js';
import {scopeFrom} from './evidence.js';
import {caseInput,policyInput} from './profile/catalogue.js';
import {decode} from './profile/core.js';
export function listCases(){return scenarios.map(s=>({id:s.id,title:s.title,variants:variants(s).map(v=>v.id),scopes:['default','data','ontology','union'],regimes:['simple','RDFS']}));}
export function makeCase(input={}){
  const resolved=decode('state' in input?policyInput:caseInput,input);
  const {scenario,variant,scope,regime,budgetMs}=resolved;
  const sample=scenarios.find(s=>s.id===scenario);
  if(!sample)throw Error('Unknown scenario: '+scenario);
  const data=variants(sample).find(v=>v.id===variant);
  if(!data)throw Error('Unknown variant: '+variant);
  return {identity:{scenario,variant,scope,regime,budgetMs},resolved,
    request:{dataset:data.dataset,description:sample.description,queries:sample.queries.map(q=>({...q})),scope:scopeFrom(scope),regime}};
}
export function normalizeRdf(r){
  const execution=r?.execution||'engineFault',done=execution==='completed';
  return {execution,claims:done?r.claims.map(c=>({key:c.key,query:c.query,answer:c.answer})):[],
    context:done?{datasetBytesSha256:r.context.datasetBytesSha256,selectedGraphSha256:r.context.selectedGraphSha256,scope:r.context.scope,regime:r.context.regime,runtimeVersion:r.context.runtimeVersion}:null,
    dataset:done?{quads:r.dataset.quads,defaultQuads:r.dataset.defaultQuads,namedGraphs:[...r.dataset.namedGraphs].sort(),selectedQuads:r.dataset.selectedQuads}:null,
    explanation:done&&r.explanation?{entailed:r.explanation.entailed===true}:null};
}
export function parity(a,b){
  const left=a.observation,right=b.observation,comparable=left?.execution==='completed'&&right?.execution==='completed';
  return {comparable,equivalent:comparable&&JSON.stringify(left)===JSON.stringify(right),node:left,browser:right,
    reason:comparable?'Exact normalized comparison; host identity and timing excluded':'Incomplete execution is not a negative RDF answer'};
}
