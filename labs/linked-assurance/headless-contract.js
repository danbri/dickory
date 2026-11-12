// Shared *request and observation* contract; not a second RDF reasoner.
// Node and Chromium each run their own real Factoidal WASM engine.
import {scenarios, variants} from './scenarios.js';
import {scopeFrom} from './evidence.js';

export function listCases() {
  return scenarios.map(s=>({
    id:s.id,title:s.title,variants:variants(s).map(v=>v.id),
    scopes:['default','data','ontology','union'],regimes:['simple','RDFS']
  }));
}

export function makeCase(input={}) {
  const scenario=scenarios.find(s=>s.id===(input.scenario||'vocabulary'));
  if(!scenario)throw Error('Unknown scenario: '+input.scenario);
  const variation=variants(scenario).find(v=>v.id===(input.variant||'base'));
  if(!variation)throw Error('Unknown variant: '+input.variant);
  const scope=input.scope||'union',regime=input.regime||'RDFS';
  if(!['simple','RDFS'].includes(regime))throw Error('Unsupported regime: '+regime);
  const budgetMs=input.budgetMs??60000;
  if(!Number.isInteger(budgetMs)||budgetMs<1||budgetMs>120000)throw Error('budgetMs must be 1..120000');
  return {
    identity:{scenario:scenario.id,variant:variation.id,scope,regime,budgetMs},
    request:{
      dataset:variation.dataset,description:scenario.description,
      queries:scenario.queries.map(q=>({...q})),scope:scopeFrom(scope),regime
    }
  };
}

// The invariant projection ignores nondeterministic runtime timings, human
// diagnostics and infrastructure-specific attestation. It does NOT turn
// an incomplete execution into a false RDF answer.
export function normalizeRdf(result) {
  const execution=result?.execution||'engineFault';
  const completed=execution==='completed';
  const context=completed?result.context:{};
  return {
    execution,
    claims:completed?(result.claims||[]).map(c=>({
      key:c.key,query:c.query,answer:c.answer
    })):[],
    context:completed?{
      datasetBytesSha256:context.datasetBytesSha256,
      selectedGraphSha256:context.selectedGraphSha256,
      scope:context.scope,regime:context.regime,
      runtimeVersion:context.runtimeVersion
    }:null,
    dataset:completed?{
      quads:result.dataset.quads,defaultQuads:result.dataset.defaultQuads,
      namedGraphs:[...result.dataset.namedGraphs].sort(),
      selectedQuads:result.dataset.selectedQuads
    }:null,
    explanation:completed&&result.explanation?{
      entailed:result.explanation.entailed===true
    }:null
  };
}

export function parity(left,right) {
  const a=left.observation,b=right.observation;
  const completed=a.execution==='completed'&&b.execution==='completed';
  return {
    equivalent:completed&&JSON.stringify(a)===JSON.stringify(b),
    comparable:completed,
    reason:!completed?'At least one path did not complete; timeout, cancellation and memory failure are not semantic refutations':
      JSON.stringify(a)===JSON.stringify(b)?'Identical normalized RDF outcomes for this exact input':'Observations differ',
    node:a,browser:b
  };
}
