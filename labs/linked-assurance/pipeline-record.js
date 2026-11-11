// Evidence index for the actual executions, not a second pipeline engine.
// Factoidal owns the RDF graph runner; Lean owns the executable policy adapter.
export function pipelineRecord({rdf,verification,identities,compile,execution}){
  return {
    schema:'linked-assurance-pipeline-v1',
    rdfGraph:rdf.pipeline||null,
    hostStages:[
      {id:'credential-check',kind:'verification',input:'public key + exact payload + signature',output:'verified flag + expiry',
        implementation:'WebCrypto ECDSA P-256/SHA-256',contractStatus:'host assumption',
        observation:verification,assumptions:['WebCryptoSignatureCorrect','DemoKeyIsTheIntendedKey']},
      {id:'policy-adapter',kind:'transformation',input:'Context × Execution × List QueryBinding × List QueryObservation',output:'Except String Evidence',
        implementation:'LinkedAssurance.adaptEvidence',contract:'LinkedAssurance.adapterRequirements',
        theorem:'LinkedAssurance.adaptEvidence_contract',contractStatus:compile?.contractChecked?'compiled with checked support module':'source contract; browser compilation not recorded',
        fixtureSha256:identities.fixtureSha256,successfulExecution:execution?.executed===true,
        assumptions:['HostPreservesCheckedNodeOutputs','HostPreservesRequestedBindingsAndContext']},
      {id:'policy',kind:'decision',input:'Evidence × OperationalState',output:'Decision',
        implementation:'LinkedAssurance.policy',contract:'LinkedAssurance.permitRequirements',
        theorem:'LinkedAssurance.policy_contract',contractChecked:compile?.contractChecked===true,
        sourceSha256:identities.policySourceSha256,decision:execution?.decision||null,
        assumptions:['ClaimKeysHaveTheIntendedApplicationMeaning','OperationalObservationsAreAccurate']},
    ],
    connections:[
      {from:'rdfGraph.bindings',to:'policy-adapter.observations',assurance:'named host assumption; exact queries and node indices exported'},
      {from:'credential-check',to:'policy.operational',assurance:'named host assumption'},
      {from:'policy-adapter',to:'policy.evidence',assurance:'Lean Except.map calls the policy only after successful adaptation'},
    ],
    compositionTheorem:'LinkedAssurance.policy_pipeline_contract',
    assurance:'RDF stage contracts, adapter contract and policy contract are separate. Host transport and the meaning of application keys are not proved end to end.',
  };
}
