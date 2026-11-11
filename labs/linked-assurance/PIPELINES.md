# Contracted stages in Linked Assurance

Graph selection, inference and query evaluation now use Factoidal's existing
checked node API. An executable Lean adapter has its own contract connecting
query bindings and observations to the policy. The exported record identifies
both parts and the assumptions connecting them.

| Stage | Input → output | Contract or boundary |
| --- | --- | --- |
| TriG reader | String → dataset and prefixes | Factoidal `ReaderContract` |
| Graph selection | Dataset → Dataset | CONSTRUCT `shippedEvaluator`, under `EvalContract` |
| RDFS closure | Graph → Graph | `rdfsReasoner`, under `Regime.Entails`; omitted in simple mode |
| Each ASK binding | Dataset → Answer | `shippedEvaluator`, under `EvalContract`; an actual Boolean output |
| Description explanation | Selected dataset → explanation result | Separate `rdfsExplainGraphStage` branch, under `ExplainGraphContract` |
| Signature check | Key, payload, signature → verification observation | WebCrypto ECDSA host call; named correctness and key-selection assumptions |
| Policy adapter | Context, execution state, bindings, observations → `Except String Evidence` | `adapterRequirements`, with `adaptEvidence_contract` |
| Policy | Evidence, operational state → Decision | `permitRequirements`, with `policy_contract` |

Selection precedes closure. CONSTRUCT binds subject, predicate and object from
the chosen graphs of one parsed document; it creates no template blank nodes.
Shared blank identity is retained. The explanation branch starts from the
selected original graph, not the closure presented as asserted input. An edited
description is not assumed equivalent to an edited ASK.

Factoidal checks node settings and wire types. Exported `rdf.pipeline` records
include the checker reports, exact selection query, each claim key's query and
node index, settings digests, contract names and stage evidence.
`registeredStagesProved` describes registered stage contracts, not an independent
proof of the JavaScript runner or an end-to-end policy decision.

The Lean adapter receives requested bindings separately from observed
query/Boolean pairs. It rejects missing or extra observations, query mismatches,
duplicate keys and claims attached to non-completed runs. Its theorem establishes
preservation of both lists, their order and the execution context on success.
`Except.map` calls the policy only after successful adaptation.
`policy_pipeline_contract` combines this contract with the permission contract.
It does not assign domain meaning to arbitrary user-chosen claim keys.

## Factoidal's general pipeline machinery

[PipelineBridge.lean](lean/PipelineBridge.lean) imports Factoidal's actual
`L4Factoidal.Dataflow.Stage` type and wraps the executable adapter and policy as
stages. `Stage.comp` composes them; `adaptedPolicyStage_sound` uses that stage's
soundness proof. No second RDF semantics or substitute stage calculus is defined.

The native check materialises only transitive Lean imports from Factoidal commit
`6f57afba14e04ed648358e4693790edff69a6cd3`, the npm runtime's declared source
identity. It writes only under this lab's ignored `artifacts/`. The
[native check report](artifacts/pipeline-native-checks.json) records source hashes
and axiom dependencies. Native compiled modules are not imported into wasm32.
The browser compiles the same adapter and policy definitions and their contracts
in Workbench and Policy.

```sh
python3 labs/linked-assurance/tools/check_lean.py
python3 labs/linked-assurance/tools/check_pipeline.py --factoidal /path/to/factoidal-core
```

The public npm registry does not yet register this application adapter as a new
npm node. Native Stage integration and the host evidence index are explicit;
the entire browser execution is not covered by one instantiated Factoidal
pipeline theorem.

## Other kinds of stage

Stages can transform or check any typed values. Factoidal 0.35.1 exposes
`xslt4Transform`: String → XSLT result. The regression suite executes it and
confirms its evidence is **tested**, not proved. A transformation's correctness,
the parser's correctness and the meaning of the output need separate contracts.
Connecting their types alone proves none of these properties.

Signature verification fits the same architecture. This lab uses WebCrypto ECDSA
over exact payload bytes. It does not claim the contracts of Factoidal's different
VC or Ed25519 stages, some registered but not bound in this npm release. A
signature stage must identify the algorithm, key, bytes and assumed correctness
of the implementation; later stages may use its result under that assumption.

The record's top-level `pipeline` indexes the RDF subgraph, signature observation,
adapter, policy and connecting assumptions. Host preservation of checked node
outputs, bindings and context remains unproved. Clock, transport, permission,
key authority and application meaning remain external premises. The record is
readable JSON, not a self-authenticating certificate of the whole system.
