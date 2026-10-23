# Dataset content policies and denotation boundaries

This seventh increment addresses the remaining three Semantics §10 records with explicitly partial mappings. AI close reading and a second AI source review informed the design; neither is accepted expert review. The source's MAY/SHOULD language remains visible rather than becoming an unconditional axiom.

## Chosen content and entailment

`DatasetPolicies.lean` introduces a candidate `DatasetRegime` with an arbitrary model type and dataset truth relation. A model may contain a modal structure; the interface does not restrict every regime to one simple interpretation. It also does not certify that a candidate is an admissible RDF semantic extension. Section 3's preservation obligations remain separate.

`IncludesDefault` represents an explicitly adopted default-content condition through a designated graph interpretation for each model. From that assumption, the proofs transfer simple consequences of the default graph to dataset-policy consequences. The same composition works for RDF/RDFS or another graph regime when the designated interpretations satisfy its model conditions. Consequences compose through the existing graph-entailment proofs.

The default-only example uses all simple interpretations in the declared universe and takes dataset truth to be default-graph truth. Its entailment is proved equivalent to simple entailment between defaults, and it respects dataset isomorphism. The corresponding `defaultUnder` construction ranges over all models satisfying a supplied graph-regime condition, and its entailment is proved exactly equivalent to the existing `EntailsUnder` between defaults. This connects the choice directly to RDF/RDFS graph semantics without claiming those model classes are inhabited. These are policy choices, not the uniquely prescribed RDF dataset semantics.

## What preserves entailment

Restricting a regime's models while retaining its truth relation preserves entailment. A subtype construction is proved equivalent to quantification with the corresponding model-class premise. A truth-preserving map from new models to old models supplies another sufficient transfer condition; it is not a characterization of every semantic extension.

`DatasetPolicyExamples.lean` demonstrates why adding a dataset-dependent truth condition is different. Requiring a fixed IRI graph name to be present retains default content and respects dataset isomorphism. Yet the default-only policy's entailment from a dataset with one empty named graph to the dataset with no named graphs fails under the presence policy. The example uses an IRI key, avoiding an arbitrary choice of ambient blank identity.

`DatasetNamedComparison.lean` records the source's illustrative matching-name graph condition. Missing graph names are filled with empty graphs. The generic comparison needs a genuine graph-entailment relation to represent the source; its simple specialization uses the existing `SimplyEntails`. This comparison uses exact keys, considers named components independently and omits the default. It supplies neither key-renaming alignment nor a common existential witness across graphs. Mutual comparison does not imply dataset isomorphism: the earlier present-empty/absent distinction supplies a checked counterexample. These conditions do not define the complete modal-like extension suggested by the source.

## Name pairing is not denotation

The current `DatasetNameDenotation.lean`, strengthened by the [global-name refinement](20261023-global-name-scope.md), quantifies over arbitrary IRI/literal/blank domains and a selected IRI, then fixes one dataset whose graph-name IRI also occurs as subject, predicate and object in a true component triple. An explicit injective embedding places graph objects in the resource carrier alongside a distinct non-graph object. Two simple interpretations satisfy the default graph and all named graphs. In one, the name denotes its paired graph object; in the other, it denotes the distinct object.

The result is existential and limited to simple interpretations. It does not prove RDF/RDFS model existence, unconstrained denotation for every dataset, or independence from additional assertions and extensions. The embedding belongs to the example and is not required of all RDF interpretations. The source permits identity or nonidentity; it requires neither a general equality nor a general inequality based solely on pairing. Its engine-inference guidance remains an implementation/review obligation.

## Review boundary

This policy increment initially brought the catalogue to 137 mappings among 197 preliminary records, including partial mappings. All source extraction and formalization approvals remain pending. The three new mappings cover logical interfaces and conditional results; they do not discharge recommendation conformance, extension admissibility, the entire dataset section, or implementation refinement.

The compact Statements/Syntax/Simple review route remains 359 lines. README, methodology, glosses and browser checks expose the new scope assumptions. The complete-coverage gate continues to reject the outstanding source, proof, review and implementation obligations.

Before the later global-name refinement, the frozen inventory contained 39 formal files and 1,315 local declarations, with 5,798 declarations in the elaborated dependency closure. The 93 new declarations include generated helpers; all 56 new authored declarations have curated English glosses. No existing declaration signature, foundation module or allowed logical axiom changed.

Validation passed the full Lean build and registry audit, all seven rejection checks, eleven Python tests, viewer generation with all authored glosses, the methodology skill validator, and the site-link check. Three additional Chromium checks exercise the optional policy scope, fixed-IRI presence counterexample and simple-model denotation alternatives; CI gates publication.
