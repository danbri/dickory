# Ordinary rule strategies and the missing blank-predicate intermediate

24 October 2026. Twenty-sixth working increment. Both printed Appendix A entailment examples now have checked positive proofs. The blank-predicate example also has a proof of failure for the displayed rules restricted to ordinary conclusions, independent of the container-axiom selection issue. The full formalization remains incomplete and expert fidelity reviews remain pending.

## Source method and exact boundaries

The existing source-reading subagent used AI close reading of the archived RDF 1.1 Semantics text. HTML parsing then located the selected passages. Appendix A is informative. In `#entailment-rules-informative`, paragraphs 3–5 introduce the ordinary procedure and its soundness/incompleteness assertion. The first table’s second and fourth rows contain the literal and blank-predicate examples. Paragraphs 11–13 contain the second derivation; paragraphs 20–22 discuss rule strategies. `#dfn-rdfd1`, `#dfn-rdfs7` and `#dfn-rdfs2` supply the actual patterns.

The first ordinary procedure has no `rdf:_1` fallback. The later generalized procedure does. `OrdinaryAxiomSeed` preserves that distinction. Its surrounding graph operations remain extensional sets.

The rdfD1 table gives two conclusion triples sharing an existential blank. It does not prescribe a fresh-per-application allocator. `OrdinaryStep` adopts that policy explicitly and proves it sound: the blank is absent from the current graph’s occurring support, both new triples use it, and the old assignment is extended with the literal’s resource value. Syntactic freshness does not require a distinct resource, global freshness, or absence from the independently interpreted conclusion. The recognized-datatype premise remains unchanged; no additional well-typedness test is introduced.

`OrdinaryRun` is a finite sequence of transitions, with possibly infinite graph inputs. It is not a saturation scheduler. Repeated fresh allocation can keep adding triples, and a finite ambient blank type can exhaust its supply. Certified reuse, fairness, termination and a complete ordinary evaluator remain distinct obligations. The proved no-literal invariant makes these allocation questions irrelevant to the second example.

## Connected proofs

[OrdinaryRuleRuns.lean](../RDF11/OrdinaryRuleRuns.lean) connects ordinary syntax, seed inclusion, graph preservation and full-model satisfaction. Every RDF or RDFS run preserves satisfaction in each fixed model of that regime. The existing simultaneous-substitution theorem proves the final instance check sound. An explicitly smaller shared-assignment rule relation embeds into a containing strategy; no claim that every proper subset is incomplete or that a measurable fraction of useful inferences remains is made.

[OrdinaryRuleScope.lean](../RDF11/OrdinaryRuleScope.lean) preserves the exact three-triple premise:

```turtle
ex:a rdfs:subPropertyOf _:b .
_:b rdfs:domain ex:c .
ex:d ex:a ex:e .
```

The conclusion is `ex:d rdf:type ex:c`. The existing generalized closure derives `ex:d _:b ex:e` by rdfs7, then the final typing by rdfs2. Existing closure soundness gives full RDFS entailment. A full model from `RDFSModelConstruction` satisfies the premise under its explicit sufficient datatype/language parameters; these are constructor hypotheses, not restrictions imposed on every interpretation.

[OrdinaryRuleFrame.lean](../RDF11/OrdinaryRuleFrame.lean) supplies a separate syntactic invariant containing the premise and every RDF/RDFS axiom, closed under every displayed rule with an ordinary conclusion, and excluding the target. It is not an RDFS interpretation. Induction excludes the target from every finite ordinary run. The least ordinary-conclusion closure seeded with all axioms also excludes it and contains no literal, so rdfD1 cannot fire. Because the conclusion is ground, substitution cannot rescue the final instance test. This is an unbounded derivation argument, not a bounded search. Supplying all axioms is an explicitly stronger seed, showing that container selection is not responsible.

The obstruction concerns the displayed rule strategy. A new sound composed rule could bypass the intermediate; ordinary RDF syntax does not inherently prevent the entailment.

[SharedLiteralExample.lean](../RDF11/SharedLiteralExample.lean) proves the first example’s positive RDF entailment. Two edges to the identical literal entail two edges to one shared blank plus its datatype triple. Substituting that same literal at every blank occurrence produces a subgraph of the existing generalized RDF closure. The string theorem specializes the datatype to xsd:string. A certified policy reusing one representative for an identical literal can recover this witness, so no universal failure claim for all ordinary allocation policies is made.

## Printed intermediate and review

The archived derivation prints `ex:d _:b ex:c` as the rdfs7 result. The given premise and stated rule preserve `ex:e`. `printedIntermediate` retains the printed triple; `rdfs7_step` derives the actual rule result; `intermediate_not_printed` checks their syntactic inequality. The final typing still has a valid proof.

`Q-ORDINARY-EXAMPLE-INTERMEDIATE` records this as a rule-instantiation mismatch awaiting expert review, not a declared W3C erratum. It does not assert non-entailment of the printed triple considered independently: its existential predicate can have a different witness. The original source bytes are unchanged.

The catalogue now has 192 mappings among 229 preliminary records, including partial mappings, with fourteen open source questions and no accepted expert fidelity reviews. Three new records separately expose the two examples and the printed derivation. The ordinary-procedure mapping now covers sound runs as well as the existing final finite instance check, while retaining its partial status. The short Statements/Syntax/Simple route is unchanged.

Concrete IRI/literal correspondence, full datatype theories, source coverage certification, the remaining mathematical obligations and Factoidal implementation refinement are still required for the overall goal. This increment supplies no new runtime evaluator or W3C-fixture result.

## Verification

The full 96-job Lean build passes. The deliberate registry audit adds 99 authored declarations with curated glosses and 168 compiler helpers, including constructors, recursors, equations and derived decidable equality. The ten helpers not directly prefixed by a new authored declaration have explicit links to the two new enumeration types or the existing Term.hasLiteral definition. All 2,921 previous declarations retain their signatures and module/kind attribution. There are no new library declarations, library modules or logical axioms. The registry now contains 3,188 local declarations, an elaborated closure of 7,941 declarations and 94 formal files.

The fifteen Python tests, twelve closure runtime checks, eighteen instance runtime checks and twelve rejection probes pass. Frozen verification passes with no errors, and the source review viewer has been regenerated with the new declarations and glosses. Six new Chromium check groups extend the browser gate to 128 groups, covering actual seed/transition code, fresh-witness truth, unbounded ordinary failure, the source mismatch, shared-literal identity and restricted-rule scope. Browser execution and publication evidence must be recorded before treating those gates as passed.
