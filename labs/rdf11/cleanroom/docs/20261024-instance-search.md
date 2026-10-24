# Finite instance search and simple-entailment decisions

24 October 2026. Twenty-fourth working increment. The finite instance search is exact, returns a certified substitution when successful, and decides simple entailment for ordinary conclusions. It composes with the executable printed RDF/RDFS closure procedure. This does not repair that procedure's completeness obstruction or establish the specification's complexity classification.

## Source reading and scope

The source-reading agent used AI close reading of the archived specification, including the surrounding definitions and qualifications. HTML parsing located the selected passages afterwards. Relevant selectors are `#notation-and-terminology > p:nth-of-type(9)`–`(12)` and `#dfn-instance`; `#blank-nodes > p:nth-of-type(2)`–`(3)` and its condition table; `#simpleentailment > p:nth-of-type(1)`; `#properties-of-simple-entailment-informative > p:nth-of-type(6)`–`(8)` and `#dfn-interpolation`; and Appendix A `#entailment-rules-informative > p:nth-of-type(4)`, `(15)`–`(19)`. Source bytes and their hashes are unchanged.

The instance and truth definitions are normative. The entailment properties and Appendix A procedure/complexity discussions are informative. Finite effective inputs qualify the executable interface; they do not impose a global finiteness restriction on RDF graphs. The new derived claims `MT11-FINITE-INSTANCE-DECISION` and `MT11-EXECUTABLE-CLOSURE-INSTANCE-CHECK` make the refinement scope explicit. Existing decidability, interpolation and closure mappings are extended. The ordinary rule procedure is mapped only for its final instance test, and the complexity discussion only for decision, candidate-count and ground-reduction components.

The catalogue now has 186 mappings among 225 preliminary records, including partial mappings. Thirteen source questions remain open and no expert review is marked accepted. These counts are not compliance percentages.

## The proof chain

`InstanceSearch` enumerates distinct premise-position terms and distinct occurring conclusion blanks. A successful substitution must send each such blank to a term in a premise triple: `blank_image_in_terms` proves that restriction. `assignments_cover` and `candidates_complete` show that finite enumeration cannot miss a successful witness. No finite ambient blank type is required.

One simultaneous substitution serves all conclusion triples. IRIs and literals remain fixed. Different blanks may coalesce, distinct conclusion triples may collapse to one source triple, and source triples can be reused. A replacement blank is not recursively substituted even if its identifier also occurs in the conclusion. Embedded literal datatype IRIs do not become candidate terms unless they actually occur in triple positions. Deduplicating input presentations preserves the represented sets and the answer.

`check_iff` proves exact instance-subgraph existence; `search_sound` certifies the returned witness. `certificate` packages the actual substitution with its inclusion proof. `candidates_length` gives K^b candidate-list entries, where K and b count distinct premise terms and occurring conclusion blanks. For b=0 there is one empty assignment, including when K=0. `check_ground` proves equality with direct triple inclusion. The list-size equation is not a runtime or NP-completeness theorem.

`InstanceDecision` connects this algorithm to the existing ordinary interpolation theorem. `ordinaryDecision` and `apartDecision` are executable decisions of model-theoretic simple entailment for finite inputs with an ordinary conclusion; the premise may be generalized. Separate blank types are embedded into disjoint copies, and satisfaction/entailment preservation is proved. This preserves separate existential graph witnesses; it does not identify a shared blank's referent across premise and conclusion or replace union with merge. `ordinary_interpolation_apart` also extends the non-finite mathematical interpolation result to independent blank types.

Failure gives a concrete Herbrand countermodel via `negative_countermodel`, including for generalized conclusions. Generalized success is only a syntactic result: `InstanceCheckScope.generalized_success_not_entails` connects a successful executable match to the existing property-only-denotation countermodel. The ordinary-conclusion restriction is enforced in the decision interface.

`ClosureInstanceCheck` composes exact finite RDF/RDFS closure generation with exact search. Its iff theorems identify instance existence in the selected closure; its ordinary-conclusion theorems identify simple entailment from that closure. Positive checks imply RDF/RDFS entailment, including independently typed input blanks. The answer is invariant under repeated or reordered input presentations.

The opposite direction remains unavailable. `selection_failure_consistent` proves that the full executable check returns false on the existing container-selection example while full RDFS entailment holds and a full model satisfies the premise under the existing constructor hypotheses. This connects actual executable behavior to the earlier proof for all derivations. It is evidence for source review, not an adopted erratum or a repaired algorithm.

## Review route and remaining obligations

Read [InstanceSearch.lean](../RDF11/InstanceSearch.lean), [InstanceDecision.lean](../RDF11/InstanceDecision.lean), [ClosureInstanceCheck.lean](../RDF11/ClosureInstanceCheck.lean) and [InstanceCheckScope.lean](../RDF11/InstanceCheckScope.lean). Each authored declaration has a curated draft English gloss in the viewer. The separate Statements/Syntax/Simple entry route remains 393 lines.

Eighteen project-owned symbolic regressions exercise empty inputs, witness certificates, shared blanks, simultaneous replacement, collapse, lexical identity, generalized images, independent blank domains, candidate counts and closure composition. They run through Lean's executable evaluator alongside universal kernel proofs. Two new rejection probes check the ordinary-conclusion type boundary and refusal to use different witnesses for one shared blank. No W3C parser fixture or package test is claimed.

Concrete IRI/literal parsing and identity correspondence, fresh-blank ordinary-rule saturation, arbitrary-D procedures, full RDF/RDFS entailment completeness, operation costs and NP membership/hardness proofs remain separate. The algorithms are exhaustive reference implementations, not a performance claim. Current source questions and expert fidelity reviews remain open. No Factoidal JS/WASM, ingestion or storage boundary is refined by this increment.


## Deliberate registry audit

The increment adds 114 local declarations: 71 authored declarations with curated English glosses and 43 generated equations, pattern helpers, simplifier and proof helpers with explicit parent links. All existing declarations retain their type, kind and module attribution. Five formal files are enrolled; the two root import files and generated source snapshot change. Source bytes are unchanged.

The registry now contains 2,826 local declarations across 87 formal files, with an elaborated dependency closure of 7,560 declarations. The two newly used standard-library modules, Init.Data.List.Find and Init.Data.List.Nat.Sum, contribute eight inspected theorems/definitions for finite search and repeated-sum length reasoning. They add no logical axiom. The allowed set remains propext, Classical.choice and Quot.sound; no local declaration is unsafe or an added axiom.

## Validation and publication gate

The local build completed all 89 jobs. The frozen registry/source verifier passed with 186 mapped records among 225 preliminary claims; it continues to reject complete coverage. All twelve rejection probes, eighteen executable instance regressions and fifteen Python unit checks passed. The existing twelve closure regressions retain their passing report and are rerun by CI. JavaScript syntax, skill validation and whitespace checks passed.

The publication workflow also regenerates the source viewer, stages nine public files plus a build manifest, checks local links and runs Chromium before deployment. Eight new browser check groups exercise actual Lean bodies and glosses, certified substitutions, the ordinary/generalized boundary, positive closure soundness, the checked negative-completeness obstruction and explicit partial statuses. Together with the existing checks these specify 114 browser checks; their execution result belongs to the workflow evidence, not this pre-publication count.

The [editions and families design](20261023-spec-versions-and-families.md#cross-family-review-boundaries) records the corresponding future SPARQL boundary: certified instance existence does not supply the specified multiset of query solutions. Cross-edition catalogues and OWL/SPARQL bridges remain planned work.
