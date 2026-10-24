# Arbitrary graph families, shared union and merge

24 October 2026. Twenty-fifth working increment. Union and merge now cover arbitrary set-sized families, including empty and infinite families and independently typed blank domains. Their truth conditions connect to exact syntactic projection, the existing instance relation and disjoint-support graph isomorphism. The formalization remains incomplete and all expert fidelity reviews remain pending.

## Source reading and attribution

The existing source-reading subagent used AI close reading of the pinned RDF 1.1 text. Parsing subsequently located the passages. The operative §4.1 definitions are `#shared-blank-nodes-unions-and-merges > p:nth-of-type(15)`, `(16)` and `(20)`; assignment and whole-graph existential truth are in `#blank-nodes > p:nth-of-type(2)` and its following table. The graph-isomorphism convention is `#notation-and-terminology > p:nth-of-type(14)`. The informative discussion of separate witnesses is `#shared-blank-nodes-informative > p:nth-of-type(5)`–`(6)`. The graph-set combination note is `#simpleentailment > p:nth-of-type(3)`.

The source imposes no finite-family restriction. Its explicit permission for infinite graphs is separately recorded; finiteness of an executable input must not become a silent mathematical hypothesis. The headline “merging lemma” is our derived review name grounded in §4.1 and the truth conditions. Appendix C does not contain a separately named merging theorem or proof.

The graph-set combination paragraph is explicitly a technical note, so its catalogue status is corrected to informative under the specification's normative-boundary rule. This does not weaken the normative union, merge or truth definitions. Archived bytes and source hashes are unchanged.

The note's final sentence makes a separate historical assertion: merging a set in RDF 1.1 is said to reproduce the 2004 graph-set simple-entailment definition. The new record `MT11-MERGE-RDF2004-ENTAILMENT-CORRESPONDENCE` captures that assertion and remains unmapped. The preceding paragraph fixes the regime to simple entailment. A proof requires the dated 2004 definitions and explicit syntax, interpretation and blank-scope correspondence; the current RDF 1.1 family theorem supplies only one side. It is not evidence of complete RDF/RDFS/datatype or dataset equivalence between editions.

The viewer now displays available scope notes for unmapped claims. Selecting the historical claim exposes the missing bridge obligation, and the shared source passage retains its unmapped colour even while its other claim has a checked Lean mapping.

## Mathematical contracts

`Set.iUnion` preserves the original blank identity domain. `GraphFamily.merge` uses a dependent pair of an index and a blank from that input domain. The construction changes no IRI or literal and does not require unused identities in the original domain. `ordinaryMerge_generalize` connects the ordinary syntax construction exactly to the generalized one.

Under a fixed assignment, union truth is equivalent to truth of every input. Union satisfaction therefore requires one common assignment. `Coherent` and `amalgamate` give a second characterization: separate graph witnesses can be combined exactly when they agree on every shared occurring blank. `Apart` concerns occurring supports, not the entire ambient blank type; it makes coherence automatic.

`graphTrue_merge` combines an explicitly supplied assignment family without selecting witnesses. `satisfies_merge` proves that one interpretation satisfies the merge exactly when it separately satisfies every input. Its reverse direction uses classical choice to select assignments for an arbitrary family. Different syntactic blanks may receive the same resource value. Individual satisfiability in different models would be insufficient.

An indexed family can repeat the same graph and thereby produce extra fresh copies. `unionSet` and `mergeSet` instead index the actual members of a set of graphs. Surjective reindexing preserves merged satisfaction; it is not claimed to preserve graph isomorphism. The empty-family result requires no default index and yields exactly the empty graph.

`forget_tags` proves exact image equality between the tagged merge and the original union. `ScopedBlank` embeds both into one common ambient sum, allowing `union_is_instance` to use the existing simultaneous-substitution relation without redefining it. Under `Apart`, `apart_isomorphism` gives actual inverse maps on occurring supports and exact graph-image equality. This discharges the no-shared-blanks correspondence using the source's convention of identifying isomorphic graphs. It does not claim literal equality between terms of different Lean types.

Entailment stays a relation between graphs. The merge correspondence quantifies over one model satisfying every component separately. The union correspondence quantifies over one common blank assignment. The fixed-model-condition version composes with `EntailsUnder`; it does not establish extra syntax admission for arbitrary extensions or a dataset/OWL/SPARQL entailment policy.

## Connected examples and review route

The previous two-resource shared-blank countermodel is reused for indexed families and literal sets of graphs. Their merges are satisfied while their unions are false. The infinite example has a natural-number-indexed family of disjoint blank supports, a proved isomorphism and a common witness assigning the same resource to every blank. A separate nested-subgraph example has exactly two union triples and three merged triples, independently of the chosen duplicate-free enumerations. This is a derived example of size increase, not a transcription of the source's pictured example.

Read [FamilyMerge.lean](../RDF11/FamilyMerge.lean), [MergeInstances.lean](../RDF11/MergeInstances.lean) and [FamilyMergeExamples.lean](../RDF11/FamilyMergeExamples.lean). The headline alias in [Statements.lean](../RDF11/Statements.lean) now states the full family result. The two existing graph-renaming composition lemmas are generalized to accept different input, intermediate and output blank types; their old uses remain instances of the stronger signatures.

The catalogue has 187 mappings among 226 preliminary records, including partial mappings. Union, merge and their instance/isomorphism relationship now include these results. The newly mapped graph-set note exposes the choice between union and merge. Thirteen source questions remain open, and no extraction or formalization expert review is accepted. These counts are not compliance percentages.

Concrete blank-label allocation, identity provenance across retrievals, parser/serialization behavior and Factoidal JS/WASM refinement remain separate obligations. The family operations are mathematical constructions, not an executable infinite-graph merging engine. Full RDF/RDFS completeness, concrete term/datatype correspondence and the remaining source-accountability work are still required for the overall goal.

## Deliberate registry audit

The increment adds 95 local declarations: 62 authored declarations with curated English glosses and 33 compiler-generated equations, pattern, simplifier and proof helpers with parent links. The registry now inventories 2,921 local declarations across 90 formal files, with an elaborated closure of 7,674 declarations. Exactly three existing signatures change: the ordinary and generalized graph-renaming composition lemmas now support different blank types, and the merging headline now aliases the arbitrary-family theorem. The original binary merge theorem is retained. All other existing signatures, kinds and module attributions are unchanged.

Nineteen newly referenced standard-library declarations support Boolean existential elimination, dependent-pair elimination and equality, dependent conditional congruence and propositional simplification. They belong to already reviewed modules, are safe declarations, and add no logical axiom. The allowed set remains `propext`, `Classical.choice` and `Quot.sound`; no local axiom, unsafe definition or proof placeholder is introduced.

The complete 92-job build and frozen registry verifier passed after adding the separately extracted historical claim. All twelve rejection probes, fifteen Python unit checks and the twelve closure plus eighteen instance execution regressions passed. The short Statements/Syntax/Simple route is 394 lines. Eight new Chromium check groups bring the workflow's browser gate to 122 checks, including the actual family theorem bodies, common-witness condition, set-versus-indexed distinction, exact instance/isomorphism maps, infinite and size examples, and the visible unproved historical bridge. The workflow evidence records their execution before Pages deployment.
