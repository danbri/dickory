# Collection typing and countermodels

23 October 2026. Twelfth working increment. Source mappings remain subject to expert review; concrete vocabulary/datatype correspondence and implementation refinement are not established.

## Source and method

AI close reading selected Appendix D.3, under `#collections` / `#rdf-collections`. All ten direct paragraphs are informative. Their normative support comes from the existing RDF/RDFS axioms and semantic conditions. HTML parsing locates these selected passages in the unchanged archived bytes; it does not extract assertions by itself.

The catalogue separates the exact permutation example, branching permission, missing-rest permission, the nil-empty convention and a derived nil self-edge witness. The broad assertion about existence of other collections and the optional extension policies remain unmapped. Context resolution makes the head/tail antecedent explicit and distinguishes an informally “non-list” tail from a resource outside the semantic class rdf:List. RDFS's range condition requires every rest target to belong to that class.

## Connected results

`Collections.cell` describes the two-triple first/rest idiom using ordinary syntax. `twoItemChain` contains the four printed triples with two existential blanks and a nil terminator. `branchingCell` preserves the four printed multiple-head/multiple-tail triples. These constructors impose no global well-formedness condition on RDF graphs.

`CollectionEntailment` factors vocabulary-domain and vocabulary-range derivations through rdfs2 and rdfs3. It derives List typing for first subjects and both rest endpoints, with semantic entailment corollaries using the already verified shared-assignment soundness theorem. Nil typing comes directly from the RDF axiom. These theorems need no constructor-specific Parameters. Their generalized terms retain the possibility of a literal typing subject; ordinary input syntax and generalized consequences remain distinct.

The new `RDFSFreeProperties` helpers preserve one assignment for both terms and retain partial literal denotation. Arbitrary unrecognized IRIs use the model constructor's name branch. This extends the examples beyond selected built-in vocabulary endpoints without imposing unique names on every interpretation.

`permutation_not_entailed` applies to arbitrary distinct item IRIs outside the recognized datatype set. Its model has exactly the selected first and rest relation pairs. It satisfies the original two-cell description, but every assignment for the reversed description fails. Both source graphs have four edges and no added type assertions. The two graphs have independent existential assignments; within either graph, repeated blanks must keep one denotation.

`branching_consistent` satisfies the printed shape and proves distinct semantic values for its two heads and its two tails. Its universal free relations give at least two of each, not exactly two. The RDFS typing requirements remain satisfied; being a List does not guarantee the intended chain structure.

`rest_existence_not_entailed` accepts any IRI item, including a recognized datatype IRI. The first-only premise is true while the entire rest relation is empty. Even a wholly existential rest-edge conclusion is false, independently of which blanks an application might choose.

`nil_self_edges_consistent` is explicitly a derived witness: nil may have first and rest edges to itself while all RDF/RDFS conditions hold. This refutes a blanket outgoing-edge prohibition or acyclicity requirement. It does not prove that the usual application traversal fails to terminate, because that convention stops at nil. The nil-empty convention itself remains a separate descriptive record.

## Limits and review

The countermodels use the existing sufficient `RDFSModelConstruction.Parameters`. They do not establish arbitrary-graph satisfiability, compatibility of every datatype theory, or the full prescribed built-in meanings. The witnesses are partial evidence for the broad absence of collection well-formedness constraints, not an exhaustive characterization. Additional premises may force conclusions absent from these particular examples.

There are 164 mappings among 215 preliminary records, including partial mappings. No extraction or formalization review is accepted. The short Statements/Syntax/Simple review route remains unchanged. Eighteen new authored declarations receive curated English glosses.

The remaining full-spec obligations include concrete syntax and datatype correspondence, general RDF/RDFS consistency, complete rule and decision procedures, finite pre-interpretation preservation, source-accountability acceptance, expert review of both mapping stages, and package/JS/WASM refinement. The complete-coverage gate must continue to reject this draft.

## Deliberate registry audit

The registry adds 26 declarations: 18 authored declarations and eight generated helpers. Existing declaration signatures are unchanged. The inventory contains 1,524 local declarations in 53 formal files and a closure through 6,126 declarations. No new foundation modules or logical axioms are introduced; allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`. The collection and schemaName reduction equations retain their actual CollectionExamples compiler attribution; private denotation case helpers are explicitly grounded through their parent definition.

## Local validation

The full Lean build and frozen registry audit pass, as do source/hash regeneration, all 15 Python tests and seven negative checks. Source/gloss viewer generation, JavaScript syntax, methodology-skill validation and whitespace checks pass. The complete-coverage request remains rejected. Six collection checks bring the Chromium suite to 49 checks; actual browser execution and Pages deployment remain CI obligations at commit time. No local browser execution is claimed.
