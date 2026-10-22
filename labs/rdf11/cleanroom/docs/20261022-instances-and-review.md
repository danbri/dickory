# Second increment: instances and a readable review path

22 October 2026. Draft mapping, no accepted expert reviews or package refinement.

The archived Semantics prose was reread by the explicitly requested AI close-reading subagent. HTML selectors locate the resulting selections; no grep-based assertion extraction was used. The pinned specification bytes and their SHA-256 identities are unchanged.

## New formal work

[Instances.lean](../RDF11/Instances.lean) adds partial, simultaneous substitutions over a common ambient blank-node identity domain. An omitted mapping preserves the blank. All names remain fixed. The graph image is a set, so identification of triples cannot introduce duplicate graph membership.

| Claim | Result | Remaining boundary |
|---|---|---|
| MT11-GRAPH-INSTANCE | Definition of term/triple/graph substitution and instances | Generalized syntax; use ordinary endpoints where required |
| MT11-INSTANCE-PROPERTIES | Reflexivity, transitivity and an original witness for each image triple | No finiteness or injectivity restriction |
| MT11-VOCABULARY-INSTANCE | Names introduced for blanks must lie in V | Existing names are unrestricted |
| MT11-PROPER-INSTANCE | Name replacement or identification of distinct occurring blanks | Proper instance is not proper subgraph |
| MT11-ISOMORPHISM | Inverse renaming on occurring blanks; mutual instances; identical satisfaction; mutual entailment | Does not equate original sets or preserve external blank sharing; a packaged Concepts all-node bijection remains future work |
| MT11-LEAN-GRAPH | No instance is a proper subgraph | A mathematical RDF property, not a reference to the language Lean |
| MT11-LEAN-CONSEQUENCES | Ground graphs are lean; ordinary instance/subgraph equivalence | Partial coverage of the broader redundancy discussion; no existence theorem for lean subgraphs |
| MT11-INTERPOLATION | An instance of ordinary E contained in G implies G entails E | Only one direction; completeness remains open |
| MT11-INSTANCE-ENTAILMENT | Upgraded from blank-only replacement to arbitrary RDF-term substitution with an ordinary source; ordinary endpoints corollary | Generalized-source interpretation question remains open |

Properness uses the resolved substitution, so explicit identity replacements are not proper and a replacement colliding with an unchanged blank is detected. Only identities occurring in the source graph count. Composition applies the second substitution to the first substitution’s resolved images; replacement does not recursively reapply itself.

The instance-entailment proof fixes an interpretation and pulls back one satisfying assignment for the entire image graph. Every source blank in ordinary RDF occurs as subject or object, so truth supplies an IR-valued replacement denotation. The proof does **not** assume IP is a subset of IR. Source and image may share identities: every original blank’s assignment is recomputed, rather than retaining assignments for identities appearing in both graphs. Ordinary endpoint types allow literal replacements for object-only blanks while excluding literal subjects.

The frozen registry now lists 14 formal files and 438 local declarations, including generated helpers; their elaborated closure has 2,396 declarations. The new declarations were inspected and explicitly enrolled with source/support grounds. No new foundation modules or logical axioms were needed. The verifier still rejects undeclared files and declarations instead of enrolling them automatically.

## Reading and review

The viewer now offers a rendered reading copy and original-HTML tabs, with the same passage associations. The reading copy uses an allowlist of passive HTML and attaches records at their original scalar offsets. It adapts publisher styling; it does not claim a browser-rendering identity proof. Unlocated areas remain explicitly without passage associations. Nested associations are retained, with the innermost clicked element opening its claims.

Search covers claim IDs, paraphrases and symbol-linked English. Status filters and labelled colours distinguish mapped, partial and unmapped records. Mixed passage colours conservatively reflect the least-covered associated claim. These statuses do not indicate expert acceptance or exhaustive extraction of a passage.

Every local declaration shown in the viewer receives an expandable English gloss. [lean-glosses.json](../catalogue/lean-glosses.json) holds curated prose for authored definitions, statements and important fields. Compiler-generated declarations receive a separately labelled explanation of their role and documented parent. Missing authored glosses or stale gloss names fail viewer generation. The prose itself needs expert review and is not proved equivalent to Lean.

## What remains missing

There are **42 mapped records, including partial mappings, among 195 preliminary records**. Eight previously unmapped records gained mappings; ordinary instance entailment was strengthened. The preliminary directory itself is not a proven complete extraction, so these figures are not a specification compliance percentage.

1. **Complete simple-entailment mathematics:** the converse of interpolation, compactness, lean/proper-instance non-entailment, and the scope of generalized predicates. Isomorphism currently has an explicit inverse-renaming representation; the separate all-node bijection packaging in Concepts remains unproved.
2. **Skolemization:** freshness/injectivity and the source’s entailment, non-entailment, lifting and vocabulary-conservativity results. The source’s preceding paragraph supplies the “graph contains blanks” premise for its four listed results; preserve that context in future claims.
3. **Datatypes and concrete terms:** literal structure, language tags, lexical/value spaces, datatype maps, ill-typed literals and D-interpretations; concrete IRI admissibility/equality.
4. **RDF and RDFS:** axiomatic triples, vocabulary interpretation conditions, classes, properties, domain/range, subclass/subproperty and the stated entailment consequences/rules.
5. **Other source material:** datasets, remaining general requirements, informative discussion and examples; finer statement spans and resolved contextual references.
6. **Assurance:** independent source-to-claim and claim-to-Lean review, a complete character accountability certificate, and a formal grounding certificate for the dependency inventory. SHA/decoder/locator/extractor tools still form part of the trust boundary.
7. **Executable integration:** no parser, reasoner, JS/WASM wrapper or published npm artifact is refined by this model. W3C tests remain a separate required validation stream; their coverage cannot establish full specification coverage.

A useful next semantic milestone is ordinary interpolation completeness, followed by explicit RDF interpretation conditions. Neither is claimed as finished here.

## Validation

The full library and frozen registry pass with Lean 4.33.1. The seven rejection checks still reject unregistered sources, bad bindings/dependencies, proof placeholders, duplicate enumerations and false complete-coverage claims. Eight Python checks cover Unicode source slicing, passive rendering and attachment of every selected passage. CI exercises the actual viewer in Chromium before publishing: code/proof visibility, nested dependencies, English glosses, filters/search, both document views, clickable annotations, deep links and mobile layout.
