# Datatype, RDF and RDFS increment; compact review route

This is a source-first Lean increment, not an F* port or a package-verification result. Its source is the archived 25 February 2014 RDF 1.1 Semantics, principally §§7–9, with Concepts §3.3 clarifying lowercase language-tag values. Existing simple truth conditions, entailment, substitutions and certified set representations remain the foundation. An AI source-reading pass checked the condition and axiom transcription; expert extraction and formalization reviews are still pending.

## What is checked in Lean

`Datatypes.lean` fixes one external datatype theory across all models. D is a set of recognized IRIs. Ordinary lexical-to-value maps are partial and value spaces are their ranges. One shared value carrier allows datatype aliases and overlapping spaces. Language-tagged values use unchanged lexical strings and US-ASCII-normalized tags, separately from ordinary L2V. The partial injective `ValueRealization` connects external values to a model's carrier: empty D does not force all those values into every simple interpretation.

The proved consequences include exact empty-D/simple-entailment equivalence, preservation under recognizing more datatypes, undefined denotation and graph unsatisfiability for ill-typed recognized literals, and object-literal replacement when two recognized datatypes give the same value. None of these proofs supplies concrete XSD arithmetic, XML Char validation or BCP47 parsing.

`RDF.lean` conjoins D-conditions, required recognition, the RDF property equivalence, complete recognized datatype spaces and the full RDF axiom graph. Every positive container index is included: symbolic `container n` means `rdf:_(n+1)`. `RDFRules.lean` proves rdfD1 with one fresh blank shared by both conclusion triples; a sum type makes it distinct from every existing blank. rdfD2 lifts the existing property proof to full RDF models. An ill-typed literal receives no invented fallback value.

`RDFS.lean` defines ICEXT by the rdf:type relation, and IC/LV by their designated class extensions. Classes and properties share the resource universe; their identities are not equated with their extensions. The file transcribes the RDFS conditions and all 16 domain axioms, 16 range axioms, six hierarchy axioms, and three infinite container schemas. Ordinary datatype-extension equality follows from RDF conditions instead of being duplicated. The langString extension's equality with actual tagged-literal denotations remains explicit.

`RDFSRules.lean` records all 14 named RDFS rules and proves truth preservation under a single assignment. The proof relation composes rules with premise triples and both axiom families. Its soundness theorem produces graph entailment, preserving witness sharing throughout. A further theorem connects derived memberships in disjoint recognized datatype spaces to RDFS-unsatisfiability. This is soundness, not a complete rule procedure, termination theorem or full datatype decision algorithm.

## Review method and reading route

Read `RDF11/Statements.lean`, `RDF11/Syntax.lean` and `RDF11/Simple.lean`: 359 lines together in this increment. Statements contains explicit types, source anchors and one-line aliases for eight headline topics, with both clauses of the empty-graph result. Supporting definitions and full proofs remain accessible through imports and the viewer's actual dependency links. The short route is an orientation for review, not a replacement for inspecting those dependencies.

Interpolation and compactness are explicit source names; the other headline names are local reviewer labels. Binary merging is labelled as binary. Instance/interpolation scope stays ordinary where required. Compactness assumes a finite ordinary conclusion. “Skolemization lemma” means fresh-vocabulary conservativity here, not the separate exact-lifting equation `H = sk(H′)`.

The repository skill at `.agents/skills/rdf11-spec2lean/SKILL.md` records the continuing workflow: AI close reading; byte-pinned source; character accounting; explicit contextual referents; distinct extraction/formalization reviews; readable claims and glosses; frozen declaration grounding; and verification before publication. HTML locators find selected passages and do not perform semantic extraction. Conditions represented as fields define admissible interpretations; compilation alone does not establish model existence or fidelity to the prose.

There are 125 mapped records among 195 preliminary claims, including partial mappings. The registry inventories 28 formal files and 972 declarations; the elaborated closure contains 5,432 declarations. The new standard-library dependencies come mainly from real string/character normalization. They were explicitly inspected and enrolled. No new logical axioms were added; the allowed set remains `propext`, `Classical.choice`, `Quot.sound`.

## Fidelity boundaries and open work

- Literal syntax and vocabulary spellings are still interfaces. Legal-form coverage, concrete equality and actual namespace/index encodings need separate proofs.
- Concepts specifies lowercase tag values. The normalized pair space respects that distinction, but the abstract literal interface does not yet prove that every legal pair has a literal. RDFS retains the exact literal-image condition rather than assuming that coverage.
- The D table explicitly fixes ordinary datatype IRI denotations. It does not separately state the corresponding langString equality. The reconstruction does not invent an extra equality to an arbitrary canonical datatype entity.
- Recognized RDF value spaces must be fully realized in the model carrier. This requirement connects an external-value representation to the semantic set equality; it must not be confused with an executable conversion routine.
- The printed datatype/RDFS entailment directions are recorded as source-review questions alongside the proved model-class directions. No official erratum status is claimed.
- The additional-valid-triples table is not an axiom table. Its unqualified XMLLiteral/HTML class typings remain a recognition-scope question; optional recognition has not been silently strengthened.
- Full model existence, additional validity consequences, arbitrary-family merge, remaining generalized-syntax scope, exact Skolem lifting, rule completeness, concrete datatypes, datasets and other uncodified prose remain open.
- No parser, npm artifact, JS/WASM wrapper or W3C test runner is refined by this reconstruction. Preventing the earlier implementation failures still requires those paths to preserve the proved contracts.

## Validation

The full Lean 4.33.1 build, frozen inventory/dependency verification, seven rejection checks, nine Python tests, source-range regeneration and viewer generation pass locally. The headline aliases introduce no new proofs or assumptions. The completeness gate remains deliberately closed; expert reviews and implementation refinement are absent. The repository CI additionally exercises the generated viewer in real Chromium before deploying Pages.
