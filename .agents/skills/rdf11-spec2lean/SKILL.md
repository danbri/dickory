---
name: rdf11-spec2lean
description: Extend and review Dickory's source-first RDF 1.1 Semantics formalization, preserving source traceability, readable headline statements and explicit assurance boundaries.
---

# RDF 1.1 specification to Lean methodology

Work in `labs/rdf11/cleanroom`. This is a separate reconstruction from pinned W3C texts, not a port of Factoidal implementation proofs. Prior exposure to that implementation is disclosed in the README. Do not silently import its definitions or claim its npm/WASM wrapper is verified.

## Read and extract

Use AI close reading for semantic assertion extraction. HTML parsing or text search may locate already selected passages, but cannot determine their meaning or completeness. A source-reading subagent is appropriate when requested; keep its findings and code work connected through explicit source selectors. Consult RDF Concepts where Semantics imports its definitions.

Preserve the archived source bytes and SHA-256 identities. Source coordinates are Unicode scalar intervals `[start,end)`, with explicit conversions to UTF-8 bytes and browser UTF-16 offsets. Never normalize newlines or Unicode in the authoritative source. Every character has an accounting disposition; unresolved text is not covered formal semantics.

Extract definitions, conditions, general requirements and mathematical consequences, not only named entailment rules. Record normative/informative status. Replace indexicals such as “other”, “this” and “above” with explicit referents, and record the antecedent passages. Whole-element highlights may contain still-unextracted assertions.

## State and prove

Use W3C notation (`IR`, `IP`, `IEXT`, `IS`, `IL`, `IC`, `ICEXT`, `LV`) and mathematical distinctions. Graphs are sets; triple syntax, resource values, literal syntax and datatype identities must not collapse accidentally. Semantic roles may overlap where W3C permits them.

Keep a short review route: `RDF11/Statements.lean`, `Syntax.lean`, then `Simple.lean`. The headline file contains one-line theorem aliases with specification section anchors and plain-English scope notes. Aliases inherit the original theorem's full type; do not restate a weaker result under an unqualified stronger title. In particular, retain ordinary/generalized syntax boundaries, binary versus arbitrary-family merge, finite-conclusion compactness and Skolem freshness. The specification explicitly names interpolation and compactness; other headline titles are local review names. Skolem conservativity does not discharge the separate exact-lifting equation.

Connect new proofs to existing definitions and results. Rule soundness must preserve one blank-node assignment across premises and derivations. Distinguish soundness, completeness, model existence and executable refinement. A semantic condition represented as a structure field is an assumption defining a model class, not a theorem establishing that the class is inhabited.

When formalizing a stated procedure, preserve its exact axiom selection, fallback conditions and rule-premise positions. A stronger semantic helper does not authorize broadening the named rule. Appendix A selects container axioms from the conclusion and tests whether step 2 added triples; GrdfD1 has an object-literal premise. Record possible omissions as review questions. Establish the claimed semantic entailment, failure of the specified procedure, and any required consistency witness before describing a candidate as a checked counterexample to completeness.

Datatype meanings are fixed external parameters until a concrete library is proved. One shared value domain permits overlapping value spaces. `rdf:langString` uses normalized string/tag pairs, with ASCII-only lowercase tag values. Keep its literal-image condition explicit. Do not require a global injection of all datatype values into every simple model when D is empty. Record literal/vocabulary coverage and representation obligations rather than silently assuming concrete XSD or BCP47 correctness.

No `sorry`, added axioms, unsafe local definitions or native-decision proof shortcuts. Preserve unresolved source questions rather than changing a formal definition to make a desired result compile. The reversed entailment arrows and optional datatype typing questions require expert disposition, not silent correction or unqualified erratum claims.

## Map and explain

Update `catalogue/mapping-review.json` and regenerate `claims.json` plus `Audit/Snapshot.lean` with `tools/source_catalogue.py`. Bind exact Lean declarations; qualify partial mappings. Add context resolutions and open questions where needed. Extraction and formalization expert reviews remain pending until actual review evidence is supplied.

Every authored declaration needs a curated gloss in `catalogue/lean-glosses.json`. Generated helpers may inherit an explicitly labelled parent/role explanation. Explain conditions and important exclusions in ordinary language. The viewer must expose actual Lean bodies, elaborated types, dependencies and connected claims; a name/type list alone is insufficient.

Explicitly review and update the frozen registry: new/changed file hashes, declaration signatures, reverse claim bindings, grounding support and library modules. Inspect elaborated dependency/axiom closure. Do not make verification automatically enroll new files or declarations. Unimported Lean files are still inventoried; temporary formal experiments must not become silent cruft.

## Verify and publish

Use the pinned Lean/Python versions. Run `python3 tools/verify.py`, `python3 tools/negative_checks.py`, `python3 -m unittest discover -s tools -p 'test_*.py'`, and `python3 tools/review_viewer.py`. `--require-complete` must keep failing while any completeness, review or implementation-refinement obligation remains. Build the site with repository-root `python3 tools/build_site.py`; Chromium CI must pass before Pages deployment.

Keep the README, this skill and a dated worknote aligned with the actual increment: source locations, theorem scope, explicit parameters, checked counts, verification and remaining gaps. Counts include partial mappings and are not compliance percentages. Distinguish checked formal results, draft English mappings and absent implementation verification.

The user has authorized experimental work directly on `main` and Pages publication. Preserve unrelated changes, fetch before pushing, avoid force pushes, and verify the deployed revision. When asked to commit the current increment, finish its necessary verification and commit it without waiting for full-spec completion.
