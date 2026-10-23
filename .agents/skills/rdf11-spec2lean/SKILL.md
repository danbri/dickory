---
name: rdf11-spec2lean
description: Extend and review Dickory's source-first RDF 1.1 Semantics formalization, preserving source traceability, readable headline statements and explicit assurance boundaries.
---

# RDF 1.1 specification to Lean methodology

Work in `labs/rdf11/cleanroom`. This is a separate reconstruction from pinned W3C texts, not a port of Factoidal implementation proofs. Prior exposure to that implementation is disclosed in the README. Do not silently import its definitions or claim its npm/WASM wrapper is verified.

## Read and extract

Use AI close reading for semantic assertion extraction. HTML parsing or text search may locate already selected passages, but cannot determine their meaning or completeness. A source-reading subagent is appropriate when requested; keep its findings and code work connected through explicit source selectors. Consult RDF Concepts where Semantics imports its definitions.

Preserve the archived source bytes and SHA-256 identities. Source coordinates are Unicode scalar intervals `[start,end)`, with explicit conversions to UTF-8 bytes and browser UTF-16 offsets. Never normalize newlines or Unicode in the authoritative source. Every character has an accounting disposition; unresolved text is not covered formal semantics.

Extract definitions, conditions, general requirements and mathematical consequences, not only named entailment rules. Read the surrounding normative prose together with condition tables. A table omission is not permission to omit a prose obligation: correct an underconstrained model when the prose supplies the requirement, and record the correction rather than treating it indefinitely as an open question. Record normative/informative status. Replace indexicals such as “other”, “this” and “above” with explicit referents, and record the antecedent passages. Whole-element highlights may contain still-unextracted assertions.

## State and prove

Use W3C notation (`IR`, `IP`, `IEXT`, `IS`, `IL`, `IC`, `ICEXT`, `LV`) and mathematical distinctions. Graphs are sets; triple syntax, resource values, literal syntax and datatype identities must not collapse accidentally. Semantic roles may overlap where W3C permits them.

Preserve §5's global name scope in interpretation witnesses: a finite vocabulary is a pre-interpretation, not automatically a full RDF 1.1 interpretation. Prefer constructions generic over arbitrary IRI/literal domains with total IS and permitted partial IL, or prove the extension from a reduced vocabulary. Full name-domain coverage does not require an infinite resource carrier or defined denotations for every literal. Keep the source's infinite name-mapping assertion separate from model-carrier cardinality, and do not claim it proved without a concrete domain/cardinality argument.

Keep a short review route: `RDF11/Statements.lean`, `Syntax.lean`, then `Simple.lean`. The headline file contains one-line theorem aliases with specification section anchors and plain-English scope notes. Aliases inherit the original theorem's full type; do not restate a weaker result under an unqualified stronger title. In particular, retain ordinary/generalized syntax boundaries, binary versus arbitrary-family merge, finite-conclusion compactness and Skolem freshness. The specification explicitly names interpolation and compactness; other headline titles are local review names. Skolem conservativity does not discharge the separate exact-lifting equation.

Connect new proofs to existing definitions and results. Rule soundness must preserve one blank-node assignment across premises and derivations. Distinguish soundness, completeness, model existence and executable refinement. A semantic condition represented as a structure field is an assumption defining a model class, not a theorem establishing that the class is inhabited.

Before proving model existence, check the external parameter compatibility that the conditions require. A model-class structure can be empty. Keep sufficient constructor hypotheses separate from specification requirements and necessary conditions; do not invent a blanket exclusion of namespace IRIs from datatype recognition. Datatype identification and lexical-to-value maps may have aliases, while distinct fixed values must remain distinct under realization. Reuse the D-model literal proof where possible. For RDFS, reconcile full recognized value spaces with the literal-image equality for langString: every language value needs an actual tagged-literal representative. Explicitly distinguish prescribed built-in meanings from arbitrary inhabitants of the abstract datatype interface.

When formalizing a stated procedure, preserve its exact axiom selection, fallback conditions and rule-premise positions. A stronger semantic helper does not authorize broadening the named rule. Appendix A selects container axioms from the conclusion and tests whether step 2 added triples; GrdfD1 has an object-literal premise. Record possible omissions as review questions. Establish the claimed semantic entailment, failure of the specified procedure, and any required consistency witness before describing a candidate as a checked counterexample to completeness.

Datatype meanings are fixed external parameters until a concrete library is proved. One shared value domain permits overlapping value spaces. Every recognized datatype IRI, including langString, denotes its fixed datatype. Index actual value spaces by datatype identity so aliases remain coherent. Distinguish the absent language L2V evaluator from its nonempty-capable pair value space; representing the former as nowhere-defined must not collapse the latter into an empty ordinary range. `rdf:langString` uses normalized string/tag pairs, with ASCII-only lowercase tag values. Keep its literal-image condition explicit. Do not require a global injection of all datatype values into every simple model when D is empty. Record literal/vocabulary coverage and representation obligations rather than silently assuming concrete XSD or BCP47 correctness.

For datasets, reuse ordinary graph syntax and one blank domain across the default graph, named-graph contents and graph-name keys. Preserve present empty named graphs separately from absent keys. Use one global blank bijection for dataset isomorphism, including blanks appearing only as names of empty graphs; per-graph equivalence does not preserve sharing. Keep graph-name pairing separate from denotation. Semantics §10's MAY/SHOULD language does not mandate one dataset satisfaction relation. Label quad projections and their information-loss results as derived representation obligations, distinct from the informative interoperability advice.

Represent dataset recommendations as explicitly adopted policy conditions and preserve their modal force in the catalogue. An arbitrary truth-relation interface does not certify an admissible RDF semantic extension. Distinguish restricting models with truth fixed from changing truth by a dataset-dependent condition; only the former automatically preserves entailment. Label truth-preserving model maps as sufficient conditions. Check blank-identity dependence before asserting policy invariance under dataset isomorphism. Matching-name graph comparisons are illustrative necessary conditions: record whether they align keys, share witnesses and include the default. A name-denotation example needs an explicit graph-object embedding and an exact interpretation-regime boundary; do not infer a required inequality from the absence of a required equality.

No `sorry`, added axioms, unsafe local definitions or native-decision proof shortcuts. Preserve unresolved source questions rather than changing a formal definition to make a desired result compile. The reversed entailment arrows and optional datatype typing questions require expert disposition, not silent correction or unqualified erratum claims.

## Map and explain

Update `catalogue/mapping-review.json` and regenerate `claims.json` plus `Audit/Snapshot.lean` with `tools/source_catalogue.py`. Bind exact Lean declarations; qualify partial mappings. Add context resolutions and open questions where needed. Extraction and formalization expert reviews remain pending until actual review evidence is supplied.

Every authored declaration needs a curated gloss in `catalogue/lean-glosses.json`. Generated helpers may inherit an explicitly labelled parent/role explanation. Explain conditions and important exclusions in ordinary language. The viewer must expose actual Lean bodies, elaborated types, dependencies and connected claims; a name/type list alone is insufficient. Check structure projections too: compiler metadata may cover only the field identifier. Show and label the enclosing structure from its compiler range, preserve the original selection, and never pass off the name alone as the defining condition.

Explicitly review and update the frozen registry: new/changed file hashes, declaration signatures, reverse claim bindings, grounding support and library modules. Inspect elaborated dependency/axiom closure. Do not make verification automatically enroll new files or declarations. Unimported Lean files are still inventoried; temporary formal experiments must not become silent cruft.

## Verify and publish

Use the pinned Lean/Python versions. Run `python3 tools/verify.py`, `python3 tools/negative_checks.py`, `python3 -m unittest discover -s tools -p 'test_*.py'`, and `python3 tools/review_viewer.py`. `--require-complete` must keep failing while any completeness, review or implementation-refinement obligation remains. Build the site with repository-root `python3 tools/build_site.py`; Chromium CI must pass before Pages deployment.

Keep the README, this skill and a dated worknote aligned with the actual increment: source locations, theorem scope, explicit parameters, checked counts, verification and remaining gaps. Counts include partial mappings and are not compliance percentages. Distinguish checked formal results, draft English mappings and absent implementation verification.

The user has authorized experimental work directly on `main` and Pages publication. Preserve unrelated changes, fetch before pushing, avoid force pushes, and verify the deployed revision. When asked to commit the current increment, finish its necessary verification and commit it without waiting for full-spec completion.
