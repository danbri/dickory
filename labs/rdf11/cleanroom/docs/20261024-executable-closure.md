# Executable RDF/RDFS closure with exactness proofs

24 October 2026. Twenty-third working increment. The Lean evaluator computes the existing transcription of RDF 1.1 Semantics Appendix A for finite supplied graphs, returns each triple once, and decides membership in that closure. It does not establish the printed procedure's full entailment completeness or verify Factoidal's package.

## Source and extraction method

The source-reading agent used AI close reading of the pinned Semantics and Concepts documents. Parsing located the selected passages; search was not used to infer their meaning. The relevant Semantics locations are Appendix A's input/procedure paragraphs, its subsequent completeness and finite/polynomial assertions, `#dfn-grdfd1`, `#rdfs_patterns`, `#dfn-rdfs1`, and the vocabulary paragraph in `#notation-and-terminology`. Concepts supplies graph sethood and term identity. Existing source hashes and Unicode coordinates remain authoritative.

The derived claim `MT11-EXECUTABLE-CLOSURE-REFINEMENT` records the connection between an executable representation and that formal transcription. Its mapping is a theorem with explicit interface assumptions. `MT11-GENERALIZED-CLOSURE` and `MT11-FINITE-CLOSURE-COMPLEXITY` remain partial: source fidelity, unqualified finiteness and polynomial runtime are not settled by this increment. The catalogue contains 182 mappings among 223 preliminary records, with 13 open source questions and no accepted expert reviews. Counts are not compliance percentages.

## Connected proof chain

1. `ContainerDecoder` requires a computable inverse with `decode a = some n ↔ a = container n`. Injectivity of the encoding alone does not supply an executable inverse. Scanning includes datatype IRIs embedded in literals, even when unrecognized. The symbolic fixture uses zero for `rdf:_1`; a future concrete decoder must separately prove exact name correspondence.
2. `AxiomLists` certifies the fixed and indexed axiom lists. The executable fallback tests whether all selected axioms are already in the premise plus fixed axioms. A nonempty selected list can therefore trigger fallback. `seed_iff` proves exact equality with the previously defined `AxiomSeed`; duplicates in supplied lists do not change its set.
3. Each round evaluator has a two-way membership theorem against the existing inductive rule relation. Binary matching considers all ordered pairs, including a triple paired with itself. The zero-premise `rdfs1` facts are generated. GrdfD1 inspects the object position and the two base datatype names; it does not evaluate lexical-to-value maps, validate lexical syntax or generate fresh blanks.
4. `FiniteSaturation` deduplicates accumulated results. A nonterminal round strictly increases their length. All results remain within a finite carrier built from the K distinct supporting terms, so a K³ round budget suffices to reach a fixed point. `run_exact` combines soundness with leastness of inductive derivability. Termination alone would not prove saturation.
5. `rdf_exact` and `rdfs_exact` identify the result sets with `RDFClosure` and `RDFSClosure`. Certified enumerations carry uniqueness and exact membership. The count-respects-graphs theorems ensure that duplicate or reordered presentations of the same premise and conclusion sets yield equal result cardinalities. Satisfaction equivalence reuses the established semantic soundness results and their model assumptions.

Read [ExecutableClosure.lean](../RDF11/ExecutableClosure.lean) for the public results, then follow its imports through seed, rule and saturation proofs. The short Statements/Syntax/Simple review route remains 393 lines. Every new authored declaration has a draft English gloss; these explanations and source mappings still require expert review.

## Runtime evidence and boundaries

`python3 tools/closure_execution.py` exercises twelve project-owned symbolic fixtures through Lean's executable evaluator. They cover duplicate inputs/results, both branches of fallback including nonempty selected axioms, embedded datatype IRIs, a large isolated container index, object-only literal typing, binary self-joins, zero-premise datatype facts, the known selection obstruction, missing indexed tautologies and distinct lexical spellings. These are execution regressions alongside universal kernel-checked proofs, not proofs obtained by native evaluation or imported W3C fixtures.

Two additional rejection probes attempt to certify an incorrect decoder and an unsaturated zero-fuel result. Publication requires passing executable evidence and publishes that report alongside the existing verification reports. The review viewer exposes the actual implementation, exactness proof, sufficient-fuel hypothesis, uniqueness certificate and negative-decision scope.

The evaluator takes finite lists, computational equality, a datatype projection and an exact decoder. Abstract term equality is not yet connected to validated concrete IRI/literal syntax. The existing finiteness theorem also covers an infinite conclusion with finitely many selected indices; this executable interface is narrower. A cubic carrier/round bound is not a machine-time bound: equality, decoding, datatype projection, matching and deduplication costs remain unformalized. Final blank-instance search, larger recognized datatype sets, fresh-blank rdfD1, W3C parser fixtures and JS/WASM refinement remain separate work.

Failure of this closure membership test is not a justified semantic non-entailment verdict. The printed procedure retains the already proved selection obstruction, with its separate consistency witness and open source-review question. Its definition has not been changed to repair that issue.

## Relation to editions, errata and proposals

This is a concrete example for the [multi-baseline design](20261023-spec-versions-and-families.md): the printed procedure, a proposed correction and a later edition must remain separately identifiable. Exact implementation of a procedure and completeness for an entailment regime are different claims. A repaired procedure must receive its own definition, source/correction record and bridge obligations before any review or coverage can transfer. No cross-edition compatibility is proved here.


## Deliberate registry audit

This increment adds 259 local declarations: 107 authored declarations (including six structure fields) with curated glosses and 152 generated structure, equation, pattern, simplifier and proof helpers with explicit parent links. The standard natural-number recursor expresses the saturation loop directly. Existing declarations retain their type, kind and module attribution. The two root import files and generated source-range snapshot change; six new formal files are enrolled. No archived source bytes change.

The inventory now contains 2,712 local declarations across 82 formal files, with an elaborated dependency closure of 7,413 declarations. No new foundation module or logical axiom is admitted. The permitted logical axioms remain propext, Classical.choice and Quot.sound; no local declaration is unsafe or an added axiom.


## Local validation

The 84-job Lean build and full source/registry verifier pass. All ten rejection checks, twelve executable regressions and fifteen Python unit tests pass. The review viewer regenerates, the site stages eight explicit files with local links checked, JavaScript syntax checks pass, and the updated methodology skill validates. Seven browser checks are added for the executable proof chain and its published regression report; actual Chromium execution is a required CI gate before Pages deployment. Full specification coverage and expert acceptance remain incomplete.
