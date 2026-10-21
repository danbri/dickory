# First source-first formalization increment

Date: 2026-10-21. Scope: RDF 1.1 Semantics, initially sections 4–5.3, with imported Concepts syntax. All work is under `_LEAN/cleanroom`.

## Fidelity to the W3C mathematics

| W3C notation or concept | Lean representation | Adaptation / outstanding obligation |
|---|---|---|
| Set of triples | `Graph := Set Triple`; `Set α := α → Prop` | Set equality is extensional. No finite-graph assumption. |
| Ordinary / generalized triple | `Triple` / `GeneralizedTriple` | Ordinary predicate must be an IRI; generalized positions may be any term. |
| IRI, literal, blank node | Distinct constructors of `Term` | Domains are abstract type parameters. RFC 3987, BCP47, concrete literal construction and RDF term equality are not yet discharged. |
| Interpretation `I` | `SimpleInterpretation Iri Literal U` | Ambient type `U` permits overlapping `IR` and `IP`. |
| `IR` | `I.IR`, with `IR_nonempty` | The source’s nonemptiness condition is a required proof field. |
| `IP` | `I.IP` | It is not silently made a subset of `IR`. |
| `IEXT : IP → P(IR × IR)` | `I.IEXT` on property/resource subtypes | Subtype proofs enforce the exact endpoint restrictions. |
| `IS : IRI → IR ∪ IP` | `I.IS` | Every denotation carries evidence of membership in the union. |
| Partial `IL : Literal ⇀ IR` | `I.IL : Literal → Option I.Resource` | `none` means undefined, not a distinguished resource. |
| Blank-node mapping `A` | `I.Assignment Blank` with `AssignmentOn G A` | Partial ambient function, constrained to be defined exactly on G’s blank nodes. |
| `[I+A](E)` | `I.denote A E` | One function with explicit partial denotation. Agreement on names is definitional. |
| Triple truth | `I.TripleTrue A t` | Property membership, resource membership and extension membership all required. |
| Graph truth | `I.GraphTrue A G` | All member triples true under the same A. |
| `I` satisfies `G` | `I.Satisfies G` | Existential A outside universal triples. Ground correspondence is proved. |
| Simple entailment | `SimplyEntails G E` | All carrier types/interpretations in arbitrary fixed Lean universe u; universe-polymorphic definition. |
| Merge | `merge G H` over `Sum B₁ B₂` | Binary representative with fresh copies of all blank nodes. Identical up to renaming is not confused with literal set equality. |
| Finite graph storage | `Enumeration G` | Engineering refinement, not the mathematical definition of a graph. |

The function notation `G t` in source means membership of triple t in G. Predicate sets avoid introducing a finite representation or an additional mathematical library at this stage. Lean’s `Prop` expresses the source’s true/false conditions; absence of a proof is not an executable “false” result.

The single-point interpretation used to prove simple satisfiability is a witness model only. It does not restrict interpretation universes or assume the graph is finite.

The source’s generalized-syntax statement is recorded separately. The implemented blank-to-blank renaming theorem does not discharge all substitutions by names. In particular, generalized predicate positions and the distinction between IP and IR must be reviewed before asserting the unrestricted interpolation/instance claims.

A [separate checked countermodel](generalized-instance-question.md) makes that review question concrete. It preserves the transcribed domains and leaves the source interpretation unresolved instead of adding an unstated IP-subset-IR assumption.

## Source accountability and review

The byte-identical snapshots are:

| Document | SHA-256 | Unicode scalars |
|---|---|---:|
| Semantics, 2014-02-25 | `a4bc1dc53bc66fb7d57cd4b646e2527e35dbcce74fc54d8dd59beb255a830f80` | 139,975 |
| Concepts, 2014-02-25 | `3838c992097f72ee8784b6c96194d9879f86f2e08f53ced5a05aa4031750c5ac` | 120,796 |

The general partition theorem proves every position within the declared limits belongs to exactly one atom. A second theorem proves that each atom has nonempty, valid catalogue references. These are instantiated for both documents, including unresolved records, using kernel-evaluated `decide`.

This is a **draft structural certificate**. The SHA-256 calculations, strict UTF-8 decoding, scalar/byte/UTF-16 boundary construction, and generated Lean data are checked by Python and remain in the trust boundary. Lean does not itself prove that those digests hash those files. No accepted complete-accountability certificate is claimed while unresolved records remain.

Passage selection followed AI close reading of the original prose, tables and context. HTML parsing locates selected passages; it does not decide which assertions exist. Some selected passages are whole paragraphs, tables or a section. Their association with a claim does not establish exhaustive extraction of their contents.

The catalogue separates original paraphrase, explicit English statement, Lean symbol bindings, relation strength, limitations, extraction review and formalization review. Examples of context closure include resolving “The final condition” to the ground-graph truth row and preserving the interpolation-to-consequences inference link. Exact subphrase/antecedent character ranges and the full review acceptance workflow remain to implement.

## Declaration and file hygiene

The frozen registry lists all 13 local Lean files and all 370 declarations, including recursors, constructors, generated decision procedures and auxiliary proofs. A module is not exempt merely because nobody imports it.

The evidence extractor traverses constants in **elaborated types and bodies**, recursively, including implicit dependencies. The resulting closure has 2,323 declarations. Local declarations must have an explicit source mapping, support purpose, engineering-refinement purpose, or source-accountability purpose. Foundation records name their dependencies on claims or other foundations.

Logical axioms are restricted to `propext`, `Classical.choice` and `Quot.sound`. There are no local axioms, unsafe declarations or proof placeholders. The audit extractor and Python validator are trusted QA tools. Their successful traversal is not yet a kernel proof of the full grounding certificate; that remains a distinct requirement.

Registry membership is also not expert approval. A helper can have a declared purpose that a reviewer later judges inappropriate. The two review tracks must scrutinize that purpose and its use.

## Validation and boundaries

- Full `lake build`: passes for RDF11 and Audit.
- Concrete character partitions: compile and reference-check for both source snapshots.
- Dependency/registry/source-regeneration check: passes.
- Negative checks: reject an unimported Lean file, a nonexistent symbol binding, a missing elaborated dependency and a proof-placeholder axiom.
- Actual Lean compilation rejects an attempted duplicate-bearing finite enumeration.
- Complete-coverage mode returns a failing status for this incomplete draft.

The source viewer is an offline raw-HTML coordinate prototype. Its embedded source and JavaScript syntax are checked; rendered browser interaction has not been tested. It does not implement the full faithful-document presentation requirement.

W3C rdf11-mt tests are not rerun against this model: a proposition-valued semantics is not itself an executable entailment checker or RDF parser. The next test bridge should pin each fixture, parse its graph with explicit term identity, and distinguish proved positive witnesses, negative countermodels, unsupported regimes and parser failures. No previous implementation-test result is transferred to this project.

## Next formal work

1. Close imported syntax and identity obligations, especially literal term equality versus value equality.
2. Define general instances and graph isomorphism, then prove the interpolation lemma with the exact syntax/domain scope exposed.
3. Add datatype, RDF and RDFS interpretations following the source’s conditions and explicit external datatype obligations.
4. Refine an executable finite graph API through membership and uniqueness certificates; prove each exported boundary preserves those contracts.
5. Connect pinned W3C fixtures and wrapper regressions to that API, then bind validation to the actual shipped artifact.
6. Extend source extraction and independent reviews to every remaining normative and informative claim without treating rule codes as a complete inventory.

The previous Factoidal experiment and its patch remain separate. Nothing here changes the published npm module or asserts that its wrappers now satisfy these contracts.

