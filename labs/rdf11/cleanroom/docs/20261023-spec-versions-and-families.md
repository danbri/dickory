# Multiple editions and connected specification families

23 October 2026. Architecture proposal for review; the multi-baseline catalogue, comparison UI and cross-family Lean bridges described here are not yet implemented. Requirements VER-01 through VER-12 in [Spec2Lean](../../spec2lean-requirements.md#21-editions-errata-proposals-and-related-specification-families) are the acceptance contract.

## Keep authorities distinct; make relationships explicit

The project should preserve each source edition and prove relationships between its formalization and other editions. It should not merge RDF 1.1, RDF 1.2, errata and proposals into one mutable account of what RDF means. They can coexist in the same repository and share code without sharing an unqualified approval or coverage claim.

Use these distinct identities:

| Object | Identity and purpose |
|---|---|
| Family | RDF, OWL or SPARQL; a navigation grouping, not a single semantic regime |
| Document work | RDF Semantics, RDF Concepts, SPARQL Query, OWL Direct Semantics, etc. |
| Edition | Dated publication or editor-draft commit, with publisher status and predecessor links |
| Source asset | Exact response bytes and digest, coordinate indexes and redistribution metadata |
| Baseline bundle | Selected editions/assets, correction overlays, imported dependencies, datatype assumptions, regimes and evidence policy |
| Claim occurrence | An edition-specific English/symbol claim and all source/context ranges |
| Claim lineage | Reviewed many-to-many correspondence between occurrences; may represent splits, merges or competing readings |
| Formal bridge | A precisely scoped relationship between formalizations, with proof or counterexample evidence |

Keep the current MT11 claim IDs. Introduce new occurrence IDs for a new edition and use explicit lineage edges to connect them. Stable family concepts such as graph or interpretation are useful for finding related material; they must not assert that the definitions are unchanged. Source and claim content hashes identify versions, while stable identifiers identify their history.

An HTML serialization change can create a new asset without changing a mathematical claim. Conversely, unchanged wording may acquire a different meaning when its imported definitions, qualifications or datatype theory change. Both cases require visible provenance.

## What the official sources already require us to distinguish

The RDF 1.1 baseline remains the [2014 Semantics Recommendation](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/). As checked on 23 October 2026, the current RDF 1.2 Semantics publication is the [24 September 2026 Candidate Recommendation Draft](https://www.w3.org/TR/2026/CRD-rdf12-semantics-20260924/), explicitly a work in progress. Its change notes describe triple terms, an additional built-in datatype and an entailment rule said to have been missing from RDF 1.1. These are separate kinds of change; the retrospective explanation does not rewrite our archived 2014 source or itself settle the status of an RDF 1.1 erratum.

OWL 2 provides distinct [Direct Semantics](https://www.w3.org/TR/2012/REC-owl2-direct-semantics-20121211/) and [RDF-Based Semantics](https://www.w3.org/TR/2012/REC-owl2-rdf-based-semantics-20121211/). The latter includes a scoped correspondence theorem. The [OWL overview](https://www.w3.org/TR/2012/REC-owl2-overview-20121211/#Semantics) explains the two interpretations of ontologies; it is not a license to identify their model classes.

The dated references in OWL 2 RDF-Based Semantics and [SPARQL 1.1 Query](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#references) name the 2004 RDF documents. Our dependency graph must retain those versions. A connection to RDF 1.1 is an additional compatibility obligation, even when everyday implementations combine these technologies.

[SPARQL 1.1 Query evaluation](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#sparqlAlgebra) uses solution mappings and multisets, with sequence operations for query modifiers. [SPARQL 1.1 Entailment Regimes](https://www.w3.org/TR/2013/REC-sparql11-entailment-20130321/) supplies the semantic connections to RDF, RDFS and the OWL semantics, with regime-specific restrictions. RDF graph sethood and duplicate-bearing query results therefore need separate formal types and observation contracts.

These links are discovery/design references. They do not claim that the additional editions have already been archived, range-accounted, extracted or formalized in this repository.

## Change records and errata

Record textual movement/editing independently of mathematical change. A comparison may find unchanged wording but changed dependencies, or rewritten wording with a proved equivalent formula. Mathematical relations include equivalence, one-way implication, conservative extension on a named fragment, incompatibility and unresolved correspondence. State direction and hypotheses; a generic "compatible" badge is insufficient.

Store official errata and proposed corrections as separate pinned evidence. A baseline can explicitly adopt an overlay, producing a new bundle while retaining the uncorrected baseline. Record issuer, status, date, original ranges, replacement reading, affected claims and decision. An editor's draft, community proposal or local AI concern is not an adopted correction. Mutually inconsistent alternatives may coexist as separate experimental bundles; they cannot silently form one accepted baseline.

The current open source questions provide a practical test: a later draft may repeat the same sentence, change it, or document a correction. Each observation should link to the existing question, with an independently reviewed resolution for each affected baseline.

## Lean organization and bridge obligations

Retain RDF11's source-facing definitions. Add edition-specific modules such as RDF12, OWL2.Direct, OWL2.RDFBased and SPARQL11 when actual formalization begins. Factor shared mathematics only where its assumptions and source applications are explicit. Existing general set and finite-enumeration proofs are likely candidates; source-specific interpretation fields and term constructors should not be moved into an assumed universal model merely to remove duplication.

A proposed RDF11-to-RDF12 entailment-conservativity theorem would have a shape like:

```text
For G and H in a specified old fragment, with specified datatype parameters:
  Entails11(G, H) iff Entails12(embed(G), embed(H)).
```

This is a proposed proof obligation, not an established result. Define the syntax translation, show that it preserves term identity and blank sharing, and prove the relevant interpretation restriction/extension conditions. If only one direction follows, publish only that direction. New names, triple terms, language-literal features, regimes or datatype assumptions may require restrictions or expose counterexamples.

OWL needs separate syntax mappings and its own correspondence proof. SPARQL needs observation-specific bridges: equality of solution mappings alone does not establish multiplicity, ordering, error behavior or CONSTRUCT graph correctness. Update and protocol conformance are further surfaces. Versioned parsers, codecs and runtime representations must eventually refine the selected bundle, not a floating notion of the latest standard.

## Reviews, comparison UI and CI

Provide side-by-side annotated source and claim views with an edition/bundle selector. Each row shows source changes, English/symbol changes, Lean type/body changes, changed dependencies, bridge evidence and review state. Retain partial/unmapped filters and glosses. Colour can help navigation but every distinction also needs a text label.

Source-to-claim review and claim-to-Lean review remain separate for each baseline. A third comparison review assesses lineage and intended compatibility; it does not replace either original review. Carry-forward decisions bind to exact unchanged inputs or explicit transport evidence. Dependency changes must reopen the affected transitive closure while preserving previous acceptance as history.

CI should reject cross-hash range reuse, a shared rule name resolving to the wrong edition, proposal proofs credited to a Recommendation, unadopted corrections, stale dependency approvals and one-way bridges displayed as equivalences. Coverage reports need separate denominators for each baseline and a separate bridge-completeness view. Test expectations and comparators are versioned too; equal fixture bytes do not prove equal applicability.

## Implementation sequence

1. Add baseline, edition and dependency identifiers around the existing RDF 1.1 catalogue while preserving IDs, archived bytes and pending review states.
2. Pin one dated RDF 1.2 bundle and construct a reviewed change/lineage catalogue before attempting wholesale proof reuse. Start with the graph/term boundary and one recurring headline result.
3. Exercise an original-versus-corrected overlay and a competing proposal in the catalogue and comparison viewer; require the separation rejection checks.
4. Build one typed translation and prove its actual compatibility scope, including negative examples or limitations where needed.
5. Inventory the dated OWL 2 and SPARQL 1.1 dependency closures. Start OWL's two semantic targets and SPARQL basic graph patterns/multiset algebra as separate formalization tracks, connected to the existing RDF foundation only through explicit bridges.
6. Connect pinned W3C fixtures and product refinement to those named bundles and regimes; expand through the full specified obligations without treating tests as exhaustive.

This architecture prepares those tracks now while the RDF 1.1 formalization continues. It does not count planned OWL, SPARQL or RDF 1.2 work toward current coverage.

## First implementation milestone: one claim across two editions

Clarification on 24 October 2026. Start with graph sethood and its term/triple dependencies. Preserve the existing RDF 1.1 records; add one pinned RDF 1.2 source bundle and new claim occurrences. The sentence that a graph is a set of triples may remain mathematically familiar while the definition of a triple changes. Text similarity must therefore propose a lineage link, not approve semantic equivalence. Even an unchanged Lean theorem type can change meaning through a changed definition in its dependency closure.

The minimum review packet should contain:

1. Both source assets and their independent Unicode ranges, with each occurrence's resolved context and normative status.
2. Both English/symbol claims and the exact versions of the definitions they depend on.
3. A proposed correspondence, with separate syntax and semantic obligations. A graph embedding must preserve term identity and blank sharing; entailment preservation and reflection need their own theorems and hypotheses.
4. A proof or counterexample tied to the exact Lean environment and dependency closure. A declaration name or printed type alone is not the evidence identity.
5. Three review decisions: source extraction in each edition, fidelity of each formalization, and correctness of the correspondence. None can substitute for another.

Acceptance should be demonstrated by changing a dependency while leaving the source sentence unchanged: the comparison approval must become stale, the old approval must remain in history, and neither edition's coverage may silently inherit the other's status. A second exercise should adopt a proposed correction in an experimental bundle while leaving the Recommendation bundle unchanged. There is no requirement to create a Git branch for either exercise.

The baseline manifest should act as a semantic lockfile: exact source and catalogue versions, adopted corrections, imported editions, datatype assumptions, entailment regime, Lean environment and test expectations. Hashes make the evidence reproducible; expert review establishes whether the selected dependencies and assumptions are faithful. A rolling “latest RDF” label may help discovery but cannot identify a checked baseline.

For OWL and SPARQL, prepare document/dependency inventories now and defer implementation breadth until these baseline and bridge mechanisms work. Start OWL with the relationship between its RDF-Based and Direct semantics; start SPARQL with basic graph patterns, solution multiplicity and the chosen entailment regime. Keep the cited 2004 RDF baseline visible when relating either to our RDF 1.1 work. Each track can reuse proved mathematics through explicit imports, but carries its own source-accounting and fidelity obligations.

## A concrete correction exercise from the current RDF 1.1 work

The [executable-closure increment](20261024-executable-closure.md) separates two claims that a version comparison must not collapse: the evaluator computes the transcribed Appendix A procedure exactly, while that procedure has a checked entailment-completeness obstruction under the current source reading. Both results can hold together. Neither establishes an official erratum or a corrected algorithm.

Use that case to exercise correction records after the graph-set comparison. Keep the original source occurrence, original procedure and exactness theorem. Give each proposed repair its own English claim, definition and experimental baseline. Record whether it changes axiom selection, rule application, supported inputs or the promised observation. A repair may intentionally change closure membership while seeking to preserve soundness and restore completeness; "equivalent algorithms" would then be the wrong bridge obligation. Source-review resolution, proof of the repair's claimed property and adoption in a baseline remain distinct decisions.

The comparison viewer should expose these alongside one another: **printed procedure**, **checked implementation**, **open completeness question**, **proposed repair**, and **adoption status**. A later RDF edition repeating or changing the passage adds evidence to that review; it does not overwrite the original occurrence or automatically settle the question for RDF 1.1. These comparison records and UI are still proposed infrastructure.

## Cross-family review boundaries

Rechecked against the W3C publications on 24 October 2026. Keep three different relationships in the directory: a document's dated dependency, a semantic extension under stated model conditions, and a proved translation between versions or languages. A bibliographic reference records the first relationship; it does not establish the other two. The existing RDF11 extension interfaces may support later proofs, but are not themselves OWL or SPARQL conformance evidence.

The [OWL 2 correspondence theorem, §7.2](https://www.w3.org/TR/2012/REC-owl2-rdf-based-semantics-20121211/#Correspondence_Theorem) is a useful test of faithful extraction. Its statement includes corresponding datatype maps, mutual OWL 2 DL restrictions and the existence of suitable graph pairs equivalent under Direct Semantics. Its final entailment implication runs from Direct to RDF-Based Semantics for those pairs. Do not turn that into an unconditional iff for the original RDF graphs. Separate the construction obligations, hypotheses and implication in the claim directory before attempting reuse of RDF model proofs.

For SPARQL, begin with [basic graph patterns, §18.3](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#BasicGraphPattern), then the algebra operations and their multiplicities. Our finite instance search answers existence and returns one certified substitution. A query evaluator must expose the specified solution mappings and their multiplicities; an existential decision cannot establish that contract. [Entailment Regimes](https://www.w3.org/TR/2013/REC-sparql11-entailment-20130321/) additionally defines graph/query admissibility and error conditions. Those obligations need their own claims even when the underlying entailment relation is already formalized.

The first cross-family implementation should therefore inventory the dated source dependencies and extract one complete boundary contract per track. Keep the full OWL and SPARQL catalogues visibly incomplete while that work proceeds. Reuse a shared theorem only after its application to the target's definitions has been checked and separately source-reviewed.
