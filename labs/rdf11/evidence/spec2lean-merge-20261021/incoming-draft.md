# spec2lean: source-complete, reviewable RDF 1.1 Semantics → Lean 4 traceability

**Status:** proposed requirements for review; not a claim that coverage has been established.  
**Target repository:** `danbri/factoidal`  
**Suggested repository location:** `docs/spec2lean-requirements.md`  
**Initial source:** *RDF 1.1 Semantics*, W3C Recommendation, 25 February 2014, `https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/`.

## 1. Purpose and non-goals

Build a reproducible, independently reviewable **evidence chain** from a fixed official specification to a catalogue of its claims, then to Lean 4 definitions, propositions, theorems, and their dependencies. The primary question is **not** just whether Factoidal passes W3C entailment tests, but whether every semantically relevant normative provision of the chosen specification has been *considered*, *classified*, *faithfully represented* where appropriate, and *appropriately verified*.

The ambition is to support two separable expert reviews:

1. **Specification extraction review:** Is the source partition complete, and has every normative assertion been identified and interpreted accurately?
2. **Formalization review:** Does each catalogue entry correspond faithfully to Lean declarations, given the meanings and proofs of all dependencies?

A character-coverage certificate is necessary for extraction accountability but **not sufficient** for semantic completeness, fidelity, or correctness. A Lean kernel check is necessary for theorem validity relative to imported axioms and definitions but **not sufficient** to establish fidelity to the W3C text.

Do not conflate RDF 1.1 Semantics with *all* RDF 1.1 specifications. RDF Concepts, Schema, Turtle, N-Triples, datasets, XML Schema and SPARQL have separate normative sources. References and imported obligations must be tracked, not silently assumed to be covered. RDF 1.2 additions (including triple terms) must be distinguished from RDF 1.1.

## 2. Immutable source, offsets, and provenance

**SRC-1.** Acquire and commit or reproducibly pin the *exact bytes* of an official dated version. Record retrieval URL and time, HTTP metadata if available, `SHA-256(raw_bytes)`, content media type, document edition, license/attribution, and fetching procedure. Do not hash only a rewritten DOM, pretty-printed HTML, or copied text. Provide an offline/verifiable vendor option compatible with redistribution terms.

**SRC-2.** Decode bytes using an explicit, pinned encoding (typically UTF-8), recording failures. Define a canonical Unicode scalar-value sequence with **half-open** code-point ranges `[start,end)`. Record an exact reversible map from each scalar value to source byte offset/range; JS UTF-16 offsets are a derived coordinate space, *never* the canonical one. Do not normalize NFC/NFKC, line endings, or entity references in the canonical sequence. Code points rather than grapheme clusters are the counting unit.

**SRC-3.** Parse the pinned HTML with a pinned parser and version; separately record DOM node ancestry, element IDs, visible text projections and mappings of decoded HTML entities and generated text back to original source byte/code-point spans. Preserve source text and markup. For noncontiguous mappings, allow a set of source spans. A raw `<` or `&amp;` character has different source offsets from the character displayed in the browser: neither coordinate space may silently overwrite the other.

**SRC-4.** Hash the raw source, extraction manifest, claim records, mapping records, and review decisions independently. Derive reproducible IDs from content and source spans where useful, but use stable human-readable IDs (`scd-00039`) with explicit version/history so editorial changes do not renumber every claim. Track source revision migrations separately.

## 3. Exhaustive source coverage

**COV-1.** Partition **every source Unicode scalar value** into one or more coverage spans whose union is `[0,N)`; detect gaps, overlaps, invalid offsets, and orphan references. Each character must be accountable, including markup, whitespace, CSS, scripts, navigation, references, examples, and normative prose.

**COV-2.** Character accountability is **not** equivalent to mapping every character to a Lean claim. Maintain orthogonal labels:
- **source role:** markup, whitespace, metadata, prose, equation, table, bibliography, script/style, etc.;
- **normative status:** normative, informative, example, note, diagram, authoring guideline, administrative/conformance, uncertain;
- **disposition:** claim extracted, definitional component of a claim, context/dependency, excluded with reason, needs review, or genuinely unclassifiable.

**COV-3.** Use the spec's own conformance statement as the initial policy: sections explicitly non-normative and authoring guidelines, diagrams, examples and notes are non-normative; other material is normative. Support exceptions, inherited context, and per-span review. A normative sentence may generate zero, one, or multiple claims; a single claim may depend on noncontiguous spans and table headings. Tables, formulas, captions, footnotes and cross-references cannot be ignored.

**COV-4.** Require *normative-text disposition coverage*: every normative text span must either support an identified catalogue claim, form a documented part of a definition/premise, or have a reviewed explanation of why no formal proposition is applicable. Exclusion cannot be a default merely because an LLM did not extract a claim.

**COV-5.** Produce machine-checkable reports: raw-character coverage (must equal 100% with no holes), normative-disposition coverage, unreviewed/ambiguous normative spans, normative claim extraction coverage, mapping coverage, proof/adequacy coverage, and excluded/blocked items. **Never publish a single misleading “100% formalized” number.**

## 4. Specification Claim Directory (SCD)

**SCD-1.** Maintain a versioned, schema-validated claim directory (YAML/JSON/JSONL; choose one as canonical). Claims may represent definitions, semantic conditions, quantifiers, entailment rules, meta-requirements, scope limitations, theorem statements, domain assertions, and dependencies on external specifications. Normative status belongs to a source *span*, not a guess about the importance of a claim.

**SCD-2.** Each claim record MUST contain at least:
- stable ID, label, status/lifecycle, interpretation of source normative status;
- source edition + SHA-256 + exact source span set + anchored heading/DOM location;
- compact verbatim fragment where licensed, reviewer-accessible source view, and a **precise English restatement**;
- claim type, logical strength, quantifiers, side conditions, scope, exceptions, and cross-document references;
- links to prerequisite SCD claims and normative background assumptions;
- formalization status and Lean correspondence records;
- author/reviewer decisions, rationale, timestamp, and versioned review evidence.

**SCD-3.** Represent compound paragraphs and tables as parent source units with multiple independently reviewable atomic claims. Preserve “MUST”, “MAY”, “if”, “only if”, existence, uniqueness, universal quantification and negative claims. Avoid replacing semantic restrictions with rules that merely produce some of the expected entailments.

**SCD-4.** Model claim relationships explicitly: `defines`, `uses`, `refines`, `constrains`, `entails`, `equivalent_to`, `generalizes`, `exception_to`, `requires_external_spec`, `possible_conflict`. Require explicit scope identifiers (e.g., simple interpretations, D-interpretations, RDF/RDFS interpretations, datasets) rather than relying on file names.

**SCD-5.** Keep uncertain extraction, alternative readings, and unresolved contradictory readings as first-class items; do not suppress them to improve coverage scores. Record acceptance criteria for reviewer sign-off.

## 5. Controlled English → symbol-linked intermediate representation

**IR-1.** For each Lean-eligible claim, create a *controlled-English / symbol-linked* representation between unconstrained prose and Lean. Preserve the original English restatement alongside it. The intermediate representation must expose bound variables, types, domains, logical operators, modalities, conditions, and referenced terms explicitly; otherwise it is not an auditable bridge.

**IR-2.** Every formal identifier or bracketed placeholder in the intermediate form resolves to a **specific Lean declaration** (fully qualified name, repository revision, declaration kind, source location) and the SCD entry or external definition that justifies its intended meaning. Merely mentioning `RDFGraph11` without recording its definition is insufficient.

**IR-3.** Permit controlled templates such as:

> An `[RDFGraph11]` is a **set of** `[RDFTriple11]` elements.
>
> Possible elaboration: `RDFGraph11 := Set RDFTriple11` (**illustrative only**, not a verified transcription of a particular clause or of the current Factoidal API).

The IR must distinguish *definitional equality*, *isomorphism*, *embedding*, *predicate characterization* and *propositional equivalence*. It must also record whether “set” is extensional, whether multiplicity/order is absent, and whether the W3C specification imports its graph notion from RDF Concepts rather than defining it locally.

**IR-4.** Require a typechecked or schema-validated representation of references, quantifier structure, and dependency edges. The human-readable pseudo-English may be generated from this typed representation. Detect unbound names, ambiguous aliases, unresolved terminology, missing quantifiers and assumption drift.

**IR-5.** For each claim, expose a reviewer-friendly three-way diff: W3C source excerpt → precise English/controlled-English → Lean declaration/proof. Reviewers should be able to point to a *subphrase* and contest a particular symbol binding, quantifier, side condition, or omitted premise.

## 6. Lean mapping and recursive adequacy

**LEAN-1.** Record a many-to-many correspondence between claims and Lean declarations. Mapping classifications: `exact_definition`, `equivalent_proposition`, `proved_adequacy`, `one_way_soundness`, `one_way_completeness`, `strengthening`, `weakening`, `approximation`, `axiomatized`, `test_only`, `unimplemented`, `not_lean_applicable`.

**LEAN-2.** A mapping record identifies module, fully qualified declaration, commit SHA, precise code span, types, *all relied-on declarations and assumptions*, and a proof/checking strategy. Generate a transitive dependency closure using Lean elaboration/environment data where feasible, not regex-only import scanning. Differentiate logical dependencies from syntactic imports and implementation dependencies.

**LEAN-3.** Every Lean symbol used to interpret a spec claim must itself have a reviewed specification meaning or an explicitly identified trusted primitive. A verified theorem involving an incorrectly modeled `RDFTriple11` or `RDFGraph11` is **not** accepted as coverage of the original sentence. A chain is accepted only when all required dependency meanings are justified; display unresolved dependency leaves.

**LEAN-4.** A difference between W3C models and Factoidal models must be expressed by exact comparison theorems or documented partial simulations/embeddings with stated direction, conditions, and counterexamples. In particular, audit `formal/lean4/L4Factoidal/RDF/Semantics.lean`, whose own commentary describes totalized interpretations and other deliberate enlargements. Do not equate successful one-way soundness with full semantic equivalence.

**LEAN-5.** Record trusted computing base and proof quality: Lean version, project lockfile, build reproducibility, imported axioms, `sorry`/`admit`, `unsafe`, `opaque`, `partial`, foreign/native evaluators, axiomatized schemas, reflection, SMT/external prover certificates, and whether checked theorems depend on them. Not all such mechanisms are invalid; their presence must be accurately disclosed. Separate model-theoretic theorems from executable algorithm guarantees and empirical differential test results.

**LEAN-6.** Represent proof obligations separately from statement declarations. A definition may be correctly translated without needing a theorem; claims about algorithms need refinement/correctness results. For each spec claim provide an explicit fulfillment criterion, including “not formalizable as a Lean proposition; reviewed policy/metadata requirement” where applicable.

**LEAN-7.** Generate a dependency/assumption graph with a completeness checker for each SCD item. Accept a claim as `faithful_verified` only if (a) extraction reviewed, (b) controlled-English binding reviewed, (c) Lean proposition/definition or adequacy relationship reviewed, (d) necessary proof checks pass, and (e) required dependency semantics are reviewed, recursively. Track cycles/SCCs as a unit rather than pretending recursion terminates automatically.

## 7. Expert review interface

**UI-1.** Publish an accessible, read-only **source-first** presentation of the entire pinned W3C HTML; clickable text, equations, tables and source spans. A click (or keyboard range selection) shows source coordinates, status/disposition, associated SCD entries, controlled English, linked Lean source, proof status and dependency closure. Show unclaimed or uncertain regions prominently rather than fabricating a claim on click.

**UI-2.** Support *raw-source* and *rendered-document* views, with an explicit mapping between them. HTML markup is clickable/inspectable in source mode, even where there is no visible rendered text. Do not claim pixel-perfect equivalence across browser engines: canonical references are byte/code-point offsets and pinned source anchors.

**UI-3.** Expert reviewers can propose corrections to span segmentation, status, claim granularity, meaning, symbol binding, formal statement, or dependencies. Reviews are persistent, attributable, revision-specific, and independently inspectable (PR-backed suggestions or append-only review events). Include disagreement, resolution, reviewer qualifications (optional), and a controlled sign-off checklist for extraction and formalization **separately**.

**UI-4.** Provide bidirectional navigation: source → claims → intermediate representation → Lean → downstream claims, and Lean declaration → all dependent/justified SCD entries. Support filtering for `unreviewed`, `normative_unmapped`, `axiomatized`, `approximate`, `blocked`, `external_dependency`, and `verified`.

**UI-5.** Build without executing original specification scripts in a privileged context. Sanitize/proxy historical HTML as necessary while retaining byte-faithful raw-source access. Display status without allowing browser overlays or Unicode transformations to change source identities.

## 8. Example record (ILLUSTRATIVE; not a claimed W3C quotation)

```yaml
id: scd-00039
source:
  edition: rdf11-mt-20140225
  sha256: '<actual source digest>'
  spans: [{start_cp: 12345, end_cp: 12410}] # invented offsets; replace
normativity: external-import-or-context-to-be-determined
kind: definition
english: 'An RDF graph is a set of RDF triples.'
controlled:
  template: 'An [RDFGraph11] is a set of [RDFTriple11] elements.'
  bindings:
    RDFGraph11: 'L4Factoidal.RDF.Graph' # candidate only: verify RDF 1.1 fidelity
    RDFTriple11: 'L4Factoidal.RDF.Triple' # candidate only
  obligations:
    - 'Check extensional-set semantics versus concrete Lean representation'
    - 'Trace graph/triple definitions to RDF 1.1 Concepts'
depends_on_claims: []
lean_mappings: []
status: needs_extraction_and_symbol_review
```

IDs, offsets, names and digest in this example are placeholders. Do **not** turn this example into a certified mapping. Actual RDF graph/triple definitions and source provenance must be established from the appropriate normative document.

## 9. Validation, CI, and release artefacts

**CI-1.** Deterministically regenerate and compare source byte hash, canonical text/offset index, DOM projection index, SCD schema, span coverage, cross-references, and dependency graph. CI fails for unclassified/gap characters (source coverage), broken offsets, unbound IR symbols, dangling Lean references, stale declaration locations or unsupported `faithful_verified` statuses.

**CI-2.** **Report**, rather than necessarily fail the whole build on, incomplete semantic coverage during incremental development. Distinguish `pipeline_valid` from `coverage_complete`; never turn review in progress into a false passing badge. Strict release profile gates require zero unreviewed normative spans, zero unmapped applicable claims, and all declared adequacy/proof obligations satisfied or explicitly documented as exclusions with reviewer approval.

**CI-3.** Produce a machine-readable audit manifest plus static HTML report and a reviewable human-readable summary. Include source fingerprint; claim catalogue digest/version; approved-review counts; semantic-coverage matrix; proof dependency and admitted-assumption inventories; unresolved items; reproducible toolchain provenance.

**CI-4.** Mutation tests must demonstrate failures when: one source character is omitted, HTML entity mappings drift, a normative sentence is wrongly excluded, a Lean binding points at another declaration, a premise is dropped, an axiom is silently introduced, or a transitive dependency loses its justified meaning.

## 10. Implementation plan and acceptance gates

**Phase 0 — reconnaissance.** Inspect Factoidal's existing RDF/RDFS/Unified semantics, theorem registry, source comments and tests; inventory what can be reused. Pin source and specification of interpretation. Output a gap analysis, not a premature completeness claim.

**Phase 1 — source ledger.** Implement raw-byte provenance, code-point/byte correspondence, pinned DOM projection, exhaustive character-role/status ledger, and a minimal clickable source viewer. **Gate:** synthetic mutation tests plus 100% character accounting.

**Phase 2 — claim catalogue.** Manually seed normative section/table inventory; add assisted extraction with mandatory review, SCD schema, fine-grained source/claim links and report of undecided normative spans. **Gate:** reviewer can audit a section end-to-end and identify intentionally excluded text.

**Phase 3 — intermediate language and symbols.** Add controlled-English typed bindings and Lean environment symbol resolution; review the specific RDFGraph/RDFTriple and simple-interpretation examples end-to-end. **Gate:** all references resolve, and known deliberately enlarged interpretation semantics show explicit adequacy obligations, not false equivalences.

**Phase 4 — proof graph and CI.** Extract dependency closure, axioms and proof checks; implement claim-level status propagation; publish gap/review reports. **Gate:** regression examples fail appropriately under deliberately broken dependencies.

**Phase 5 — comprehensive external audit.** Review each normative region and its claims, prioritize semantic foundations before derived inference rules, obtain independent reviews of extraction and formal translation, and freeze a signed/versioned evidence release. **Gate:** completeness claim is scoped explicitly to the pinned *RDF 1.1 Semantics* edition, with all imported-spec exclusions or extensions named.

## 11. Definition of done / permissible claims

The strongest honest deliverable is **a reproducibly checkable, expert-reviewed traceability argument** that every normative portion of the pinned specification was dispositioned and every Lean-applicable semantic claim was represented faithfully with a justified dependency closure and suitable proofs. It is **not** automatically a formal proof that natural-language parsing was complete or that model theory itself captures all intended human meanings.

Acceptable badges/claims must be specific:
- `source_bytes_verified`: exact official source fingerprint reproduced.
- `source_partition_complete`: every Unicode code point accounted for.
- `normative_disposition_reviewed`: no unreviewed normative text.
- `formalization_mapped`: all applicable claims have reviewed typed mappings (does not imply proof).
- `lean_obligations_checked`: specified obligations checked against disclosed trust assumptions.
- `end_to_end_audited`: independent reviewers approved extraction **and** mapping **and** dependency meanings for the edition.

### Open design decisions for reviewers

1. What licensing/provenance arrangement is preferred for vendoring the W3C source?
2. What is the canonical schema format, and what extraction toolchain is trustworthy enough to pin?
3. Are source spans raw-HTML code points, DOM-text code points, or both? **Requirement:** raw is authoritative, projected ranges linked.
4. Where do imported RDF Concepts definitions live in the claim registry?
5. How much controlled English must be structural versus text with inline typed links?
6. What constitutes independent reviewer approval and how are disagreements handled?
7. What status should be assigned to semantic invariants whose full adequacy is currently unknown?

## 12. Relevant anchors

- W3C RDF 1.1 Semantics, dated Recommendation: https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/
- Factoidal Lean RDF semantics: `formal/lean4/L4Factoidal/RDF/Semantics.lean`
- Factoidal unified model theory design (read correction notes): `docs/designissues/2026-08-25-unified-semantics-lean.md`
- Factoidal proof registry (inspect actual current version): `docs/theorem-registry.md`
