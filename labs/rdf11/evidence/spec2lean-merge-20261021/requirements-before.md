# Spec2Lean: RDF 1.1 source coverage and formalization traceability

**Status:** requirements draft for expert review and implementation.  
**Date:** 2026-10-21.  
**Workspace:** all implementation and generated artifacts for this experiment belong under `_LEAN/`.

## 1. Objective

Build an auditable connection from an immutable copy of RDF 1.1 Semantics to a catalogue of its assertions, their English formulation, their Lean 4 representation, and the Factoidal operations to which the resulting proofs apply.

Every Unicode character in each included source document must be accounted for by explicit character ranges. An expert must be able to click anywhere in a faithful presentation of the document and inspect the catalogue records associated with that location, including extracted claims, their dependencies, formalization status, and Lean declarations. The connection must work in both directions: from a Lean claim back to all the source passages it represents.

The assertion catalogue is provisionally called the **Spec Claim Directory (SCD)**. The aim is to make omissions visible and eventually establish complete, reviewed formalization coverage of the declared corpus. A source theorem that is disconnected from the operations shipped to users does not establish Factoidal's implementation coverage.

This project must maintain distinct evidence for:

1. **Source accountability:** every character has a valid catalogue disposition. This is a finite, mechanically checkable property for which the project must provide a Lean proof.
2. **Extraction fidelity:** the English claims capture the source's assertions, qualifications, scope and dependencies. This requires expert review; a range-coverage proof alone cannot establish it.
3. **Formalization fidelity and proof:** the Lean declarations express the reviewed claims, with their assumptions exposed, and the required propositions have kernel-checked proofs.
4. **Implementation refinement:** Factoidal's executable operations implement those formal contracts at the boundaries actually used by the product.

The system must never turn the first achievement, or a passing test suite, into an assertion that all four have been established.

## 2. Initial corpus and scope

**SCOPE-01.** The primary specification is the complete [RDF 1.1 Semantics Recommendation of 25 February 2014](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/). Include its normative sections, informative sections, appendices, tables, mathematics, notes, examples, references, and document infrastructure in source accounting. Informative material remains identifiable and reviewable.

**SCOPE-02.** [RDF 1.1 Concepts and Abstract Syntax](https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/) supplies incorporated definitions. Include its complete snapshot in character accounting; identify the sections imported into the Semantics formalization and record why each is needed. Other normative dependencies, including datatype specifications, require explicit import records with exact document versions and imported obligations. An unresolved dependency remains an open obligation.

**SCOPE-03.** Here, “RDF 1.1 specification coverage” initially means the Semantics document and its declared dependency closure. It does not silently include every RDF syntax Recommendation, SPARQL, or OWL. The corpus manifest must state this boundary. A later claim of coverage of the entire RDF 1.1 document family requires extending that manifest and satisfying the same requirements for the added documents. Companion passages outside the initial formalization scope remain visible as such and cannot count as formalized.

**SCOPE-04.** RDF 1.2 is a separate corpus/version track. Do not use 1.2 behavior, tests or declarations to discharge a 1.1 obligation without an explicit applicability argument. Existing Factoidal types that admit 1.2 constructs may need a stated RDF 1.1 restriction in their theorems.

**SCOPE-05.** Use [w3c/rdf-tests](https://github.com/w3c/rdf-tests), especially `rdf/rdf11/rdf-mt`, as essential executable evidence. Preserve the repository revision, test identifiers and approval metadata. The tests are not the definition of the obligation inventory, and their coverage must not be presumed exhaustive.

## 3. Immutable source and coordinate model

**SRC-01 — Preserve bytes.** Store the exact downloaded document bytes and a manifest containing their SHA-256 digest, byte length, retrieval URL, final URL if redirected, retrieval time, declared publication version, media type, encoding, and retained license information. Hash the stored response body before decoding or parsing. Hash rendered HTML, extracted text, and annotations separately; none may replace the original source identity. Permit additional hash algorithms through an algorithm-tagged digest field.

**SRC-02 — Decode explicitly.** For the initial UTF-8 corpus, use strict UTF-8 decoding. Preserve line endings, a leading BOM as U+FEFF if present, and all whitespace. Do not apply Unicode normalization, newline normalization, case folding, HTML entity expansion, or error replacement to the authoritative character sequence. Reject invalid decoding rather than substitute U+FFFD. Record the decoder policy and version. Other encodings require an explicit, reviewed decoding profile.

**SRC-03 — Define “character.”** The authoritative sequence is Unicode scalar values, not bytes, UTF-16 code units, glyphs or grapheme clusters. Positions are zero-based. A range is half-open `[start, end)` with `0 ≤ start < end ≤ N`, where `N` is the scalar count. An astral character occupies one position; a base letter followed by a combining mark occupies two. A CRLF occupies two. Every range includes its source document's digest.

**SRC-04 — Maintain translations.** Store or reproducibly derive mappings among original byte spans, scalar spans, parser/token locations, and browser UTF-16 offsets. Lean's character representation and the browser's string representation must be connected explicitly. A range must be resolvable against the archived source without relying on line numbers, section titles, CSS selectors or DOM paths. Those are useful secondary locators only.

**SRC-05 — Parse HTML faithfully.** These sources are HTML; do not assume that an XML parser will accept or preserve them. Use a specified HTML parsing profile with source locations. Preserve a concrete source/token representation alongside the DOM, because DOM serialization can change quotes, entities, attribute order, whitespace, omitted tags and repaired markup. Parsing must not redefine the authoritative scalar sequence.

**SRC-06 — Map transformed text.** Entity expansion and rendering require a relation between source intervals and displayed intervals, not a constant offset adjustment. For example, all five source characters of `&amp;` contribute to the displayed ampersand. Collapsed whitespace may map many source characters to one display position; some source characters have no visible glyph. Record these cases. Generated section numbers, toolbars or other viewer content must be marked as generated, not attributed to source characters.

**SRC-07 — Preserve revisions.** A changed byte hash creates a new document identity. Annotation migration may propose new ranges but must not silently rebind accepted records to new text. Store the old ranges, proposed ranges, diff and review decision. Recompute proofs and invalidate affected review/build results when their inputs change.

### Initial local snapshots

These values identify the copies already retained for this experiment; they are not a claim that a future download will have identical bytes.

| Document | Local file | Bytes | Unicode scalars | SHA-256 |
|---|---|---:|---:|---|
| RDF 1.1 Semantics | `specifications/rdf11-mt-20140225.html` | 139985 | 139975 | `a4bc1dc53bc66fb7d57cd4b646e2527e35dbcce74fc54d8dd59beb255a830f80` |
| RDF 1.1 Concepts | `specifications/rdf11-concepts-20140225.html` | 120924 | 120796 | `3838c992097f72ee8784b6c96194d9879f86f2e08f53ced5a05aa4031750c5ac` |

## 4. Catalogue and extraction

**CAT-01 — Assertion taxonomy.** Use the following primary categories, with additional tags where a passage serves several purposes:

| Category | Examples |
|---|---|
| Definitions | Interpretation, denotation, satisfaction, graphs, instances, simple/RDF/RDFS entailment |
| Semantic constraints | Conditions on properties, classes, datatypes, extensions, domains and ranges |
| General requirements | Monotonic semantic extensions, preservation of simple truth conditions, conformance and applicability requirements |
| Mathematical consequences | Entailment properties, satisfiability results, interpolation results, relationships between regimes |

**CAT-02 — Extract by close reading.** AI may propose assertions through contextual reading. Keyword searches, rule-code extraction, DOM segmentation and automated highlighting may assist navigation, but cannot stand in for semantic extraction. Experts must review the proposed inventory. Named entailment rules are aliases on relevant records, not an exhaustive catalogue. Identify numbered conditions, table cells, mathematical formulae and consequential prose even when they have no official code.

**CAT-03 — Claim content.** Each claim must have a stable project identifier; an English statement; category; normative/informative status and the source of that status; applicable RDF version/regime; explicit quantifiers, premises and exceptions; one or more source ranges; dependency links; an extraction rationale; review state; and formalization state. Separate logical content from commentary explaining it. Retain official codes and section anchors without confusing them with project identifiers.

**CAT-04 — Many-to-many provenance.** One passage may yield several claims; one claim may depend on several noncontiguous passages or documents. Support overlapping ranges and distinct range roles such as `statement`, `qualification`, `definition`, `context`, `normativity`, `example`, and `dependency`. A sentence boundary is not necessarily an assertion boundary. The viewer must expose all applicable records rather than pick an arbitrary one.

**CAT-05 — Explicit non-assertional records.** Every source character still needs a disposition when it does not state a formalizable assertion. Record justified categories such as document syntax, formatting, navigation, bibliographic metadata, explanatory text, example, or intentionally out-of-scope companion material. Attach these records to their document construct and associated claims where appropriate. Do not invent a Lean theorem for markup or whitespace. An example may also support a separate substantive claim; labelling a whole example block “informative” must not conceal that possibility.

**CAT-06 — No catch-all completion.** A document-wide “covered” annotation does not satisfy extraction review. Partition at meaningful source constructs and use sufficiently precise assertion ranges to identify the actual evidence. Broad context ranges are permitted but cannot independently discharge assertion accountability. Large exclusions and any exclusion containing substantive prose or mathematics must be explicitly reviewable. No normative Semantics passage may be excluded merely because it is hard to formalize.

**CAT-07 — Preserve difficulties.** Ambiguities, apparent editorial errors, conflicting interpretations, missing dependencies and unformalized assertions are first-class records. Store alternative readings and their consequences. Link official errata when applicable; do not silently repair the archived text or treat an AI inference as an approved erratum. These records prevent a full-fidelity completion claim until resolved or explicitly bounded by a narrower claim.

**CAT-08 — Two review tracks.** Support separately solicitable expert reviews of (a) source → SCD completeness and accuracy, and (b) SCD → Lean completeness and accuracy. Each has its own decisions, unresolved comments, accepted revision and evidence. Acceptance of extraction must not imply acceptance of formalization, or vice versa. Reviewers may contribute to either track without being required to adjudicate the other. A third implementation-refinement review remains distinct from both.

## 5. Character coverage certificate

**COV-01 — Complete partition.** Generate a sequence of source atoms covering `[0, N)`. Each atom has a disposition and catalogue references. Atoms are nonempty, ordered, adjacent and nonoverlapping; the first starts at zero and the last ends at `N`. For an empty source, the empty partition is the sole valid case. Claim annotations may overlap independently of this partition. Splitting at annotation boundaries must preserve the original provenance.

**COV-02 — Closed references.** Every reference resolves to a versioned catalogue record; every range lies within its identified source; every assertion atom links to at least one extracted claim; every non-assertional atom links to an explicit disposition record. Drafts may contain `unresolved` atoms, but an accepted complete-accountability certificate must not. Imported obligations and scope exclusions must appear in the certificate, not disappear from its denominator.

**COV-03 — Lean verification.** Implement a small Lean model of sources, intervals, partitions and reference validity. Prove the checker sound: accepting a certificate implies that every source position belongs to exactly one accountability atom and that all its required references are valid. Instantiate that result for the actual archived documents and catalogue, rather than proving only an abstract partition lemma. Also prove or check the consistency of all byte/scalar conversion tables used to identify those positions.

The central theorem should have the following meaning, without prescribing these particular Lean names:

```text
For each document d in the declared corpus,
  for every i with 0 ≤ i < scalarLength(d),
    there exists exactly one accountability atom containing i,
    and that atom has a valid, nonempty disposition in the catalogue.
```

The digest binding, decoding and catalogue data used by the concrete theorem must be reproducible. Prefer a pure verified decoding/checking path. If the first implementation trusts a byte loader, decoder, hash implementation or data generator, enumerate those components in the certificate's trust manifest and qualify the result accordingly. A digest identifies bytes; it does not prove extraction fidelity or guarantee that the downloaded content is the publisher's intended edition.

**COV-04 — Prevent vacuity.** The verifier must reject missing or empty substitutes for nonempty declared documents, changed source hashes, omitted corpus documents, gaps, out-of-bounds endpoints, unresolved references, and unresolved atoms in accepted certificates. A valid partition containing only non-assertional records may establish a structural fact but cannot establish semantic extraction coverage. The semantic completion gate additionally requires accepted expert classification of all substantive regions and all extracted claims.

**COV-05 — Report separate completion measures.** Show source-accountability status, extraction-review status, formalization/proof status, and implementation-refinement status separately. Include unresolved claims, unproved claims, assumptions, exclusions and unsupported operations. Character percentages are navigation aids; markup volume must not inflate semantic coverage. Do not publish a single “percent RDF compliant” score.

## 6. Lean and executable mappings

**LEAN-01 — Resolve real declarations.** A mapping records repository and commit, source file, fully qualified declaration, elaborated type/signature, Lean toolchain, dependency/build identity, and evidence location. Verify declaration existence using Lean's environment. A matching name or comment is insufficient. Display all hypotheses and type restrictions to the reviewer.

**LEAN-02 — Distinguish roles.** Label each link as definition, representation, semantic condition, theorem, executable implementation, refinement theorem, or finite regression. A definition may formalize a definition without itself being a proof of an algorithm. `#guard`, a compiled function, and a successful example are not substitutes for a universally quantified theorem.

**LEAN-03 — Review translation.** Store an expert decision on whether each formal declaration faithfully represents its English claim, including domain restrictions and dependencies. Display the English statement and formal signature together. Review must catch weakened hypotheses, changed quantifier order, missing reverse implications, inappropriate equality, and claims proved only for a finite or restricted fragment.

**LEAN-04 — Make proof status reproducible.** Record proof/build results and the transitive axiom dependencies of mapped declarations. Reject placeholder proofs and unapproved user axioms in accepted completion evidence. Declare the permitted logical foundations and external trust boundaries explicitly. Changed declaration types, dependencies, source claims or toolchains must invalidate affected evidence until rechecked.

**LEAN-05 — Trace product use.** Map semantic objects to their raw representations, abstraction functions, admission boundaries, mutators, indexes, observations and exported operations. Require refinement statements where an implementation is claimed to realize a specification operation. Trace the relevant path through Lean compilation, WASM, host wrappers and the packaged artifact. A proof about an unused function cannot discharge a different function's obligation. Mark uncovered compiler/FFI/host steps explicitly rather than implying universal verification.

**LEAN-06 — Preserve honest outcomes.** Where an algorithm implements entailment or satisfiability, distinguish a proved positive answer, a proved negative answer, and failure to establish an answer. A search failing to find a contradiction is not automatically a proof of satisfiability. Record soundness and completeness separately, with the supported regimes and datatype assumptions.

### 6.1 Symbol-linked English and dependency completeness

**BIND-01 — Intermediate claim form.** Each formalizable SCD entry must retain its ordinary English statement and provide a separate **symbol-linked English** rendering. In this intermediate form, the relevant natural-language phrases are linked to explicit logical or Lean symbols. It must help experts inspect the translation without requiring them to infer the meaning of implementation names. It must not silently rewrite the English claim to match whichever theorem is already available.

The review path is:

```text
Exact source ranges
  → SCD English claim
  → symbol-linked English claim + binding table
  → Lean definitions / conditions / propositions
  → kernel-checked proofs and executable refinements
```

**BIND-02 — Stable, typed bindings.** Every symbol occurrence must carry a stable concept identifier, its semantic role, the phrase it replaces, its scope, and its versioned Lean binding. Roles include type, value, variable, predicate, function, relation, equality, quantifier and connective. The binding table resolves to fully qualified declarations and their elaborated types in a specific Lean environment. Display notation is not the symbol's identity. Variables need explicit binders and scopes; ambiguous, unresolved or accidentally captured variables fail validation.

**BIND-03 — Record what remains English.** Mere noun replacement does not establish a complete translation. Account for assertion-bearing phrases such as “is a”, “every”, “if and only if”, “the same”, “there exists”, and restrictions on a mapping or interpretation. A phrase may map to a logical construction rather than a named declaration. Record remaining semantic content as explicitly reviewed prose or as a translation gap. The intermediate form may remain readable English, but the system must not present a partially bound sentence as a fully specified proposition.

**BIND-04 — Semantic dependencies.** Each SCD entry must list the concepts and other claims needed to understand or formalize it. Each dependency resolves to another reviewed SCD entry, a foundational mathematical definition, a declared external obligation, or an unresolved gap. Record a rationale and the relevant part of the dependent claim. Reusing a symbol does not establish that its definition has been reviewed. Support expansion of the full dependency closure, with the review state and applicable RDF version visible at every level.

**BIND-05 — Lean dependencies.** Extract actual declaration references from elaborated Lean types and bodies, including hypotheses and transitive dependencies. Compare that dependency graph with the declared bindings and expose unexplained application-level dependencies, missing declarations, extra assumptions and stale links. Record proof axioms separately. Where executable evidence uses compiler substitutions or foreign implementations, include those in the implementation dependency record; a proposition's type alone does not reveal that execution path.

**BIND-06 — Explicit closure boundary.** Do not require every Lean library declaration to correspond to an RDF sentence. Identify standard mathematical and logical foundations, infrastructure, imported specification concepts and Factoidal-specific definitions separately. A closure certificate must say where traversal stops and why, with exact versions and accepted trust/review records. Mutually dependent definitions may be reviewed as an explicit cluster; circular references between unreviewed entries cannot establish completeness by themselves.

**BIND-07 — Two notions of completeness.** Mechanically check that every symbol binding resolves and that every referenced Lean dependency is accounted for within the declared closure boundary. Separately solicit an expert judgment that the chosen symbols, logical constructions and dependencies capture everything needed by the English claim. The mechanical check cannot decide whether the reviewer omitted an essential natural-language qualification or chose an inappropriate definition.

**BIND-08 — Dependency-sensitive acceptance.** A mapping can be locally reviewed while a required dependency remains unreviewed. Display that distinction. Full acceptance of an entry's formalization requires both its local fidelity decision and resolution of all required dependency obligations. Changes to a bound definition, assumption, intermediate statement or dependency boundary must invalidate affected dependent acceptance records until rechecked.

#### Illustrative SCD entry

The identifiers and Lean names below illustrate the interface; they are not assertions that these declarations already exist.

| Layer | Illustration |
|---|---|
| SCD identifier | `scd-39` |
| English claim | An RDF graph is a set of RDF triples. |
| Symbol-linked English | An `⟦rdf11.graph⟧` is a `⟦math.set⟧` of `⟦rdf11.triple⟧`. |
| Concept dependencies | The RDF 1.1 triple definition, the component term categories and their identity, mathematical set membership and extensional equality |
| Candidate Lean bindings | `rdf11.graph ↦ Graph11`; `rdf11.triple ↦ Triple11`; `math.set ↦ Set`, all resolved in the selected environment |
| Required interpretation of the sentence | Specify whether `Graph11` is defined as a set, is an equivalent abstract type, or is a representation with an explicit abstraction/refinement. Record the chosen interpretation of “is a” and “of”. |
| Additional implementation obligations | Unique enumeration and correct cardinality under the specified triple identity; preservation by constructors and mutations |

A reviewer must be able to expand `Triple11` to see whether its subject, predicate and object restrictions actually describe RDF 1.1 triples. Similarly, binding `Graph11` to `List Triple11` leaves a representation question open: the mapping needs its set abstraction and the appropriate observable-behavior proofs. The name `Graph11` itself establishes neither.

One SCD claim may require several Lean declarations and theorems, and one declaration may serve several SCD claims. The system must support these relationships without forcing an artificial one-claim/one-theorem correspondence. Derived implementation obligations must be labelled as such, with their derivation from source claims visible.

### Required worked example: graph sethood

The first vertical slice must connect [Semantics §4](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#notation), its incorporated [Concepts §3](https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/#section-rdf-graph) definition, and the member-based truth conditions to the implementation obligation that graph enumeration emits each RDF triple once.

The presentation must explain why a list can represent a set through an abstraction such as `α(xs) = {t | t ∈ xs}`, and why proving that `[t, t]` and `[t]` have the same truth conditions does not prove that raw list length implements graph cardinality. The implementation link must supply a uniqueness invariant or an appropriate refinement of each observable operation. It must use RDF term identity rather than conflate lexical identity with datatype-value equality.

Show source ranges, extracted English claims, the relevant Lean predicates and proofs, and public-boundary regressions for parsing, enumeration, counts and mutation. Keep per-graph set semantics distinct from SPARQL solution multiplicities. An identical triple in two different graphs remains two different quads. Explicitly display the remaining gap if only some storage or API paths are certified.

## 7. Expert review interface

**UI-01 — Click anywhere.** Clicking or keyboard-selecting any specification text must open the records associated with the exact displayed location and its source ranges. This includes headings, punctuation, mathematics, table headers/cells, notes, examples, links and collapsed whitespace. If several claims apply, show all of them. If there is no claim, show the explicit disposition or unresolved status. A click must never silently do nothing because extraction missed that passage.

**UI-02 — Source fallback.** Provide synchronized rendered and raw-source views. Every raw scalar position, including tags, attributes, comments, scripts and invisible text, must be selectable in the source view. For graphical mathematics or images, clicking the object must open its source-element record and linked claims; archived assets and textual/formal interpretations need their own provenance. Do not claim that invisible source syntax has a clickable glyph in the rendered view.

**UI-03 — Preserve context.** Show the source passage with nearby context, exact source digest/ranges, English claim, normative status, assumptions, dependencies, review history, Lean declaration/type, proof status and implementation links. Allow navigation from any claim or Lean declaration back to every supporting range. Distinguish a direct statement range from a contextual reference.

**UI-04 — Review operations.** Experts can propose, split, merge, correct, accept or reject claims and dispositions; adjust ranges; link dependencies; resolve ambiguities; and review Lean fidelity. Record reviewer identity, timestamp, rationale and before/after versions. AI proposals begin unreviewed. Do not overwrite accepted decisions or imply that a displayed reviewer name provides cryptographic authentication.

**UI-05 — Useful views.** Provide filters for unaccounted source, unreviewed extraction, normative obligations, missing dependencies, unformalized claims, failed proofs, unproved implementation mappings, and test-only evidence. A heatmap may help navigation but must not replace textual status or collapse the four completion measures.

**UI-06 — Faithful, inert rendering.** Render archived HTML without executing its scripts or fetching unpinned resources. Use an explicit rendering profile and retain the source map through any sanitization. Reflow, CSS and accessibility adaptations must not alter provenance. Provide keyboard navigation and text equivalents; review must not depend on color or pointer use alone.

**UI-07 — Review packets and dependency exploration.** Export review packets for either source → SCD or SCD → Lean, containing pinned inputs, precise questions, current decisions and unresolved objections. The formalization packet must include ordinary English, symbol-linked English, the binding table, exact Lean types and an expandable dependency graph. A reviewer must be able to open each dependency's own source and acceptance history. Support comments on individual bindings as well as whole claims. Generating a packet is not authorization to publish it or contact reviewers.

## 8. Test evidence and reproducibility

**TEST-01.** Catalogue test cases by stable test IRI, repository commit, manifest path and hash, active manifest membership, approval status, inputs/results, entailment regime, and recognized/unrecognized datatypes. Preserve retired or inactive descriptions separately from active entries. An expectation of `false` in an entailment manifest needs its semantic interpretation recorded; it is not merely a missing output graph.

**TEST-02.** Link a test to the particular claims it exercises with an explanation. Permit many tests per claim and many claims per test. Mark inferred associations as provisional. Do not infer semantic coverage from test filenames or from presence in the same suite.

**TEST-03.** Store per-test outcomes and the actual execution surface: pure Lean, native harness, WASM operation, or npm API, plus code/artifact hashes and invocation. Preserve failures, skips, unsupported cases and unrun cases. Test success cannot discharge a universal proof obligation; proof success cannot establish that a different product entry point ran correctly.

**TEST-04.** Add project-owned regressions for specification obligations absent from the external corpus. Clearly separate them from W3C tests. The sethood worked example must include repeated triples, lexical/value distinctions, named-graph scope and legitimate query multiplicities. Do not assert that any W3C repository promises complete specification coverage.

## 9. Data model and deliverables

Use a portable, schema-validated source format with stable IDs and deterministic serialization, initially JSON or JSON Lines. SQLite may provide indexes and queries but must be rebuildable from that source. Required entities are:

| Entity | Essential contents |
|---|---|
| Corpus/document/asset | Scope, exact bytes, digests, decoding profile, version, license, dependency role |
| Range/atom/source map | Document identity, scalar endpoints, byte/display relationships, disposition references |
| Claim/disposition | English statement or classification, category, normativity, assumptions, source roles, review state |
| Symbol-linked claim/binding | Versioned intermediate statement, bound phrase occurrences, concept IDs, semantic roles, variable scopes, exact Lean resolutions, residual translation gaps |
| Dependency | Claim/document links, imported meaning, applicability, unresolved status |
| Lean mapping | Declaration identity/type, role, hypotheses, build/proof evidence, fidelity review |
| Implementation mapping | Representation and operation, abstraction/refinement, product path, remaining trust boundaries |
| Test/run | Manifest identity, expectation, surface, artifact versions, per-case outcome, claim links |
| Review/certificate | Immutable decision history, accepted versions, checker result, concrete proof, trust manifest |

Deliver an offline-capable review viewer, a deterministic validator/certificate generator, the Lean checker and concrete source-coverage proof, the assertion catalogue, declaration/build extractors, pinned test metadata/results, and instructions to reproduce the evidence. Keep draft and accepted certificates separate. A reviewer must be able to inspect exported data without running the viewer.

Existing `_LEAN/ledger/` files are preliminary inputs. Their section links and file checks do not constitute the character-range catalogue, expert approval, declaration verification or concrete coverage proof required here. They must be migrated and reviewed, not grandfathered into accepted coverage.

## 10. Acceptance criteria and implementation sequence

| Gate | Required demonstration |
|---|---|
| A — Immutable sources | Hash/length/decoding reproduction for both pinned documents; any byte change invalidates the old binding |
| B — Coordinate correctness | Cases covering ASCII, astral Unicode, combining marks, CRLF, BOM, entities, collapsed whitespace, repaired HTML and invisible content round-trip through the declared mappings |
| C — Total accountability | Concrete Lean certificate accounts for every scalar; deliberate gaps, invalid references, bounds errors, missing documents and unresolved atoms fail the appropriate gate |
| D — Honest extraction | Every substantive region has accepted extraction/disposition review; split and overlapping claims work; blanket markup or informative labels cannot conceal unreviewed assertions |
| E — First formal slice | Graph sethood is traceable from exact ranges through reviewed English and Lean to the relevant executable boundaries, with limitations visible |
| F — Usable review | Clicks/selections in rendered and raw views resolve correctly; reverse navigation and review history work; unaccounted regions remain visible |
| G — Reproducible evidence | Exact Lean declarations and their assumptions resolve; stale proofs are rejected; test outcomes remain separate from proof status and product-surface claims |
| G2 — Mapping and dependency review | Both review tracks can be exported and adjudicated separately; unresolved bindings, missing dependencies and changed definitions invalidate the appropriate completion claims; locally accepted mappings with pending dependencies are visible |
| H — Full declared-scope completion | All in-scope assertions and imports have accepted fidelity review, required formalizations/proofs, and the implementation evidence necessary for the stated Factoidal coverage claim; no unresolved normative obligations are hidden |

Implement in this order:

1. Freeze sources and schemas; implement decoding, coordinates, source maps and partition validation.
2. Build the rendered/raw viewer and review operations. Demonstrate character accountability with unresolved semantic regions visible.
3. Complete the graph-sethood vertical slice, including the concrete Lean coverage certificate and executable links.
4. Expand the AI-proposed, expert-reviewed inventory through all four assertion categories, section by section, including imported definitions and informative material.
5. Map and audit existing Lean definitions/proofs, fill formalization gaps, connect executable operations, and integrate pinned test evidence.
6. Seek acceptance of the full declared-scope claim only when Gate H is satisfied. Publish intermediate artifacts with their exact achieved gates and outstanding obligations.

Completion of this requirements document authorizes neither a claim of completed formalization nor a conformance certificate. Its purpose is to specify the evidence that those future claims must provide.
