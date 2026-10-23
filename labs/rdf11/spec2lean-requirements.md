# Spec2Lean: RDF 1.1 source coverage and formalization traceability

**Status:** requirements draft for expert review and implementation.

**Date:** 2026-10-21; version/family requirements added 2026-10-23.

**Workspace:** the original `_LEAN/` experiment is now maintained in `labs/rdf11/` in `danbri/dickory`; the current Lean project is `labs/rdf11/cleanroom/`.

This draft incorporates the separately supplied `spec2lean-draft.md`; [merge review and provenance](docs/20261021-spec2lean-merge.md) record the additions and resolved differences. Existing requirement IDs are retained.

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

### 2.1 Editions, errata, proposals and related specification families

The [version and family design note](cleanroom/docs/20261023-spec-versions-and-families.md) gives concrete RDF, OWL and SPARQL examples. These are requirements for extension of the current prototype; existing single-baseline checks do not establish their implementation.

**VER-01 — Separate work, edition and asset identity.** Identify a specification family, a document work within it, a dated edition or editor-draft commit, and each exact byte asset separately. Retain both the publisher's edition/status and the retrieved asset hash. A changed response body at the same URL is a new asset, not automatically a new semantic edition. Record the relationship and review differences. Mutable latest-version URLs are discovery pointers, never sufficient proof inputs.

**VER-02 — Freeze a semantic baseline bundle.** A verification target names exact document/asset versions, adopted errata, regime/profile, datatype and other external dependencies, extraction and formalization revisions, toolchains and review policy. Resolve dependency versions from each source's actual references; do not substitute the latest RDF, XSD or Unicode specification by name. A proposed replacement needs a compatibility record. Keep document-scope, formalization-scope and implementation-surface scope distinct.

**VER-03 — Preserve edition-specific claims and lineage.** Keep existing IDs such as MT11-* stable. A claim occurrence in another edition has its own versioned record and source ranges. A separate lineage relation may connect one or many old claims to one or many new claims, including splits, merges and omissions. Concept-family identifiers aid navigation but do not imply identical definitions. Equal words, anchors, rule codes, Lean names or text hashes cannot alone establish semantic equivalence when context or imports change.

**VER-04 — Classify changes with evidence.** Record independently (a) source change: moved, editorial, added, removed, split, merged, qualification/dependency/modality/status changed, and (b) claimed mathematical relation: equivalence, strengthening, weakening, conservative extension, incompatibility, partial correspondence or unresolved. Every mathematical relation names its direction, fragment, hypotheses, symbol/term/model transport and proof or counterexample evidence. Human extraction decisions and kernel-checked comparison theorems remain distinct evidence dimensions. An editorial label requires review and cannot bypass dependency invalidation.

**VER-05 — Adopt errata explicitly.** Preserve the original source and separately pin each erratum's text, issuer, date and status. Record proposed, official, withdrawn and disputed corrections without treating these statuses as interchangeable. A baseline may select an explicit correction overlay, producing a distinct bundle identity and affected claim revisions; an updated publisher edition is a separate source. The viewer must expose the original passage, correction and adopted reading. A later specification's retrospective change note is evidence to examine, not automatic authorization to rewrite an earlier Recommendation. Do not permit incompatible overlays in one accepted bundle.

**VER-06 — Keep proposals experimental.** Pin proposals and editor drafts to exact snapshots/commits, record proponents and status, and maintain separate coverage and review state. Alternative proposals may coexist on main in explicitly identified tracks. Their proofs can be checked before adoption, but they must not satisfy baseline obligations or inherit standards approval. Experiments remain inventoried under the formal-artifact rules.

**VER-07 — Share code through checked instantiation.** Permit a reviewed mathematical foundation or parameterized proof to serve multiple editions. Each edition retains its own source mapping, assumptions and dependency closure. Put edition-sensitive syntax and semantic conditions in explicit modules/namespaces or version-indexed interfaces; preserve the source's notation. Do not silently broaden RDF11 terms or replace its interpretation fields to accommodate RDF12. Transfers require typed translations and checked bridges, including failure conditions for partial translations. Library/target reuse is not automatic source-review reuse.

**VER-08 — Prove the claimed compatibility direction.** A cross-edition or cross-family bridge states whether it preserves/reflects syntax, term identity, truth, entailment, query-result multiplicities, ordering or executable observations. A claim of entailment conservativity must cover both directions over the declared fragment and regimes, with explicit interpretation restriction/extension or equivalent evidence. A syntax embedding or one-way truth theorem is insufficient. Include blank scope, literal identity versus value equality, datatype parameters and any feature restrictions; do not silently add finiteness or omit new semantic conditions.

**VER-09 — Keep review and coverage scoped.** Accepted evidence binds to immutable claim content, contextual/dependency versions, formal environment and baseline bundle. Changes invalidate the affected transitive closure; preserve prior acceptance as history. Carry-forward may be proposed with unchanged-input or proved-transport evidence, but needs a recorded policy decision. Report per-baseline and per-regime coverage, imported obligations, unresolved differences and bridge coverage separately. Sharing a theorem does not merge coverage denominators or close an unreviewed source range in another edition.

**VER-10 — Provide a comparison view.** Let reviewers select two bundles, inspect their annotated sources, aligned claims, explicit English/symbol bindings, actual Lean bodies, changed hypotheses and dependencies, bridge evidence, open questions and review history. Mark changes with text labels as well as colour. Show unmatched ranges and removed claims. Distinguish original, corrected, proposed and adopted text. Search must expose family, edition, publication status, regime/profile and mapping status without requiring knowledge of a declaration name.

**VER-11 — Introduce OWL and SPARQL as explicit tracks.** OWL 2 Direct Semantics and RDF-Based Semantics are distinct targets, connected only by a separately scoped correspondence theorem and syntax mappings; profiles and rule fragments need their own applicability obligations. For SPARQL, distinguish graph-pattern matching, algebra evaluation, solution multisets/sequences, expression errors, query forms, update and protocol surfaces. Preserve RDF graph sethood while retaining SPARQL solution multiplicity. Named entailment regimes connect query evaluation to RDF/RDFS/OWL under their specified restrictions; an arbitrary entailment predicate is not evidence of conformance. Honor the dated RDF dependencies actually cited by OWL/SPARQL before proposing bridges to RDF 1.1 or 1.2.

**VER-12 — Version tests and exercise separation failures.** Bind each test manifest, approval status, expectation, comparator, dataset, query, regime and run to its baseline bundle. A fixture reused across versions needs explicit applicability; changed expectations may be legitimate differences. Reject source-range reuse across hashes, implicit cross-version symbol resolution, proposal evidence counted as baseline coverage, unadopted errata, stale dependency approvals and unproved bridge claims. Include separate tests for RDF set enumeration and SPARQL duplicate multiplicities. No test suite is presumed complete for its specification.

## 3. Immutable source and coordinate model

**SRC-01 — Preserve bytes.** Store the exact downloaded document bytes and a manifest containing their SHA-256 digest, byte length, retrieval URL, final URL if redirected, retrieval time, available HTTP metadata, fetching procedure, declared publication version, media type, encoding, and retained license information. Provide an offline copy consistent with the document's redistribution terms. Hash the stored response body before decoding or parsing. Hash rendered HTML, extracted text, and annotations separately; none may replace the original source identity. Permit additional hash algorithms through an algorithm-tagged digest field.

**SRC-02 — Decode explicitly.** For the initial UTF-8 corpus, use strict UTF-8 decoding. Preserve line endings, a leading BOM as U+FEFF if present, and all whitespace. Do not apply Unicode normalization, newline normalization, case folding, HTML entity expansion, or error replacement to the authoritative character sequence. Reject invalid decoding rather than substitute U+FFFD. Record the decoder policy and version. Other encodings require an explicit, reviewed decoding profile.

**SRC-03 — Define “character.”** The authoritative sequence is Unicode scalar values, not bytes, UTF-16 code units, glyphs or grapheme clusters. Positions are zero-based. A range is half-open `[start, end)` with `0 ≤ start < end ≤ N`, where `N` is the scalar count. An astral character occupies one position; a base letter followed by a combining mark occupies two. A CRLF occupies two. Every range includes its source document's digest.

**SRC-04 — Maintain translations.** Store or reproducibly derive mappings among original byte spans, scalar spans, parser/token locations, and browser UTF-16 offsets. Lean's character representation and the browser's string representation must be connected explicitly. A range must be resolvable against the archived source without relying on line numbers, section titles, CSS selectors or DOM paths. Those are useful secondary locators only.

**SRC-05 — Parse HTML faithfully.** These sources are HTML; do not assume that an XML parser will accept or preserve them. Pin the parser implementation, version and HTML parsing profile, with source locations, DOM ancestry and element IDs. Preserve a concrete source/token representation alongside the DOM, because DOM serialization can change quotes, entities, attribute order, whitespace, omitted tags and repaired markup. Parsing must not redefine the authoritative scalar sequence.

**SRC-06 — Map transformed text.** Entity expansion and rendering require a relation between source intervals and displayed intervals, not a constant offset adjustment. For example, all five source characters of `&amp;` contribute to the displayed ampersand. Collapsed whitespace may map many source characters to one display position; some source characters have no visible glyph. Record these cases. Generated section numbers, toolbars or other viewer content must be marked as generated, not attributed to source characters.

**SRC-07 — Preserve revisions.** A changed byte hash creates a new document identity. Annotation migration may propose new ranges but must not silently rebind accepted records to new text. Store the old ranges, proposed ranges, diff and review decision. Recompute proofs and invalidate affected review/build results when their inputs change.

**SRC-08 — Stable identities and evidence hashes.** Hash the extraction manifest, claim versions, symbol mappings, dependency inventories and review decisions independently using deterministic serialization. Keep stable human-readable claim IDs separate from content hashes; editing one claim must not renumber unrelated claims. Record split/merge lineage and bind approvals to exact content versions, not just mutable IDs. Noncontiguous source projections must retain all contributing ranges.

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

**CAT-09 — Orthogonal classifications.** Record source role, normative status, disposition and review state separately. For example, a table is a source role; normative/informative/uncertain is a status; extracted claim/context/excluded-with-reason/unresolved is a disposition. Derive claim normativity from its source spans and context, not its perceived importance. Use [Semantics §2](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#conformance) as the initial policy: expressly non-normative sections, authoring guidelines, diagrams, examples and notes are non-normative; the remainder is normative. Record inheritance and local exceptions per span. Each normative text span must support a claim, a documented definitional/premise component, or an accepted explanation of why no formal proposition applies.

**CAT-10 — Structure and relationships.** Preserve parent source units for paragraphs, tables and numbered conditions while allowing their atomic claims to be reviewed separately. Use explicit relationship types such as `defines`, `uses`, `refines`, `constrains`, `entails`, `equivalent_to`, `generalizes`, `exception_to`, `requires_external_spec` and `possible_conflict`. Give scopes stable identifiers for regimes, datatype sets, graph/dataset contexts and document versions. Preserve modality and logical strength, including permission, obligation, necessity, sufficiency, existence, uniqueness and negative assertions.

### 4.1 Context closure and indexical references

**CTX-01 — Resolve referents.** The precise English restatement and symbol-linked form must resolve semantic references whose meaning depends on surrounding discourse: “this”, “that”, “these”, “it”, “the former”, “the above”, “the following conditions”, “the same graph”, and comparable expressions. Replace them with explicit entity, variable, condition-set or claim references, or provide an unambiguous typed binding. Keep the original source unchanged. A mechanically banned-word list cannot establish context closure; seemingly explicit nouns may also rely on prior definitions.

**CTX-02 — Preserve resolution provenance.** For each resolved occurrence, record its source range, antecedent range or ranges, selected referent, scope, rationale, and review decision. Alternatives remain unresolved until reviewed; do not choose an antecedent solely because it is the nearest preceding noun. The viewer must let a reviewer move from the expanded phrase back to both the original phrase and the passage supplying its meaning.

**CTX-03 — Expose inherited context.** A claim's context frame must include variables and quantifiers introduced earlier, the interpretation/entailment regime, datatype assumptions, vocabulary restrictions, and relevant section/table qualifications. Make ellipsis explicit. Reusing a previously introduced graph variable must not create a new existential or universal quantifier. Every semantically necessary reference must resolve through this frame or a declared dependency; reading the preceding paragraph must not be the only way to discover it.

**CTX-04 — Preserve inference links.** “Thus”, “therefore”, “hence”, “consequently” and similar expressions often introduce a consequence rather than refer to one object. Resolve them into explicit premise/conclusion relationships, including any background definitions or assumptions. Preserve the difference between a consequence asserted by the source and a consequence inferred by the extractor. Removing the connective without recording that relationship loses information. If the premises or direction are uncertain, retain an open obligation.

**CTX-05 — Review contextual expansions.** Treat every expansion as part of extraction fidelity, and review its symbol binding again in the formalization track. Examples for the review tool must include an ambiguous pronoun, a condition inherited across paragraphs, a table-header restriction, and a “thus” conclusion requiring more than the previous sentence. Changing an antecedent or context frame invalidates affected claim approvals. Automated checks can establish reference closure; experts must establish that the resolved meaning is correct.

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

The trust inventory must distinguish kernel-checked proof terms from admitted axioms, `sorry`/`admit`, unsafe or partial executable code, opaque declarations, native/foreign evaluators, reflection and external-prover certificates. Record whether each mechanism actually participates in the claimed proof or execution path. These mechanisms have different implications: `opaque`, for example, is not by itself an admission or a proof defect. Include the project lockfile and reproducible build procedure.

**LEAN-05 — Trace product use.** Map semantic objects to their raw representations, abstraction functions, admission boundaries, mutators, indexes, observations and exported operations. Require refinement statements where an implementation is claimed to realize a specification operation. Trace the relevant path through Lean compilation, WASM, host wrappers and the packaged artifact. A proof about an unused function cannot discharge a different function's obligation. Mark uncovered compiler/FFI/host steps explicitly rather than implying universal verification.

**LEAN-06 — Preserve honest outcomes.** Where an algorithm implements entailment or satisfiability, distinguish a proved positive answer, a proved negative answer, and failure to establish an answer. A search failing to find a contradiction is not automatically a proof of satisfiability. Record soundness and completeness separately, with the supported regimes and datatype assumptions.

**LEAN-07 — State correspondence strength.** Classify the mathematical relationship separately from declaration role and completion status: exact definition, equivalent proposition, one-way soundness, one-way completeness, strengthening, weakening, embedding, approximation, or unassessed. State the direction, domains and conditions explicitly. Record definitional equality, isomorphism and propositional equivalence distinctly. Evidence may be a proved adequacy theorem, an axiom, finite tests, or an unfulfilled obligation; those are not interchangeable relationships.

**LEAN-08 — Audit model differences.** Where Factoidal's model differs from the source model, require a comparison theorem or a documented partial simulation/embedding with its direction, conditions and known counterexamples. As a second worked example, audit `L4Factoidal/RDF/Semantics.lean`: the recorded baseline totalizes property extensions and blank-node assignments and includes an RDF 1.2 term operation. Its later `interpolationComplete` theorem is restricted to triple-term-free graphs, despite introductory commentary describing a missing completeness direction. Review the actual declarations, hypotheses and reference model; neither a comment nor a theorem name establishes equivalence with the W3C model.

**LEAN-09 — Claim-specific fulfillment.** Give each claim an explicit fulfillment criterion and a separate list of proof/adequacy obligations. A correctly translated definition may need no independent theorem. A policy or metadata requirement may instead require an accepted `not_lean_applicable` explanation and a suitable process check. Preserve `unimplemented`, `blocked`, `axiomatized`, `test_only` and `approximate` states. None may silently become fully verified merely because its source range has been classified.

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

**BIND-09 — Structured intermediate form.** Store semantic references, quantifier/binder structure, logical operators and dependency edges in a typed or schema-validated representation; the readable symbol-linked English can be generated from it. Structural validation must detect unbound references, scope errors and unresolved aliases. Missing or inappropriate semantic quantifiers still require fidelity review. Show a three-way comparison of source, English/intermediate form and Lean, with comments attachable to a subphrase, binding or premise.

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

### 6.2 Formal-artifact registry and grounding

**ART-01 — Inventory the whole declared source tree.** Maintain a formal-artifact registry covering every file and declaration in the formalization's declared source roots, including untracked files and modules not imported by the usual build. Specify generated-output and dependency-cache boundaries; do not silently omit a file because it is absent from an import list. Record resolved paths and an explicit policy for symlinks or externally located dependencies. Unknown files and declarations are QA failures, not presumed harmless leftovers.

**ART-02 — Require ownership and purpose.** Each file/module and declaration must have a stable artifact ID, target language/version, owner or review responsibility, lifecycle state, purpose, associated SCD or supporting-directory records, and build/review status. Distinguish active formalization, mathematical foundation, proof helper, executable implementation, adapter, test, experiment, generated artifact and retired material. Helpers and generated declarations may inherit a purpose through an explicit parent/generator record; they cannot inherit it merely by directory proximity. Retired material must not silently remain on an accepted production proof or execution path.

**ART-03 — Use machine-validated labels.** Choose a canonical structured registry, with checked attributes, documentation tags or sidecars as appropriate for each target. Validate agreement between embedded labels, registry entries and elaborated declaration identities. Folder naming, comments and imported module names alone are insufficient. Keep source locations and hashes current, and provide a report of duplicate responsibilities, abandoned experiments, unreachable helpers and declarations with no grounding path. Do not automatically delete such material; require classification, justification, relocation or retirement.

**ART-04 — Account for every term dependency.** Inspect elaborated types and bodies, including implicit arguments, typeclass instances, notation expansions, recursors and generated auxiliary declarations. Every referenced constant must resolve to the registry. Locally bound variables, literals, sorts and expression constructors must be accounted for by the target's binding and foundational rules, rather than incorrectly treated as missing named RDF claims. Give domain-significant constants, such as RDF vocabulary IRIs, explicit semantic grounding. A check over surface identifiers or import names does not satisfy this requirement.

**ART-05 — Ground the directory recursively.** For every application-level declaration used to represent a claim, record a justified path to accepted SCD entries, declared derived implementation obligations, or explicitly catalogued mathematical/logical foundations. The codified directory must include these supporting records as well as source assertions, and distinguish their origins. Do not invent an RDF source sentence for Lean's logic or general mathematical machinery. Foundation boundaries require exact identities, versions, rationale and review; an unrestricted “everything imported is trusted” rule is not a grounding argument. Strongly connected components need a reviewed collective justification and external grounding, not circular approval among their members.

**ART-06 — Prove registry coverage and closure.** Provide a machine-checkable certificate, with a Lean soundness theorem and concrete instantiation, establishing that every inventoried active declaration is classified, every referenced constant is registered, and every required grounding dependency is resolved under the declared policy. Bind it to the source-file manifest, elaborated environment and catalogue hashes. Also check that the file/declaration inventory is complete for the declared roots. State the trust placed in the filesystem scanner, elaborator and dependency extractor: a theorem over a supplied list cannot establish that a faulty extractor omitted nothing. This structural proof does not replace expert review of whether a grounding link conveys the right meaning.

**ART-07 — Audit use and contracts together.** Link exported operations and their actual implementation dependencies to the obligations they must satisfy. Detect a call to an unregistered or differently justified implementation even when a proved function of a similar name exists elsewhere. Require active formal modules to be elaborated by an explicit build target; an unused file must not evade checks. Declare deliberately failing fixtures and draft experiments as such, with separate expectations, rather than allowing them to weaken production gates.

**ART-08 — Support other formalization targets.** Keep source ranges, SCD claims, contextual expansions, review decisions and semantic dependency IDs independent of Lean. Use target profiles/adapters for symbol identity, term structure, elaboration, dependency extraction, proof obligations, foundational assumptions and checker evidence. Lean 4 is the first implemented profile. A future F*, Isabelle or other profile must discharge its own adapter and trust obligations; a mapping to one target does not certify another. File and declaration governance applies to each profile without requiring a new source-claim directory.

### Required worked example: graph sethood

The first vertical slice must connect [Semantics §4](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#notation), its incorporated [Concepts §3](https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/#section-rdf-graph) definition, and the member-based truth conditions to the implementation obligation that graph enumeration emits each RDF triple once.

The presentation must explain why a list can represent a set through an abstraction such as `α(xs) = {t | t ∈ xs}`, and why proving that `[t, t]` and `[t]` have the same truth conditions does not prove that raw list length implements graph cardinality. The implementation link must supply a uniqueness invariant or an appropriate refinement of each observable operation. It must use RDF term identity rather than conflate lexical identity with datatype-value equality.

Show source ranges, extracted English claims, the relevant Lean predicates and proofs, and public-boundary regressions for parsing, enumeration, counts and mutation. Keep per-graph set semantics distinct from SPARQL solution multiplicities. An identical triple in two different graphs remains two different quads. Explicitly display the remaining gap if only some storage or API paths are certified.

### Product obligations exposed by the npm 0.11.0 review

The completed [RDF-related npm review context](context/npm-review-rdf-context.md) supplies concrete cases for implementation-mapping acceptance. The following are proposed structures/contracts, not claims that these protections are already implemented throughout Factoidal. RDF 1.2 and OWL examples remain separate from the primary RDF 1.1 formalization scope.

| Review finding | Proposed structure or proof obligation |
|---|---|
| R02: repeated triples inflate enumeration/counts | Certified graphs with uniqueness under RDF term identity; datasets with unique graph names; raw parse output admitted before semantic use; membership, cardinality and mutation-preservation proofs |
| Index/backend can diverge from stored data | An indexed-dataset structure whose index carries a `Represents index dataset` proof, including all lookup behavior used by evaluation |
| R08: nested blank nodes escape scoping | A single parametric traversal `mapBNodes : (α → β) → Term α → Term β`, used by public scoping; structured scope/local identities; occurrence-preservation, injectivity and graph-isomorphism proofs |
| R09/R12: versions drift between parsers, results and host types | Version-indexed terms, datasets, requests and graph results; explicit checked downgrade; one versioned protocol schema for codecs and host declarations |
| R03/R13: SERVICE registry or output base is lost | A complete execution-context record carried through parsing/evaluation; distinct mapping-document and output bases; format selection operates on the same evaluated result |
| R11: validation bypass and invalid emitted labels | Validated CSVW metadata required by conversion; separate internal blank-node identity and legal serialized label; injective encoding and parse/write round-trip up to isomorphism |
| R10: candidate search state reported as a model | Verdict constructors requiring evidence of satisfiability or refutation for the original supported ontology/regime; `unknown` for unsupported, inconclusive or exhausted search; translation adequacy included |
| R07: native and public resource budgets differ | Explicit resource policy in requests and capability metadata; budget exhaustion is a distinct outcome, with no transfer of a native budget claim to a different public configuration |

**LEAN-10 — Do not trust type names.** A refinement is only as strong as its predicate. At the recorded baseline, `WfIri` checks nonemptiness and the presence of a colon; `WfLiteral` checks combinations of datatype, language-tag presence and direction. Neither name alone establishes all lexical constraints of its corresponding RDF concept. SCD mapping must inspect and justify the actual predicate, identify stronger admission/serialization requirements, and expose any remaining gap.

## 7. Expert review interface

**UI-01 — Click anywhere.** Clicking or keyboard-selecting any specification text must open the records associated with the exact displayed location and its source ranges. This includes headings, punctuation, mathematics, table headers/cells, notes, examples, links and collapsed whitespace. If several claims apply, show all of them. If there is no claim, show the explicit disposition or unresolved status. A click must never silently do nothing because extraction missed that passage.

**UI-02 — Source fallback.** Provide synchronized rendered and raw-source views. Every raw scalar position, including tags, attributes, comments, scripts and invisible text, must be selectable in the source view. For graphical mathematics or images, clicking the object must open its source-element record and linked claims; archived assets and textual/formal interpretations need their own provenance. Do not claim that invisible source syntax has a clickable glyph in the rendered view.

**UI-03 — Preserve context.** Show the source passage with nearby context, exact source digest/ranges, English claim, normative status, assumptions, dependencies, review history, Lean declaration/type, proof status and implementation links. Allow navigation from any claim or Lean declaration back to every supporting range. Distinguish a direct statement range from a contextual reference.

Show resolved indexicals and inherited context on demand, with links to antecedent passages. Display claim-to-Lean correspondence strength and unresolved dependency leaves alongside proof status. Rendering need not be pixel-identical across browsers; source coordinates and pinned content remain authoritative.

**UI-04 — Review operations.** Experts can propose, split, merge, correct, accept or reject claims and dispositions; adjust ranges; link dependencies; resolve ambiguities; and review Lean fidelity. Record reviewer identity, timestamp, rationale and before/after versions. AI proposals begin unreviewed. Do not overwrite accepted decisions or imply that a displayed reviewer name provides cryptographic authentication.

Preserve disagreements and their resolutions. Define a release review policy specifying required reviewer roles, sign-off criteria and what independence means; optional reviewer qualifications may be recorded. An approval in one review track cannot satisfy another track's sign-off automatically.

**UI-05 — Useful views.** Provide filters for unaccounted source, unreviewed extraction, normative obligations, missing dependencies, unformalized claims, failed proofs, unproved implementation mappings, and test-only evidence. A heatmap may help navigation but must not replace textual status or collapse the four completion measures.

**UI-06 — Faithful, inert rendering.** Render archived HTML without executing its scripts or fetching unpinned resources. Use an explicit rendering profile and retain the source map through any sanitization. Reflow, CSS and accessibility adaptations must not alter provenance. Provide keyboard navigation and text equivalents; review must not depend on color or pointer use alone.

**UI-07 — Review packets and dependency exploration.** Export review packets for either source → SCD or SCD → Lean, containing pinned inputs, precise questions, current decisions and unresolved objections. The formalization packet must include ordinary English, symbol-linked English, the binding table, exact Lean types and an expandable dependency graph. A reviewer must be able to open each dependency's own source and acceptance history. Support comments on individual bindings as well as whole claims. Generating a packet is not authorization to publish it or contact reviewers.

## 8. Test evidence and reproducibility

**TEST-01.** Catalogue test cases by stable test IRI, repository commit, manifest path and hash, active manifest membership, approval status, inputs/results, entailment regime, and recognized/unrecognized datatypes. Preserve retired or inactive descriptions separately from active entries. An expectation of `false` in an entailment manifest needs its semantic interpretation recorded; it is not merely a missing output graph.

**TEST-02.** Link a test to the particular claims it exercises with an explanation. Permit many tests per claim and many claims per test. Mark inferred associations as provisional. Do not infer semantic coverage from test filenames or from presence in the same suite.

**TEST-03.** Store per-test outcomes and the actual execution surface: pure Lean, native harness, WASM operation, or npm API, plus code/artifact hashes and invocation. Preserve failures, skips, unsupported cases and unrun cases. Test success cannot discharge a universal proof obligation; proof success cannot establish that a different product entry point ran correctly.

**TEST-04.** Add project-owned regressions for specification obligations absent from the external corpus. Clearly separate them from W3C tests. The sethood worked example must include repeated triples, lexical/value distinctions, named-graph scope and legitimate query multiplicities. Do not assert that any W3C repository promises complete specification coverage.

**TEST-05 — Match comparisons to claims.** Record what each test comparator observes or intentionally quotients away. Graph isomorphism/canonical-set comparison cannot detect a raw enumeration duplicating the same triple; add separate API enumeration/cardinality checks. Test blank-node identity consistently across all nested occurrences and graph-name positions. Run relevant reproductions against the exact packed artifact, with nonempty test discovery, ordinary passes, expected failures, unsupported cases and environment-blocked cases reported separately. Native-only evidence cannot satisfy this product gate.

## 9. Data model and deliverables

Use a portable, schema-validated source format with stable IDs and deterministic serialization, initially JSON or JSON Lines. SQLite may provide indexes and queries but must be rebuildable from that source. Required entities are:

| Entity | Essential contents |
|---|---|
| Corpus/document/asset | Scope, exact bytes, digests, decoding profile, version, license, dependency role |
| Specification family/edition/baseline | Publisher status, exact assets, adopted correction overlays, regime/profile, dependency versions and coverage scope |
| Claim lineage/change/bridge | Versioned endpoints, split/merge alignment, change classification, transport maps, precise relation and review/proof evidence |
| Range/atom/source map | Document identity, scalar endpoints, byte/display relationships, disposition references |
| Claim/disposition | English statement or classification, category, normativity, assumptions, source roles, review state |
| Context/referent resolution | Original occurrence and antecedent ranges, bound referent, inherited context, inference links, alternatives and review decision |
| Symbol-linked claim/binding | Versioned intermediate statement, bound phrase occurrences, concept IDs, semantic roles, variable scopes, exact Lean resolutions, residual translation gaps |
| Dependency | Claim/document links, imported meaning, applicability, unresolved status |
| Formal artifact/target profile | File and declaration identity, ownership, purpose, lifecycle, grounding, target-specific extraction/checking rules, inventory certificate |
| Lean mapping | Declaration identity/type, role, correspondence strength/direction, hypotheses, fulfillment criteria, build/proof evidence, fidelity review |
| Implementation mapping | Representation and operation, abstraction/refinement, product path, remaining trust boundaries |
| Test/run | Manifest identity, expectation, surface, artifact versions, per-case outcome, claim links |
| Review/certificate | Immutable decision history, accepted versions, checker result, concrete proof, trust manifest |

Deliver an offline-capable review viewer, a deterministic validator/certificate generator, the Lean checker and concrete source-coverage proof, the assertion catalogue, declaration/build extractors, pinned test metadata/results, and instructions to reproduce the evidence. Keep draft and accepted certificates separate. A reviewer must be able to inspect exported data without running the viewer.

Existing `_LEAN/ledger/` files are preliminary inputs. Their section links and file checks do not constitute the character-range catalogue, expert approval, declaration verification or concrete coverage proof required here. They must be migrated and reviewed, not grandfathered into accepted coverage.

### 9.1 Continuous validation and evidence releases

**CI-01 — Deterministic validation.** Regenerate and compare source fingerprints, offset indexes, DOM projections, catalogue schemas, range coverage, context resolution links, symbol bindings, artifact inventory, and dependency/assumption graphs. Reject broken coordinates, unbound symbols, dangling references, unregistered artifacts, stale evidence and claims of acceptance not justified by the declared review policy. Record toolchain versions and a machine-readable audit manifest alongside a static human-readable report.

**CI-02 — Separate valid drafts from completed coverage.** A structurally valid draft may contain explicitly unresolved semantic obligations and report `pipeline_valid`; it must not report `coverage_complete`. The complete-source gate rejects unresolved source atoms. The strict declared-scope completion gate requires all normative dispositions reviewed, applicable claims faithfully mapped, required proofs checked, and dependency meanings justified. Reviewed non-applicability is permitted when a proposition is inappropriate; excluding a required normative obligation narrows the claim and prevents claiming full coverage of the original scope.

**CI-03 — Mutate the evidence chain.** Demonstrate rejection or invalidation when a source character is omitted, an entity projection changes, an accepted disposition is altered, a symbol points to a different declaration, a premise disappears, an undeclared axiom enters the proof closure, an antecedent changes, an orphan Lean file appears, or a required grounding dependency loses approval. Use curated semantic challenge cases for wrongly excluded normative text or incorrect referents. CI can catch unauthorized changes and stale approvals; it cannot generally recognize an expert's newly approved but mistaken reading of English.

**CI-04 — Publish precise statuses.** Every reported status must name its scope, input hashes, evidence version and required review policy. Use separate statuses with the following meanings:

| Status | Meaning |
|---|---|
| `source_bytes_verified` | Archived bytes match the recorded source fingerprint; retrieval provenance is available |
| `source_partition_complete` | Every source scalar has a valid accountability disposition |
| `normative_disposition_reviewed` | No normative span in the stated scope awaits disposition review |
| `formalization_mapped` | Applicable claims have reviewed structured mappings; proofs may still be pending |
| `artifact_grounding_checked` | The declared formal source tree and term dependencies satisfy the registry and grounding policy |
| `lean_obligations_checked` | The stated Lean obligations pass under the disclosed foundations and trust boundary |
| `spec_mapping_audited` | Required independent reviews accept extraction, formal translation and dependency meanings for the pinned scope |
| `implementation_refinement_audited` | The named executable/product paths have the separately specified refinement and artifact evidence |

These are independent evidence dimensions, not a single pass badge. In particular, `spec_mapping_audited` does not imply that the npm API was audited. A release bundle may be signed under a declared identity/key policy; a signature authenticates the bundle and does not strengthen its semantic claims.

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
| G3 — Context and model adequacy | Indexicals and inference links have reviewed resolutions; the interpretation-model example exposes one-way results, restrictions and open comparison obligations |
| G4 — Formal-artifact grounding | Every file and declaration in the declared roots is classified; concrete registry/closure checks detect orphan artifacts, unexplained term dependencies and stale support records |
| G5 — Edition and correction separation | Two pinned editions, an erratum overlay and an experimental proposal coexist; ranges, review acceptance and coverage cannot leak between bundles; dependency changes invalidate affected evidence |
| G6 — Cross-family and version bridges | A selected compatibility claim exposes and checks its transport, direction and conditions; OWL semantics and SPARQL multiplicities stay distinct; unsupported connections remain explicit obligations |
| H — Full declared-scope completion | All in-scope assertions and imports have accepted fidelity review, required formalizations/proofs, and the implementation evidence necessary for the stated Factoidal coverage claim; no unresolved normative obligations are hidden |

Implement in this order:

1. Inventory existing RDF/RDFS/Unified semantics, the theorem registry, source comments and actual declarations. Freeze sources and schemas; implement decoding, coordinates, source maps and partition validation.
2. Build the rendered/raw viewer and review operations. Demonstrate character accountability with unresolved semantic regions visible.
3. Complete the graph-sethood vertical slice, including the concrete Lean coverage certificate and executable links; then audit the interpretation-model example and its comparison obligations.
4. Expand the AI-proposed, expert-reviewed inventory through all four assertion categories, section by section, including imported definitions, informative material and explicit context/referent resolution.
5. Map and audit existing Lean definitions/proofs, register the complete formal source tree and grounding dependencies, fill formalization gaps, connect executable operations, and integrate pinned test evidence.
6. Seek acceptance of the full declared-scope claim only when Gate H is satisfied. Publish intermediate artifacts with their exact achieved gates and outstanding obligations.

Completion of this requirements document authorizes neither a claim of completed formalization nor a conformance certificate. Its purpose is to specify the evidence that those future claims must provide.

### Decisions to settle during implementation review

Choose the canonical structured format and typed-intermediate schema; select and pin the HTML/source-map and target-environment extractors; settle attribute/sidecar conventions and the foundation-grounding policy; and define reviewer independence, disagreement resolution and optional signing arrangements. Raw Unicode scalar coordinates, the two review tracks and explicit unresolved states are requirements, not open alternatives.
