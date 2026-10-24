# Structured literal identity and imported language-tag syntax

27th working increment, 24 October 2026. Structured literal syntax, imported grammar and their connected proof obligations are implemented. Expert source reviews, full RDF/S coverage and package refinement remain incomplete.

## Source reading and version boundary

The existing user-requested source-reading subagent used AI close reading of the pinned RDF 1.1 Concepts §3.2–3.4 and Semantics §4/§7.1. HTML parsing located the selected passages. RFC 5646 §2.1 and §2.2.9 supply the imported well-formed-language-tag grammar. A second AI fidelity pass checked all grammar branches, the 26 grandfathered alternatives, raw-case identity and the normalization/model hypotheses; it found no substantive source-fidelity defect. This is draft assistance, not accepted expert review. The archived RFC HTML has SHA-256 `b184da959296601926af6723163b89dcc1f50a39c27f8abbf8b46de905d75a39`; it remains unmodified.

Concepts §3.3 defines literal equality component by component, permits lexical tag lowercasing, and specifies lowercase tag values. Preserve raw language-tag spelling in RDF 1.1 literal identity. The [22 May 2013 RDF WG discussion and resolution](https://www.w3.org/2013/05/22-rdf-wg-minutes.html) supports this reading. The [7 April 2026 RDF 1.2 Concepts CR, §3.4.1](https://www.w3.org/TR/2026/CR-rdf12-concepts-20260407/#section-Graph-Literal) retrospectively explains the difference between the versions. Those documents are supporting historical evidence, not replacements for the pinned normative RDF 1.1 text; no cross-edition bridge or approved fidelity review is claimed.

## Formal representation and connected results

`StructuredLiteral Iri langString` has ordinary typed and language-tagged constructors. Both retain a Unicode lexical string. Ordinary literals carry a datatype unequal to langString; tagged literals carry a raw string and a proof of BCP47 well-formedness, with datatype fixed to langString. Component equality determines the entire literal. Datatype lexical validity and NFC normalization are not constructor preconditions. IRI validation remains an explicit separate obligation.

The grammar follows every RFC 5646 §2.1 branch, including private-use tags and all 26 fixed grandfathered alternatives. ASCII lowercasing is used for grammar matching while the original spelling remains available. Splitting uses the standard proved list operation on Unicode characters; a reconstruction theorem confirms that no characters are discarded. Lowercasing is proved idempotent and preserves well-formedness. The grammar is a proposition with certified constructors, not yet an executable string parser.

RFC §2.2.9 distinguishes well-formedness from the stronger validity class. Registry membership and duplicate variant/singleton exclusions are not silently added to RDF's imported well-formedness condition. Registry validation, extension-specific validity and RFC 4647 language matching are separate obligations.

The new representation instantiates the existing `LiteralSyntax` interface and constructively supplies every language-space representative. This discharges `RDFSModelConstruction.LanguageCoverage` for theories using this syntax and connects directly to the existing base-recognition model-existence theorem. It does not supply prescribed XSD datatype meanings or characterize arbitrary-graph consistency.

Optional tag normalization leaves lexical form and datatype unchanged. With langString recognized, it preserves denotation and whole-graph satisfaction, using the existing simultaneous literal-substitution theorem and one shared blank assignment. It is idempotent but need not preserve RDF 1.1 term identity.

The checked symbolic-name example distinguishes `"chat"@FR` from `"chat"@fr`. The upper-case singleton does not simply entail the lower-case singleton; with recognized language semantics they are D-equivalent. A graph containing both triples has a certified two-element enumeration. Normalizing it yields a one-triple set and a certified one-element enumeration. The general `Enumeration.imageDeduplicated` construction enforces uniqueness even when the mapping identifies input members.

These are formal contracts and proofs. No parser, JS/WASM wrapper or published Factoidal artifact has yet been shown to consume them.

## Integration and verification

The catalogue has 204 mappings among 240 draft records, including partial mappings, across two pinned W3C sources and the imported RFC. The RFC's remaining text is explicitly unresolved. All 14 prior source questions remain open; no expert approval is inferred from the AI fidelity pass.

The frozen registry contains 3,363 local declarations and an 8,227-declaration dependency closure across 99 local formal files. All prior declaration signatures are unchanged. The increment adds 98 declarations with curated glosses and 77 compiler helpers with explicit grounding. The reviewed library closure adds 111 safe declarations, including six newly reached standard-library modules for lists, string splitting, modification and length. No added axioms, unsafe local definitions or native-decision proofs occur. The short Statements/Syntax/Simple review route remains 394 lines.

Full build and registry verification pass, as do 14 rejection checks, 16 Python tests, 12 executable closure checks and 18 instance-search checks. The rejection suite now checks untagged langString construction and an empty language tag. The source generator was corrected to include each imported document's unresolved disposition in the Lean partition certificate; the certificate rejected the omitted RFC record before this fix. Browser and deployment validation are recorded separately when run.

The viewer names the imported RFC separately and preserves the selected source when a claim has passages in several documents. This makes both the RDF import and the RFC definition inspectable without selecting a claim forcing navigation back to the first document. It is not the proposed multi-edition comparison UI.

Local site generation and link checks pass. After installing the pinned browser dependencies with the available Node 22 runtime, all 136 Chromium check groups pass locally. The first CI run also passed formal verification but correctly withheld deployment when a stale reload assertion expected three declaration blocks instead of the four now mapped to triple-term domains. That assertion is corrected; the CI browser gate must pass before Pages deployment. The initial missing-package/DNS attempt is not counted as a pass.
