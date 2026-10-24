# Semantic extensions: syntax admission, truth and regime connections

24 October 2026, twentieth increment. This extends the formal mapping of normative §§3 and 5, connecting their requirements to the existing simple, D, RDF and RDFS model classes. It does not establish full-spec coverage, expert acceptance or product refinement.

## Source requirements and construction

The source-reading subagent used AI close reading of §§3 and 5 and the defining passages in §§7–9. Section 3 permits additional syntax requirements and requires simple entailments to survive when the relevant syntax conditions hold. Section 5 separately requires preservation of the simple truth conditions. The requirements do not demand that every legal graph be satisfiable or that arbitrary combined semantic assumptions have a model.

`SemanticExtension.lean` supplies a precise construction with two independent fields: `legal`, a predicate on ordinary RDF graphs, and `conditions`, a predicate on simple interpretations. Ordinary `Graph` already enforces triple term categories. Concrete IRI and literal lexical validity remain external obligations.

`AdmissibleGraph` contains a graph and its admission proof; `Model` contains an interpretation and its condition proof. The extension's `Satisfies` is exactly the existing simple satisfaction relation, retaining one assignment across all triples and consistent use of each IRI's denotation. `Entails` accepts two admitted graphs before quantifying over the selected models. Illegal comparisons therefore cannot become vacuously successful through an implication whose legality premise is false.

`entails_iff` connects this typed interface exactly to `EntailsUnder`. `preserves_simple` proves preservation of simple entailment for admitted pairs. Reflexivity, transitivity, subgraph entailment, premise monotonicity and valid-process transport retain the relevant admission proofs. None proves that syntax is closed under those operations.

## Existing regimes and refinement

The simple, datatype, RDF and RDFS constructors all use unrestricted admission over ordinary graphs. `no_additional_syntax` checks this statement for all four regimes. Their model conditions are respectively True, DModel, RDFModel and RDFSModel. Four entailment-equivalence proofs connect these constructors to the existing definitions; they are not independent reimplementations of RDF semantics.

`Refines` requires inclusion of both legal graphs and model classes. Its entailment theorem transfers weaker entailment to stronger conditions; its satisfiability theorem transfers in the opposite direction. RDF refines D and RDFS refines RDF with the same meanings and compatible vocabulary parameters. Increasing recognition while keeping the datatype theory fixed supplies another refinement. Arbitrary extensions are not assumed ordered. These proofs use the model definitions and §3, leaving the previously recorded reversed-arrow source questions unchanged.

`meet` conjoins two admission predicates and two model conditions. It refines each input but does not prove that their combination has any model or legal graph. Neither refinement nor shared code is a cross-edition theorem; an RDF 1.1/1.2 bridge still needs its own term/model transport and scope proof.

## Checked boundaries

`ExtensionBoundaries.lean` defines an illustrative policy requiring one chosen ground triple. Its singleton graph is admitted and simply entails the empty graph, but that empty graph violates the policy. This formally separates valid deletion from preservation of admission. It does not impose the policy on RDF itself.

The same file proves that a graph containing a recognized ill-typed literal is admitted by the datatype regime but is unsatisfiable. It consequently entails every admitted conclusion. This is semantic inconsistency, distinct from malformed triple syntax or an extension syntax violation. No processor error-reporting behavior or inference-execution mandate follows. A negative compilation check confirms that the required-triple policy rejects an empty graph at the admission boundary.

## Richer model presentations

`ExtensionPresentations.lean` permits enriched model structures with their own truth relation. Each must provide a reduct to a simple interpretation and prove **both directions** of RDF truth correspondence on every admitted graph. Selecting precisely those reducts yields a `SemanticExtension`; the enriched entailment relation is proved equivalent to its entailment relation.

The reduct need not be injective or cover all simple interpretations. The carrier universe and enriched-model-data universe remain separately parameterized. Lean emits an advisory that these universe parameters occur together in the structure's overall sort; they are intentionally distinct in its fields and are not suppressed.

This is a reusable conditional bridge, not a formalization of OWL, RIF, SPARQL or modal datasets. Their encodings, admissibility and truth correspondences remain separate obligations. Dataset-policy interfaces alone do not supply this proof. The source has not been interpreted as establishing an exhaustive classification of all extensions.

## Source locations, catalogue and review

The newly associated passages are `#semantic-extensions-and-entailment-regimes > p:nth-of-type(1)`–`(3)`. Existing mappings retain paragraph 4's qualified preservation requirement and `#simple-interpretations > p:nth-of-type(1)`'s truth-condition requirement. Defining support is in `#D_interpretations > p:nth-of-type(1)`, `#rdf-interpretations > p:nth-of-type(2)`–`(3)` and `#rdfs-interpretations > p:nth-of-type(5)`. The ill-typed boundary reuses §7.2's satisfiability/unsatisfiability definitions and existing proofs.

Context records resolve “such set of semantic assumptions”, “In such cases”, and the reference to the extension's syntax conditions. The original source bytes and source questions are unchanged. Two previously unmapped entries now have partial mappings, and the existing preservation mappings include the admission and enriched-presentation proofs. There are 179 mappings among 221 preliminary records, including partial mappings. These counts are not a compliance percentage. All extraction and formalization expert reviews remain pending.

The short Statements/Syntax/Simple review route remains 393 lines. The new modules are supporting material reached through their mapped claims. The README and repository methodology describe the admission/truth distinction and the limitations on proof reuse.


## Deliberate registry audit

The inventory adds 93 declarations: 50 authored declarations with curated English glosses and 43 generated fields, constructors, recursors, equality rules and helpers with explicit parents. Every prior declaration retains its type, kind and module attribution. No foundation modules or axioms are added; the allowed axioms remain propext, Classical.choice and Quot.sound.

The registry contains 2,120 local declarations across 69 formal files, with a closure of 6,777 declarations. The only previously inventoried formal files changed are the root import and the generated source-range snapshot; three source modules are deliberately enrolled. The inventory record_count metadata is corrected to its actual existing 221 records; no new source claim was invented to increase that count.

## Local validation

The pinned Lean build passes all 71 jobs. The formal registry and source mapping verifier passes, all eight rejection checks pass, and all fifteen Python tests pass. The generated viewer includes the new source associations, actual Lean bodies and English glosses. The skill validates and the browser test script passes JavaScript syntax checking. Chromium interactions and deployment are checked separately by the publication workflow for the resulting commit.
