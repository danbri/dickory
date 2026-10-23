# Vocabulary pre-interpretations and full-name completion

23 October 2026. Sixteenth working increment. The proofs cover simple-semantic name locality; the finite-resource bound remains open.

## Source reading and separation of obligations

[Informative Appendix B](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#finite_interpretations) explicitly presents a sketch without proof. Its third paragraph combines a restricted name vocabulary, the proposed N+B+1 resource bound, extension to full interpretations, preservation of relevant truth, and equivalent satisfiability and entailment. An AI source-reading pass assessed the whole paragraph and its surrounding qualifications. This is not accepted expert review.

The source catalogue retains `MT11-FINITE-SIMPLE-PREINTERPRETATION` as partially covered and isolates the proved name-completion component as `MT11-SIMPLE-PREINTERPRETATION-COMPLETION`. Both are associated with the original paragraph, and the sketch disclaimer is separately associated. The definition record remains partial: Appendix B informally describes a mapping into IR, while the precise refinement reuses normative §5's IS into IR union IP and partial IL. No property-as-resource or total-literal assumption has been introduced.

Source selectors are `#finite-interpretations-informative > p:nth-of-type(2)` for the disclaimer and p3 for the simple pre-interpretation sketch. The term itself is anchored at `#dfn-pre-interpretation`. The mapping resolves “Any such pre-interpretation” to the structures and proposed bound immediately preceding it, without treating that bound as already proved.

## Checked construction

`PreInterpretation V U` is the existing `SimpleInterpretation` applied to IRI and literal subtypes carrying membership evidence in V. It keeps the existing resource and property roles, partial literal denotation, and nonempty IR. V and U need not be finite.

`PreInterpretation.extend` retains IR, IP and IEXT. Known names retain their denotations; unused IRIs denote one existing resource and unused literals remain undefined. Restriction back to V recovers the exact original interpretation. The construction proves denotation equality and triple/whole-graph truth equivalence for every fixed blank assignment, then existential satisfaction equivalence. A theorem also covers any same-carrier completion whose restriction is the given interpretation.

Generic name transport and interpretation pullback live in `NameMaps.lean`. They preserve the graph's set representation and blank identities, and commute with the ordinary-to-generalized syntax embedding. Arbitrary name maps preserve simple entailment in one direction. Reflection for vocabulary inclusion uses the explicit completion proof; it is not asserted for arbitrary maps that may identify names.

Ambient graphs can be restricted using evidence that their vocabularies lie in V; inclusion recovers the exact original triple sets. `preinterpretation_entailment_iff` and `preinterpretation_satisfiable_iff` connect these representations to the existing model-theoretic definitions. Entailment quantifies over all V-preinterpretations, including infinite carriers. Graphs may have distinct blank types, and their existential satisfaction witnesses remain independent.

For finite graphs, exact name lists feed the existing duplicate-free `Enumeration`. A literal contributes its literal name and its datatype IRI, as §4 requires. `finite_shared_vocabulary` enumerates exactly the union of the two graph vocabularies; `finite_vocabulary_comparison` combines this with the entailment equivalence. Finite intermediate lists may repeat names, but the resulting enumeration has proved uniqueness and exact membership.

## What this does not establish

The N+B+1 resource bound, finite-carrier countermodel equivalence and decision/complexity claims remain unproved. N counts distinct names, not denotations; finite vocabulary alone does not ensure finite blank support. A future countermodel compression must preserve a premise witness and conclusion falsity without accidentally identifying independent blank witnesses.

Appendix B's weakened datatype conditions, (N+B)×(D+1) bound, and RDF/RDFS extensions are separate obligations. This simple completion may not satisfy their additional semantic conditions. Generic name-map lemmas likewise do not establish compatibility between specification editions. Concrete IRI/literal domains, accepted source/formalization reviews and npm/WASM refinement remain external obligations.

The short Statements/Syntax/Simple reviewer route remains 371 lines. The new claims link to their actual bodies and curated English glosses. All reviews remain pending.

## Deliberate registry audit

The registry adds 82 declarations: 41 authored declarations and 41 generated helpers. This includes reduction equations for the existing term/triple names definitions, now requested by the new proofs. Private matcher equations retain explicit parents. Every existing declaration keeps its type, kind and compiler-attributed module.

The inventory has 1,748 local declarations in 59 formal files, with a dependency closure of 6,369 declarations. The only changed existing formal files are the root import and generated source-accountability snapshot. No foundation modules or logical axioms were added; the allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.

## Validation

The full 61-job Lean build and frozen-registry verification pass. All seven rejection checks and 15 Python tests pass; the source catalogue and annotated review viewer regenerate successfully. Site staging/link checks, JavaScript syntax, methodology-skill validation and whitespace checks pass. The browser suite now includes four additional interaction checks (66 configured in total), covering precise pre-interpretation fields, common-assignment truth preservation, both comparison directions and the still-open resource bound. Chromium CI must pass before publication.

The catalogue has 172 mappings among 217 preliminary claim records, including partial mappings, and nine open source questions. No expert review is accepted. The complete-coverage gate continues to reject completion, including missing implementation refinement; these counts are not a compliance percentage.
