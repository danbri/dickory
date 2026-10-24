# Local datatype models and bounded satisfiability

Update: the [nineteenth increment](20261024-datatype-completion.md) now constructs full datatype completions, proves ordinary-conclusion entailment equivalence and checks the generalized scope obstruction. The following records the eighteenth increment as published.

24 October 2026, eighteenth increment. Source extraction and formalization review remain pending. This increment adds checked datatype results; it does not establish full RDF/RDFS coverage, the printed datatype bound, datatype entailment equivalence, or package refinement.

## Source reading and the selected precise definition

The pinned RDF 1.1 Semantics Appendix B is informative. Its fourth paragraph localizes datatype literal-value obligations to literals occurring in the compared graphs, prints `(N+B)*(D+1)` as a resource bound, and discusses extension to full interpretations. Read that paragraph with the preceding definition of N and B, normative §5 interpretation components, and §7's fixed datatype identification and literal conditions. The source-reading agent used AI close reading; the catalogue locator only selects its identified paragraphs.

`DatatypePreinterpretations.lean` gives a precise proposed reading. `PreInterpretation.DConditions P T D ρ` retains the original external datatype theory T, the recognized-IRI set D and one coherent value realization ρ. Recognized IRIs present in V denote their fixed datatype identities. Vocabulary literals retain the original normalized language-pair values or ordinary lexical-to-value results. Recognized ill-typed vocabulary literals remain undefined. Literals absent from V impose no local literal-denotation obligation.

This preserves §5's separate IR and IP roles, total local IS and partial local IL. It does not turn all properties into resources. The underlying value realization may describe values outside the active domain without requiring those values to belong to IR or IP. A finite local interpretation therefore need not contain every value of a recognized datatype.

Three checks connect this definition to existing formal material:

- Restricting any full D-interpretation's names satisfies these local conditions with the same realization.
- If V contains every name, local conditions are equivalent to the original full `SimpleInterpretation.DConditions`.
- A supported restriction of IR/IP preserves literal values, undefined literals and every localized datatype condition. Alias denotations remain coherent.

The claim remains a partial definition mapping because Appendix B sketches rather than fully specifies its weakened structures. Concrete literal syntax and built-in datatype meanings remain external obligations.

## Checked results and their directions

`FiniteDatatypeModels.lean` reuses the preceding simple compression construction. It retains comparison-name values, one satisfying premise assignment's values on counted blanks, and one resource for nonemptiness. Both IR and IP are restricted; their union has at most N+B+1 distinct members, so IR has that bound too. The ambient Lean carrier can still contain unused objects. The recognized datatype set need not be finite for this derived bound.

`finite_d_pre_countermodel` obtains the exact name-union and shared-blank-union enumerations from finite graphs. Full D-nonentailment supplies a weakened countermodel within the bound. Compression preserves premise satisfaction and reflects every conclusion over V into the original model, thereby retaining conclusion falsity. This is one direction only. Accordingly, `d_entailment_of_bounded_preinterpretations` gives a sufficient condition for full entailment; it does not say every weakened countermodel extends to a full countermodel.

For satisfiability, both directions are proved by `d_satisfiable_iff_bounded_preinterpretations`. The reverse direction takes a different route: a local satisfying model cannot contain an occurring recognized ill-typed literal; the existing characterization then constructs a full D-model. This new model need not retain the local IEXT or the truth of any other graph. Existence of some full model for G is weaker than completing a given pre-interpretation while preserving a comparison.

`Statements.datatype_preinterpretation_satisfiability` is a one-line alias with the complete statement, source anchor and explicit scope. The short Statements/Syntax/Simple review route remains under 400 lines. Every authored declaration has a curated draft gloss; projections retain their structure context in the viewer.

## The empty-comparison bound question

`empty_comparison_counts` proves that two empty graphs have zero names and zero occurring blanks. `resource_enumeration_pos` proves that any finite enumeration of a §5 resource universe has positive length. The combined theorem `empty_comparison_printed_bound_conflict` records both facts together with full D-satisfiability of the empty graph:

- `(0+0)*(d+1)=0` for every natural number d, independently of how recognized datatype aliases are counted.
- No pre-interpretation retaining nonempty IR can meet that resource bound.
- The empty graph is nevertheless D-satisfiable for the existing external datatype interface.

This is a checked conflict under the explicit §5-faithful refinement, not an adopted erratum. The source reader found no stated empty-graph exception or automatic augmentation of the graph vocabulary. `Q-DATATYPE-PREINTERPRETATION-ZERO-BOUND` requests expert disposition. The printed source stays intact, its unrestricted mapping stays partial, and the N+B+1 result is labelled as a separate derived bound. The certificate is not a nonempty-graph counterexample or a failed-entailment example.

## Remaining completion work

The new `MT11-DATATYPE-PREINTERPRETATION-COMPLETION` entry keeps the full-model extension claim visible and unmapped. Restoring values for all ambient recognized literals can enlarge IR. Simple name completion, which leaves IR/IP unchanged, does not discharge that obligation. Equality of ground triple truth does not by itself prove preservation of existential graph satisfaction with one shared blank assignment.

Generalized predicate blanks require special attention if a previously property-only denotation becomes a resource. This is a proof obligation, not a checked counterexample in this increment. The source extends its definitions to generalized syntax, so a future ordinary-only result must retain that qualification rather than silently changing the source scope.

The printed multiplicative bound, effective search, concrete datatype meanings, RDF/RDFS pre-interpretations, cross-edition bridges and product refinement remain open. Tests and machine-checked proofs do not supply expert acceptance of the source-to-claim or claim-to-Lean mappings.

## Catalogue changes

Three records split the local conditions, derived bounded satisfiability result and unproved completion obligation from the existing datatype sketch. There are 220 preliminary records and 175 mappings, including partial mappings. There are ten open source questions and no accepted expert reviews. These counts are not compliance percentages.


## Deliberate registry audit

The frozen inventory adds 41 declarations: 24 authored declarations with curated glosses and 17 generated projections, constructors, recursors and matcher/equation helpers. Generated helpers have explicit parents, including newly needed equations of existing definitions. All previous declaration types, kinds and module attributions remain unchanged. No foundation modules or axioms were added; the allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.

There are 1,872 local declarations in 63 inventoried formal files and an elaborated dependency closure of 6,513 declarations. The changed existing formal files are the root import, headline aliases and regenerated source-range snapshot; the two new modules are explicitly enrolled. Unimported formal files remain subject to the same inventory checks.


## Local verification

The full Lean library builds successfully (65 jobs). The frozen-registry/source verifier passes with 1,872 local declarations and a 6,513-declaration dependency closure. All seven negative checks and fifteen Python tests pass. Viewer generation, JavaScript syntax validation and methodology-skill validation pass. The short review route is 386 lines. Chromium CI checks the actual rendered code, glosses, partial/theorem status and open completion entry before deployment; its result is separate evidence from these local checks.

The completeness gate still rejects this draft, including the newly recorded bound question. Accepted extraction and formalization review counts remain zero; package refinement remains absent.
