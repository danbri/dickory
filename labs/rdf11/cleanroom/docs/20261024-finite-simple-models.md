# Bounded simple countermodels and pre-interpretations

24 October 2026. Seventeenth working increment. Appendix B's simple N+B+1 bound and bounded-model equivalences are now proved in the existing abstract-name semantics. Datatype/RDF/RDFS finite-model claims and effective decision procedures remain open.

## Source scope

[Informative Appendix B](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#finite_interpretations) sketches restriction to the names used in G and E, the N+B+1 resource bound, completion to full interpretations, and equivalent satisfiability and entailment. The preceding increment proved name-domain locality. This increment proves the separate domain bound and connects the two constructions.

The existing `MT11-FINITE-SIMPLE-PREINTERPRETATION` mapping is upgraded from partial theorem to theorem, with extraction and formalization review still pending. Its source paragraph remains `#finite-interpretations-informative > p:nth-of-type(3)`; p2 states that the appendix is an unproved sketch. An AI reading pass assessed the preservation directions and active-domain treatment against that paragraph and normative §5. It is not expert acceptance.

`MT11-PREINTERPRETATION` remains a partial definition mapping because our precise refinement retains §5's IS into IR union IP and partial IL, while Appendix B loosely describes mapping into IR. The new theorem is explicitly relative to that refinement and the existing abstract IRI/literal domains.

## Construction and bound

Start with a model I satisfying G and one satisfying assignment whose domain is exactly the occurring blanks of G. Let v enumerate the exact union of the names of G and E, and b enumerate their union of occurring blank identities. Both enumerations have exact membership and no duplicates. A literal contributes its literal name and datatype IRI to v; a blank shared between the graphs is counted once in b.

Retain one existing resource, every defined name value in v, and assignment values for the blanks in b. Undefined literal values and undefined assignment entries contribute nothing. The list has at most N+B+1 entries. Removing repeated denotations gives a set with at most that many objects; no unique-name assumption is used.

`DomainRestriction.interpretation` intersects both IR and IP with that set and restricts IEXT accordingly. It preserves all comparison-name values and partiality of IL. Property-only denotations remain outside IR. The selected set consists entirely of objects already in IR or IP, so it is exactly the new active domain. `BoundedDomain` witnesses its duplicate-free enumeration and upper bound; `BoundedDomain.resources` derives the required bound on IR by subset enumeration.

Ambient Lean U is a representation carrier, not the specification's IR. It may contain unused objects. The bound covers every object that can participate in the pre-interpretation's denotations and truth conditions. Completing name domains yields a full interpretation with this same bounded active domain; its globally defined name-mapping structure is still not finite.

## Preservation directions

The restriction preserves term denotation and triple/whole-graph truth for every restricted assignment lifted into the original model. Consequently any conclusion satisfied in the restriction is satisfied in the original. The retained premise assignment can be lowered into the restriction, so G remains true. If E was false originally, it remains false after restriction. These arguments preserve shared-blank correlations within each graph without requiring the independent G/E satisfaction witnesses to agree.

This is not a claim that compression preserves every originally true graph or positive witness. Exact truth preservation for every assignment over the comparison vocabulary belongs to the subsequent name-completion construction, whose IR, IP and IEXT remain fixed.

`finite_simple_countermodel` supplies the exact comparison enumerations and a bounded countermodel for finite graphs whenever simple entailment fails. The more general `bounded_simple_countermodel` permits any enumerated vocabulary covering both graphs and any enumerated blank set covering the premise. `simple_entailment_iff_bounded_preinterpretations` and `simple_satisfiable_iff_bounded_preinterpretations` state the source-facing equivalences with exact union counts. These quantify over the same transcribed simple semantics, including generalized syntax, without adding IP-subset-IR or total-IL assumptions.

The new one-line `Statements.finite_simple_countermodel_bound` alias retains all hypotheses. The short Statements/Syntax/Simple reviewer route is 379 lines.

## Remaining boundaries

These are semantic existence and equivalence proofs using classical choice, not an executable finite search or a complexity theorem. Restriction is not asserted to preserve D-, RDF- or RDFS-model conditions. The separate datatype bound and weakened datatype/RDF/RDFS pre-interpretations remain unproved. Concrete IRI/literal syntax, specified built-in datatype meanings, expert reviews and npm/WASM refinement remain external obligations.

No new source question or claim is introduced. The catalogue remains 172 mappings among 217 preliminary records, including partial mappings, with nine open questions and no accepted reviews. Completing this mathematical component does not establish complete specification coverage.

## Deliberate registry audit

The registry adds 83 declarations: 34 authored declarations and 49 generated helpers, including structure fields/constructors and private matcher equations with explicit parents. Every existing declaration retains its type and kind. Two existing generated helpers (`Set.empty.eq_1` and `SimpleInterpretation.mk.congr_simp`) acquire Preinterpretations compiler attribution after the headline file imports the new results earlier; their existing grounding is preserved.

There are 1,831 local declarations in 61 inventoried formal files and a dependency closure of 6,472 declarations. No new foundation modules or logical axioms were added. The allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`. The only changed existing formal files are the root import and headline statements; all new files and declarations are explicitly enrolled.

## Validation

The full 63-job Lean build and frozen-registry verification pass. All seven rejection checks and 15 Python tests pass, and the source catalogue and review viewer regenerate successfully. Site staging/link checks, JavaScript syntax, methodology-skill validation and whitespace checks pass. The browser suite now contains 70 configured interaction checks, including the bounded headline, active-domain/resource distinction, preservation directions and bounded-pre-interpretation equivalences. Chromium CI must pass before publication.

The complete-coverage gate continues to reject completion: unresolved source accounting, incomplete mappings and reviews, source questions and absent implementation refinement remain explicit.
