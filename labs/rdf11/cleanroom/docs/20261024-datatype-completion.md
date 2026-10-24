# Datatype completion, ordinary entailment and generalized scope

24 October 2026, nineteenth increment. The preceding weakened-model construction now has a full datatype completion and an exact bounded entailment theorem for ordinary conclusions. A checked abstract witness explains why the ordinary-conclusion hypothesis cannot simply be erased. Source fidelity and expert adjudication remain pending.

## Full interpretation construction

`DatatypeCompletion.lean` extends a local interpretation P over V into a full interpretation over the ambient IRI and literal domains. The carrier becomes `Sum U Value`. An already realized datatype value keeps its embedded old object; a previously unrealized value gets its own tagged representative. `ValueRealization.embed_injective` and `complete` preserve distinct fixed values while making realization total.

Every local IRI and literal retains its old optional denotation under this embedding. Absent recognized datatype IRIs receive their fixed identities. Recognized literals are evaluated globally, including normalized language pairs and undefined ill-typed literals. Absent unrecognized literals remain undefined. `DatatypeCompletion.conditions` checks all original §7 conditions against the completed realization.

The constructor chooses universal IR and IP in the larger carrier. That is a witness choice, not a requirement on all models. Its property extensions contain exactly embedded old relation edges, with the original property and endpoint evidence. Giving additional objects resource/property roles does not itself create relation edges.

## Assignment truth and existential graph satisfaction

`tripleTrue_lift_iff` preserves every generalized triple under an embedded old blank assignment. `graphTrue_lift_iff` uses one shared assignment across the entire graph, preserving correlations. Consequently every locally satisfied generalized graph remains satisfied after completion.

For the reverse direction, lower a completed assignment by keeping only embedded old resources. Every blank in an ordinary triple occurs as a subject or object; a true completed edge forces those endpoints to be old resources. The predicate is a fixed IRI. Thus one lowered assignment works for every member of an ordinary graph, proving `ordinary_satisfies_iff` in both directions.

This distinction is essential: preserving old assignments' truth does not exclude new satisfying assignments in a larger IR. A generalized predicate blank can use an object that was formerly only a property.

`OrdinaryPreinterpretations.lean` preserves ordinary syntax during vocabulary restriction and proves that restriction commutes with generalization. The resulting `d_entailment_iff_bounded_preinterpretations_ordinary` combines full completion with the previous finite compression proof:

- The premise G may be generalized; the conclusion E is an ordinary `Graph`.
- V covers both vocabularies, including literal datatype IRIs. S covers the premise's occurring blanks. The graph witnesses remain independent.
- Full D-entailment holds exactly when every localized D-pre-model with at most N+B+1 active objects preserves premise-to-conclusion satisfaction.
- The bound counts IR union IP. D may be an arbitrary recognized-IRI set; this result does not enumerate it or implement a decision procedure.

Exact comparison-union enumerations from finite inputs instantiate these covers. `Statements.datatype_preinterpretation_ordinary_entailment` is a one-line alias retaining the complete type and source anchor. The Statements/Syntax/Simple entry route remains 393 lines. The N+B+1 bound remains separate from the printed multiplicative formula and its existing empty-comparison question.

## Checked obstruction for generalized comparison preservation

`DatatypeCompletionScope.lean` uses four abstract IRI symbols and one abstract literal. In a schematic reading, the graphs are:

```text
G: s p s .
E: s _:b s .
```

The shared vocabulary is proved to contain exactly s and p. Both p and another IRI d identify recognized custom datatypes. The ambient literal has lexical form "" and datatype d, and its value is the fixed datatype object identified by p. The literal and d are absent from the comparison vocabulary. Both recognized datatype value spaces are proved nonempty; this example does not rely on an empty datatype.

The local model has IR={false}, IP={true}, IS(s)=false and IS(p)=true, with the sole possible property edge present. It satisfies all current localized datatype conditions and has an exact two-element active-domain enumeration. It satisfies G but cannot satisfy E: its blank assignments can use only false, while its only property is true.

In every full D-model of this abstract theory, global literal evaluation places the fixed datatype object identified by p in IR. The existing edge for G then supplies the predicate-blank witness for E. `full_entailment` proves this, and `full_premise_satisfiable` proves that the entailment is not vacuous through an inconsistent premise. `no_comparison_preserving_completion` excludes any full D-model, on any carrier at the selected universe, preserving both local satisfaction values.

The datatype's value space and its binary property extension IEXT are different structures; the argument does not identify them. The source-reading subagent used AI close reading of Concepts §5 and Semantics §§4,5,7 and Appendix B. It found no explicit nonemptiness requirement for datatype spaces, no prohibition on one custom datatype object being another datatype's value, and no D-only prohibition on using a recognized datatype IRI as a predicate. The strengthened witness makes both recognized spaces nonempty anyway. These observations support review; they are not expert acceptance.

The close reading locates this material in Concepts `#section-Datatypes > p:nth-of-type(1)`–`(4)` and `#datatype-iris > p:nth-of-type(1)`; Semantics `#notation-and-terminology > p:nth-of-type(1)`, `#simple-interpretations > table:nth-of-type(1)` and `p:nth-of-type(12)`, `#literals-and-datatypes > p:nth-of-type(5)`–`(6)`, `#D_interpretations > table:nth-of-type(1)`, and Appendix B `p:nth-of-type(3)`–`(4)` within `#finite-interpretations-informative`. The chosen recognition set concerns D-model mathematics; it is not a processor-conformance claim about required built-ins. RDF/RDFS add property constraints and require their own scope analysis.

## Fidelity boundaries and the source question

`Q-DATATYPE-COMPLETION-GENERALIZED-SCOPE` records the checked failure for the present localized conditions. It is not a declared source erratum or a theorem refuting every possible refinement of Appendix B.

Two boundaries stay explicit. First, the witness has abstract finite name domains, not a proved implementation of the complete concrete RDF name domains. Second, the pre-interpretation definition follows normative §5's IS codomain IR union IP, whereas Appendix B loosely says V maps into IR. The latter reading would itself exclude the displayed property-only referent. Its consistency with the preceding normative semantics needs an explicit review decision.

The full completion still preserves truth for every embedded old assignment, including generalized triples. The failure concerns additional existential witnesses and the wider claim of unchanged generalized entailments. No definition is silently changed to force that wider result. Ordinary entailment has its own proved, qualified mapping; generalized coverage remains partial.

## Review and remaining work

There are 221 preliminary claim records, 177 mappings including partial mappings, eleven source questions and no accepted expert reviews. The existing completion entry moves from unmapped to partial theorem; the bounded ordinary-entailment result has a separate derived theorem entry. The original source bytes and the previous zero-bound question are unchanged.

Remaining work includes expert disposition of the pre-interpretation scopes, the printed datatype bound, RDF/RDFS finite-model completion, concrete name and datatype correspondence, rule completeness, other source obligations, and all product refinement. An optional stronger local resource-compatibility condition would be a new explicit refinement requiring its own proof and review, not an automatic correction to the current conditions.


## Deliberate registry audit

The inventory adds 155 declarations: 58 authored declarations with curated glosses and 97 generated constructors, projections, instances, recursors, equations and matcher helpers. Every generated helper has an explicit parent, including the derived equality instance and private matcher equations. Existing declaration types and kinds remain unchanged. One existing generated equation, `SimpleInterpretation.Relates.eq_1`, moves compiler attribution from RDFModels to DatatypeCompletion after the earlier headline import; its prior grounding is preserved.

There are 2,027 local declarations in 66 inventoried formal files and a dependency closure of 6,684 declarations. No new foundation modules or axioms were added. The allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`. Only the root import, headline file and regenerated source-range snapshot change among previously inventoried formal files; three new source modules are deliberately enrolled.

## Local validation

The pinned Lean build passes all 68 jobs. `tools/verify.py` passes the registry and mapping checks; all seven rejection checks and fifteen Python tests pass. Viewer generation succeeds with actual Lean bodies and curated glosses, and the site staging checks resolve all local links. The repository skill validates and the browser script passes its JavaScript syntax check. These are local results; Chromium interaction and deployment evidence are recorded by the publication workflow for the resulting commit.

Earlier countermodel glosses now explicitly distinguish the unrestricted generalized case from the new ordinary-conclusion converse. The zero-bound question remains open without retaining the outdated suggestion that no datatype completion has been proved.
