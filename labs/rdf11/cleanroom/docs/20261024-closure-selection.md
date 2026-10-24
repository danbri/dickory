# Appendix A: container-axiom selection obstruction

24 October 2026, twenty-first increment. The printed closure procedure is retained. The formal transcription now has a checked example satisfying all three relevant obligations: full RDFS entailment, failure of the selected-closure test, and full RDFS consistency of the premise. This is evidence for the open source question Q-CLOSURE-CONTAINER-SELECTION, not an official erratum or accepted source-fidelity review.

## Source and example

The previously requested source-reading subagent used AI close reading of Appendix A and independently re-read the new proof definitions against the procedure and all rule constructors. It found no qualification requiring S's container names to occur in E, extra container typing in S, or a Bag/Seq/Alt type for the subject. The source inputs are ordinary RDF graphs; the example satisfies that condition.

The input scope and closure definition are `#entailment-rules-informative > p:nth-of-type(15)` and `#dfn-generalized-rdf-rdfs-closure`. Paragraph 16 contains the four-step procedure, paragraph 18 the consistency-qualified completeness claim, and paragraph 20 the tautology claim. Appendix A is informative. The full semantic entailment uses `#RDFS_axiomatic_triples`, `#dfn-rdfs12` and `#dfn-rdfs7`.

```turtle
# S
s rdf:_17 o .

# E
s rdfs:member o .
```

Both graphs are ordinary ground singletons, with no literal or blank node. Their two example IRI names are syntactically distinct; no unique-name assumption about their denotations is made. In the existing vocabulary representation, `container 16` denotes the symbol for rdf:_17 and `container 0` the symbol for rdf:_1.

Step 2 selects container axioms using E. E mentions no indexed container IRI, so it selects none and the fallback supplies only rdf:_1 container axioms. This example therefore does not depend on the possible distinction between “step 2 selects nothing” and “step 2 adds no new triple.” The existing set-growth reading of the fallback remains unchanged.

Full RDFS semantics has the rdf:_17 ContainerMembershipProperty axiom. rdfs12 makes rdf:_17 a subproperty of rdfs:member, and rdfs7 derives E from S. `ClosureSelection.full_entailment` reuses the existing general `container_membership_entailment` proof.

## Absence is proved for every derivation

`ClosureSelectionFrame.lean` defines a finite relation on syntactic tags. `ClosureSelectionScope.lean` maps names and terms to those tags and defines `Supported`. This relation is an overapproximation of the selected closure, not an RDFS interpretation or a semantic countermodel.

The proof shows that S, every selected non-container axiom and every rdf:_1 fallback axiom are supported. Every RDF axiom is supported, including ordinary property typing of indexed names. The only exceptional RDFS axioms are the ContainerMembershipProperty typings whose selection matters here. Syntax-name injectivity prevents an rdf:_1 axiom from secretly supplying rdf:_17's typing.

The invariant survives GrdfD1, rdfD2 and every rdfs1–rdfs13 rule, including both rdfs4 cases. There is no supported literal premise for GrdfD1. The selected rdf:_1-to-member subproperty edge is permitted, but no supported assertion uses rdf:_1 as predicate. The rdf:_17 assertion cannot acquire that selected tag. Induction through `ruleDerives_least` covers arbitrary derivations; no finite search bound or executable saturation assumption is used.

The conclusion is unsupported, so `conclusion_absent` excludes it from the closure. `closure_not_simply_entails` uses the existing ground-entailment/subgraph equivalence. `closure_has_no_conclusion_instance` separately states the printed instance-test failure for every blank substitution: ground E cannot change under substitution.

## Full-model consistency and datatype boundaries

`premise_consistent` uses the existing full RDFS model construction with its free-property relation set to True. That model satisfies every RDF/RDFS condition and all container axioms. It is separate from the deliberately weaker syntactic invariant. Thus the semantic entailment is not merely an artifact of an inconsistent premise.

The theorem states the constructor's sufficient datatype hypotheses explicitly. `ClosureSelectionWitness.lean` then constructs a family inhabiting those hypotheses. It has typed literals for every non-langString IRI and tagged literals carrying validity evidence, a string-value branch, a normalized language-pair branch, and fixed datatype descriptors. Every permitted language value has an actual literal representative.

The AI source pass caught a needed lexical boundary: `#D_interpretations > p:nth-of-type(3)` excludes xsd:string lexical forms containing code points outside XML10's Char production. The witness therefore parameterizes `stringLexical` rather than hardwiring all Lean strings as valid xsd:string forms. Language-tag validity and its closure under ASCII lowercase are also explicit. The generic entailment and absence proofs do not depend on these meanings.

`selection_counterexample` combines full consistency, full RDFS entailment and closure non-entailment for the **same** theory, vocabulary and pair of graphs. `witness_parameters_inhabited` additionally exhibits an abstract all-strings/all-tags inhabitant, solely to rule out empty constructor hypotheses. It is not claimed to implement XML10 or BCP47. Concrete IRI spelling/global-name correspondence and concrete datatype validation remain external obligations.

## Catalogue and methodology

The existing closure and completeness mappings now expose the actual Lean bodies and curated English glosses. The completeness mapping remains partial: soundness is proved, while its converse conflicts with the current selection transcription. The open question includes the example, invariant, full-model evidence, remaining boundaries and a request for expert adjudication. No archived source bytes, axiom-selection definitions or rule premises were changed.

There remain 179 mappings among 221 preliminary records and eleven source questions. These counts are not coverage percentages. All expert reviews remain pending and package refinement remains absent. The short Statements/Syntax/Simple route remains unchanged at 393 lines; the supporting proof is available through the relevant mapped claims.

Any proposed repair, including selecting container axioms from S as well as E, must receive its own definition, correctness obligations and explicit correction/baseline record. It must not overwrite the archived procedure or inherit a completeness badge from these results.


## Deliberate registry audit

The increment adds 222 local declarations: 59 authored declarations with curated English glosses, and 163 compiler-generated constructors, eliminators, pattern equations, decision helpers and simplifier support declarations with explicit parents. All prior declarations retain their type, kind and module attribution. The only previously inventoried formal file changed is the root import. Three formal modules are deliberately enrolled; the source-range snapshot and archived documents are unchanged.

The registry now contains 2,342 local declarations across 72 formal files and a dependency closure of 7,003 declarations. No new foundation module or axiom is admitted; propext, Classical.choice and Quot.sound remain the only allowed logical axioms.

## Local validation

The pinned Lean build passes all 74 jobs. The formal registry/source verifier passes, all eight rejection checks pass, and all fifteen Python tests pass. The viewer generator resolves every required declaration to actual code and English glosses, the site builder passes local-link checks, the updated browser script passes JavaScript syntax checking, and the methodology skill validates.

Local Chromium execution was unavailable because this checkout has no installed Playwright package. The publication workflow installs its pinned browser dependencies and must pass the full interaction checks, including the five new closure-review checks, before Pages deployment. A Git fetch could not resolve github.com in the local sandbox; the connected GitHub API independently confirmed remote main at the unchanged parent commit before publication.
