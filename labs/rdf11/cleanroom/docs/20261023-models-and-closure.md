# D-model existence and generalized closure

This fifth increment continues the source-first reconstruction from RDF 1.1 Semantics §§7.2.1, 8.1.1, Appendix A and the container discussion in Appendix D. There is no F* or Factoidal implementation lineage in these proofs. It connects the datatype/RDF/RDFS conditions to model existence, literal substitution and the specified generalized closure.

## Explicit models

`DatatypeModels.lean` constructs a D-model for every fixed external datatype theory and recognized set D. Its carrier injectively embeds external values and adds an unnamed resource. IR and IP are the whole carrier, and every property extension is full. Recognized ordinary datatype IRIs retain their fixed identities; recognized literals retain their required values or undefinedness. Unknown types can denote the unnamed resource. No default value is supplied to an ill-typed recognized literal.

This one witness proves that every graph without ill-typed literal occurrences has a D-model, without any finiteness assumption. Combined with the earlier undefined-literal theorem, it gives both exact characterizations:

- D-satisfiable if and only if no member triple contains an ill-typed literal.
- D-unsatisfiable if and only if some member triple contains an ill-typed literal.

The empty graph therefore has a D-model for every D. These are statements about simple D-semantics; the model does not satisfy the additional RDF/RDFS conditions in general. Its deliberately unrestricted relations establish existence, not universal interpretation requirements.

A further theorem takes an explicit ill-typed literal and constructs two ordinary singleton graphs for which D-entailment holds but simple entailment fails. It combines D-explosion with ground interpolation. This strengthens the evidence attached to the printed entailment-direction question, while retaining the ill-typedness assumption and making no claim of official erratum status.

## Literal substitution

`LiteralSubstitution.lean` records recognized values through the ordinary and tagged branches of the datatype theory. A simultaneous literal map may leave a literal unchanged or replace it using a proof that both recognized literals have one value. It operates in all three generalized triple positions, preserving IRIs and blank identities.

The image graph remains a set, including when triples collapse to the same image. Satisfaction is preserved in both directions under one shared assignment. The result covers overlapping datatype spaces and normalized language values, extending the previous object-only theorem. Concrete datatype equalities remain obligations of an eventual datatype library.

## The specified generalized closure

`RDFRules.lean` now proves GrdfD1, and full-family `RDFSDerives` composes it and rdfD2 with the existing RDFS rules. The named rule uses an object literal, exactly as the source table states. Its semantic helper proves the stronger any-position consequence, which is not silently substituted into the closure definition.

`EntailmentClosure.lean` follows Appendix A's printed seed: retain S; add non-container axioms; add container axioms selected by occurrence in E; and add rdf:_1 axioms if step 2 added no triples. Occurrence reuses the existing vocabulary definition, including embedded datatype IRIs. The fallback is a set-growth test relative to the seed after step 1, not merely a test that E lacks container IRIs. The named closure recognizes exactly langString and xsd:string.

The inductive saturation relation has a proved least-closure property. Selected axioms and every rule preserve truth under one assignment. Consequently, G and its closure have the same satisfaction status within the corresponding RDF/RDFS model class. A positive simple-entailment check, or an instance-subgraph check, is therefore sound. These proofs do not require consistency, finite inputs or an exhaustive executable search.

The converse completeness theorem, finite generation and a decision procedure remain unproved. A source-review question concerns the E-only container selection: full RDFS semantics proves that `s rdf:_17 o` entails `s rdfs:member o`. `ContainerEntailment.lean` proves this for every index using its full-family axiom, rdfs12 and rdfs7. The specified seed appears to omit the needed rdf:_17 axioms in this example. Closure non-derivability and an appropriate full-model consistency witness still need proofs; this is not a confirmed counterexample or declared erratum.

## Review and checks

The Statements/Syntax/Simple review route remains 359 lines. README and the repository methodology skill now distinguish exact procedure transcription from stronger semantic helpers and spell out the evidence needed before accepting a completeness counterexample.

The catalogue has 130 mapped records among 195 preliminary claims, including partial mappings. The frozen inventory has 32 formal files and 1,070 local declarations, with a closure through 5,535 declarations. The changed signatures are the five generated eliminators for the intentionally extended `RDFSDerives`; no existing authored theorem signature was changed. No new foundation modules or logical axioms were introduced.

Validation uses the full Lean build, explicit registry/dependency verification, source-range regeneration, seven negative checks, eleven Python tests and generated viewer checks. Two new tests ensure that every pending source question blocks complete-coverage certification, including newly added questions and questions with proved theorems but no accepted expert adjudication. The gate no longer hard-codes only the first generalized-instance question. Chromium CI gates Pages publication. Expert mapping reviews, concrete datatype implementations, finite/completeness proofs and package refinement remain open.
