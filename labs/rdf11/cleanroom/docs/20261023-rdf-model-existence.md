# Constructing RDF models and repairing datatype fidelity

The earlier `RDFConditions` and `RDFSConditions` structures transcribed semantic constraints. A structure defining a class of interpretations does not prove that any interpretation satisfies those constraints. This increment constructs a family of RDF models, corrects a missing prose requirement in the earlier datatype encoding, and derives two parameter-compatibility obligations. It does not claim general RDF/RDFS satisfiability or full formalization.

## Source reading and provenance

A follow-up AI close reading checked Semantics §7–9 and informative Appendix B. HTML parsing located the selected passages in the existing hash-pinned archive; text search did not extract their meaning. The source's claim that only ill-typed literals cause unsatisfiability applies to **simple D** interpretations. RDF adds exact datatype class extensions, and RDFS adds further conditions. Neither section promises that arbitrary supplied datatype parameters admit a model.

The new derived records are grounded in the definition at `#rdf-interpretations`, the D-interpretation conditions, `#rdfsemcond1`, `#rdfsemcond3`, `#RDF_axiomatic_triples`, and the langString image clause in `#rdfssemcond1`. They are marked **derived**, not attributed to the source as separately named theorems. The additional partial mapping of `MT11-RDF-VOCABULARY-LIMITS` links the paragraph about unspecified meanings and retains the separate optional-recognition paragraph.

## Correcting the langString omission

A second close-reading pass found that the earlier table-only datatype encoding was too permissive. Normative §7 prose fixes recognized datatype identification and explicitly treats langString as denoting its exceptional datatype; Concepts §5.4 says recognized datatype IRIs have fixed referents. The special §7.1 table row governs tagged-literal evaluation. It does not remove the surrounding denotation obligation.

`DConditions.language_denotation` now requires the recognized langString IRI to denote `T.identified langString` through the existing value realization. Both the simple D-model and the RDF model map every recognized IRI to its fixed datatype. The previous model-family draft that used a separate unconstrained langString name has been replaced before publication. The correction is a formalization repair, not a claimed specification erratum or merely an unresolved source question.

The actual datatype space is now selected by **datatype identity**, so aliases share both denotation and value space. The language datatype has the normalized pair space. Its absent L2V is encoded as an everywhere-undefined partial evaluator, which does not make its actual value space empty. Every other datatype uses its L2V range.

`recognized_datatype_aliases` and `recognizedSpace_identified_eq` prove alias coherence. `language_alias_illTyped` records a derived edge case: an ordinary literal with a recognized noncanonical alias of langString has no L2V value. Canonical tagged literals still have no ill-typed instances. Concepts permits language tags only with the canonical IRI, and §7.1 sends other IRIs through the ordinary evaluation branch. This edge-case reading is explicitly marked derived and still needs expert mapping review.

The new `MT11-LANGSTRING-DENOTATION` record is explicit prose; `MT11-DATATYPE-ALIAS-COHERENCE` is derived. Both are linked to the fixed-referent and alias passages in Concepts as well as the Semantics prose. This distinction matters: an assertion need not have a named rule code or a table row to bind the formalization.

## The RDF model family

[`RDFModels.lean`](../RDF11/RDFModels.lean) uses a universe containing every external value, one separate name object per supplied IRI, and a spare resource. Both IR and IP are this entire universe. This is a permissible model choice, not a universal RDF requirement. The interpretation covers every supplied IRI and literal, including unused names.

Every recognized datatype IRI, including langString, denotes its externally identified value. Literal denotations are transported from the existing D-model construction; the datatype proof is reused. The rdf:type relation has exact recognized datatype columns, while the other property extensions are an arbitrary supplied relation R. Every RDF axiom is checked, including all positive container indices.

The sufficient constructor assumptions are:

- The literal and vocabulary interfaces agree on the langString IRI.
- D recognizes rdf:langString and xsd:string.
- D does not recognize rdf:type, rdf:Property or rdf:List.

The three exclusions are **construction assumptions**, not namespace restrictions in the specification or necessary consistency conditions. `base_parameters` proves that the base recognition set meets them by vocabulary distinctness. `base_empty_satisfiable` then exhibits a carrier and an RDF model of the empty graph. Datatype aliases remain allowed: distinct IRIs may identify one datatype; neither datatype identification nor lexical-to-value mapping is assumed injective.

`non_type_triple_independent` constructs two RDF models for the same parameters, one satisfying and one falsifying a chosen all-IRI triple whose predicate is unrecognized and differs from rdf:type. This proves satisfiability and non-entailment from the empty graph. It is a partial vocabulary-independence result with explicit hypotheses, not a complete account of RDF entailment or an RDFS countermodel.

## Two compatibility obligations

If D recognizes rdf:Property with an empty value space, no RDF model exists. The required axiom `rdf:type rdf:type rdf:Property` places the denotation of rdf:type in that space. The new proof derives this contradiction from the existing axiom and datatype-extension condition; every graph is then RDF-unsatisfiable for those parameters. The result transfers to RDFS through the existing model-class inclusion. This is an incompatible external-parameter scenario, not an assertion about the prescribed standard datatype meanings.

[`RDFSModelConstraints.lean`](../RDF11/RDFSModelConstraints.lean) proves a second necessary condition: every permitted language-string value must be represented by an actual tagged literal. RDF requires the full recognized value space; RDFS says the langString extension is exactly the image of actual tagged literals. Injectivity of value realization forces the representing literal to have the same normalized language value. Omitting a representative makes the RDFS model class empty. The present `LiteralSyntax` fields do not guarantee this coverage. A future full-domain literal binding must establish it; an RDFS model constructor cannot silently assume it away.

## Review boundaries and next work

The external theory still needs the prescribed xsd:string and langString meanings, concrete legal IRI/literal domains, and lexical identity. Arbitrary inhabitants of `DatatypeTheory` are not automatically implementations of those prescribed meanings. The langString referent omission has been corrected. Concrete built-in meanings and full lexical-domain coverage remain external obligations.

This increment establishes an RDF model family and exposes conditions needed for RDFS. It supplies neither an arbitrary-graph RDF consistency criterion nor an RDFS model construction, finite-model bound, complete rule procedure, or npm/WASM refinement. Expert extraction and formalization reviews remain pending. The existing 359-line headline review route is unchanged.

The next model-construction work must provide the actual language-literal coverage, keep prescribed datatype meanings compatible with the reserved vocabulary, and satisfy all RDFS domain/range/hierarchy conditions. Merely adding an assumed `RDFSConditions` field would not close that obligation.


## Registry audit

Compared with the previous published commit, the reviewed update adds two modules and 61 local declarations, changes 16 existing generated constructor/recursor/equation signatures, and repairs the bodies of the datatype definitions and witnesses. There are 1,378 local declarations in 41 formal files, with a closure through 5,892 declarations. All authored declarations have curated English explanations; fields and generated helpers have explicitly labelled explanations.

The only newly reached foundation module is the standard-library `Init.Data.ULift`, supplying five equality-decision declarations with empty axiom closures. Allowed logical axioms remain `propext`, `Classical.choice` and `Quot.sound`. No local axiom, unsafe declaration or proof placeholder is introduced.

There are 144 draft mappings among 204 preliminary records, including partial mappings and explicitly labelled derived records. These counts are not compliance percentages. No expert review is marked accepted.

The complete local Lean build and frozen registry audit pass, along with all seven rejection checks, eleven Python tests, source-viewer/gloss generation, skill validation, JavaScript syntax checking and the local site-link check. The complete-coverage gate still rejects this draft. Chromium CI checks the new model hypotheses, denotation repair, alias coherence and compatibility proofs in the review interface before publication.

## Review presentation correction

Inspection of the new denotation field found that Lean's projection metadata selected only `language_denotation`, hiding the actual condition in the code block. The viewer now expands name-only field ranges to the containing structure's compiler-located range, labels that context, and preserves the original identifier range in the generated evidence. It requires matching source files and containment of the original range, so unrelated source cannot be borrowed. Three new tests cover expansion, preservation of complete field excerpts, and rejection of wrong-file/out-of-range context; all 14 Python tests pass. This changes trusted presentation code, not the Lean proofs or frozen formal declarations.
