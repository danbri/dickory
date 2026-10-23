# Reification and container countermodels

23 October 2026. Tenth working increment. Draft mappings; expert review pending.

The new RDFS witness family now supports connected proofs for informative Appendix D.1 and D.2. All countermodels reuse the existing RDFS conditions and complete axiom family. A shared `FreeProperty` calculation exposes Q for properties outside the constructor's fixed schema dispatch; the earlier class/member rdf:value proof now reuses it too.

## What is proved

`Triple.reification` builds the four ordinary RDF triples describing type and components. It does not identify a resource with a concrete triple token, document or quoted syntax object. The IRI-component truth proof is reused in both reification countermodels and the metadata example.

`reification_not_assertion` gives a model of a reification in which its described rdf:value assertion is false. `assertion_not_existential_reification` gives the converse separation: the assertion is true but rdf:subject has an empty extension, so no existential root can satisfy the complete reification. These are counterexample families to general inference patterns, not a theorem that every possible triple fails the entailments. Axiomatic triples, overlaps and additional premises require separate treatment.

`same_components_not_metadata` gives two distinct IRI-named resources describing identical components, with metadata on only one. The denotations are distinct in the witness; no unique-name assumption is added to the interpretation definitions.

For containers, `bag_permutation_not_entailed` preserves the printed conclusion with only two membership edges and no added Bag typing. The selected first and second values are distinct, and no existential root can witness the swapped order. `second_position_not_entailed` gives a Seq with positions 1 and 3 while every position-2 edge is false; neither conclusion blank can evade that empty relation, even if the blanks co-denote. `bag_and_sequence_consistent` permits both types on one resource. `no_container_member_property_transfer` refutes metadata transfer in both directions between a Bag and one identified member.

All countermodels retain `RDFSModelConstruction.Parameters`. Endpoints are chosen unrecognized designated vocabulary IRIs through `SchemaSymbol`, not arbitrary concrete ex: IRIs. They witness the source graph shapes without claiming full concrete-name correspondence. The example predicate rdf:value still has its ordinary specification axioms and no invented evaluation behavior. RDFS countermodels also refute weaker RDF/simple entailments through the already proved regime inclusions.

## A printed blank-node conclusion requires review

Appendix D.1 paragraphs 11–14 first discuss two reification resources with matching components. The printed premise contains two reifications with blank roots xxx and yyy and a property assertion on xxx. The printed singleton conclusion is the same property/object assertion on yyy, preceded by a non-entailment connective.

Under independently existential graph satisfaction, the conclusion can use xxx's property witness. `ReificationScopeReview.printedPremise` transcribes the nine ordinary premise triples, and `printed_conclusion_follows` proves their positive simple entailment of the printed singleton conclusion. The underlying `blank_property_consequence` works across arbitrary blank types and needs no datatype or RDFS constructor assumptions.

This is recorded as **Q-REIFICATION-BLANK-CONCLUSION**, pending expert adjudication. The archived source is unchanged. The intended no-transfer statement for distinct fixed resources has a separate countermodel; it is not substituted for a proof of the printed existential non-entailment. No specification erratum is declared.

The source locator gained an optional exact-text selector so the short connective paragraph can be selected without also selecting longer paragraphs containing the same words. A test checks ambiguous substring rejection and exact source slicing. This is only passage location; AI close reading selected and assessed the claims.

## Review and audit

Read `RDFSFreeProperties.lean`, `Reification.lean`, `ReificationExamples.lean`, and `ContainerExamples.lean`. The existing short entry route through Statements, Syntax and Simple remains 359 lines. AI source review checked the four modules against the selected Appendix D passages and found no source-fidelity blocker; it does not constitute accepted expert review.

New selectors bind Appendix D.1 paragraphs 3, 5–6 and 10–14 and D.2 paragraphs 5–6, 8, 10–12 and 14–15. Indexicals in the reification definition and non-entailment explanation have explicit antecedents. Whole-element highlighting still does not establish that every assertion in a passage has been extracted.

There are 154 mappings among 206 preliminary records, including partial mappings and a separately labelled derived positive-entailment record. Six existing records gain partial mappings. All expert reviews remain pending. Container open structure covers only the gap and overlapping-type consequences: infinite membership, fixed bounds and arbitrary membership-addition claims remain open.

The deliberately reviewed registry adds 30 local declarations in four new formal files. Twenty-one authored declarations have curated English glosses; nine generated helpers have explicitly labelled explanations. The FreeProperty equation is generated in the older examples module, and the reification equation and Subject.toTerm case helpers are generated in ReificationExamples; actual compiler attribution is preserved. Existing signatures are unchanged. The registry contains 1,470 declarations in 48 files, with a closure through 5,984 declarations. No new foundation modules, logical axioms, proof placeholders or unsafe declarations were introduced.

## Remaining scope

These proofs do not certify concrete literal/IRI domains, prescribed datatype libraries, arbitrary-graph consistency, rule completeness or finite procedures. Concrete token identification and the complete not-quotation discussion remain unformalized. Dataset semantic-extension obligations, other informative assertions, context grounding, expert review, Lean grounding certificates and executable links to W3C tests remain outstanding. No npm/JS/WASM artifact refinement is established.

## Validation status at commit

Local checks passed: full Lean build and registry/closure audit, source regeneration and hashes, seven negative gates, all 15 Python tests, source/gloss viewer generation, site links, JavaScript syntax, methodology-skill validation and whitespace checks. The browser suite now contains 39 checks. Chromium execution and Pages deployment for this increment are separate CI obligations; no local browser pass is claimed.

The preceding RDFS-model increment, 3491149, passed all 34 browser checks in run 40021731043 and deployed successfully. Its public build revision and viewer SHA-256 were checked against the downloaded artifact before this increment was committed.
