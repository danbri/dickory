# RDFS model construction and source-facing witnesses

23 October 2026. Ninth working increment. Draft mappings; expert review pending.

The RDFS condition structure now has a proved family of inhabitants. The construction reuses the existing RDF interpretation and literal proofs, supplies the schema-property relations, and proves every existing RDFS condition and every axiomatic triple, including all positive container indices. No semantic condition was weakened to obtain a witness.

## Source and mathematical scope

The primary source is the pinned [RDF 1.1 Semantics §9](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#rdfs-interpretations): the interpretation definition, semantic condition tables and RDFS axiomatic triples. The earlier necessary language-literal coverage theorem also uses §8's exact recognized datatype extensions and §7.1's language-literal denotation condition. Source-reader AI close reading checked the new modules against these passages; this is not expert acceptance.

`RDFSModelConstruction.Parameters` states sufficient hypotheses: the literal and vocabulary langString IRIs agree; langString and string are recognized; other schema symbols are not recognized as datatypes; and each language-string value has an actual tagged-literal representative. The recognition exclusions are choices of this constructor, not namespace restrictions required by W3C.

For the base recognition set, vocabulary distinctness discharges those exclusions. With aligned names, `base_model_exists_iff_language_coverage` proves that the **current parameterized RDFS model class is inhabited exactly when the language-literal coverage condition holds**. This is not an arbitrary-graph consistency criterion or a certification of concrete XSD/BCP47 meanings.

The interpretation uses the RDF constructor's disjoint carrier of external values and fresh name-objects. Recognized datatype IRIs denote their fixed datatype identities. Datatype-object class columns retain exactly their prescribed spaces, including the special identity-indexed langString space. Name-object columns are universal. “Name-object” here means the `name` constructor branch, not every object denoted by an IRI.

IR, IP, IC and LV are universal in this witness family. This does not make all class extensions universal, and is not required of other models. The external `Value` parameter supplies values and datatype descriptors; it is not an assertion that every literal value belongs to that supplied domain. Neither LV = image(IL) nor LV = image(realization) is silently assumed.

Subclass is column inclusion. The selected subproperty relation is reflexive, points every property to member, and includes isDefinedBy to seeAlso; member and seeAlso have universal extensions. Domain and range target every name-object, whose class column is universal. The source constrains consequences of these relations, not their exact extensions, so this stronger choice satisfies the conditions. A freely supplied relation Q controls the remaining properties.

## New source-facing consequences

- §9 paragraph 4: rdfs:Class and rdfs:Resource have distinct denotations and equal class extensions in the family. The later [RDFS consequence increment](20261023-rdfs-consequences.md) supplies an unnamed empty-class witness by refining the spare resource's column.
- §9 paragraph 14: a model permits overlapping semantic roles. Further witnesses give class self-membership and property self-application. These are permitted configurations, not universal requirements on models.
- The same paragraph's class/member observation: two explicit countermodels refute transferring an rdf:value assertion from a class to an individual typed member, and the converse. They do not address properties asserted of every member, or prohibit transfer supported by additional premises.
- §9.1 paragraphs 3–5: a singleton triple with IRI subject and object rdfs:Literal is satisfiable under the constructor assumptions. This is the note's consistency consequence. The mapping remains partial: no general theorem excluding literal syntax objects from LV, or equating LV with denotation images, has been supplied.

`rdf:value` was chosen as an example property for the countermodels. Semantics §8 asserts its rdf:Property type; §9 asserts Resource domain and range. Those axioms are proved by the same model witness. No special value evaluation or extraction is added. [Schema §5.4.3](https://www.w3.org/TR/rdf-schema/#ch_value) explains the structured-value idiom and explicitly gives it no meaning on its own. This supplementary explanation is not a new hash-pinned source claim in the catalogue.

## Review route and audit

Read `RDFSModelRelations.lean`, `RDFSModels.lean`, and `RDFSModelExamples.lean` in that order, following imports for the existing datatype/RDF interfaces. The short headline route `Statements.lean`, `Syntax.lean`, `Simple.lean` remains unchanged and under 400 lines; it remains an entry point to simple semantics, not a complete RDFS proof audit.

The catalogue has 147 mappings among 205 preliminary records, including partial mappings. One new derived record covers the construction; two existing records gain partial theorem mappings. Existing interpretation, class-structure and language-coverage records now link to the witnesses. Source selectors locate AI-selected paragraphs; whole-element highlighting does not certify extraction of every assertion.

There are 42 new curated English glosses, 62 new registered local declarations and three new formal files. Twenty of the declarations are structure projections, constructors, recursors or generated equation/simplification helpers. Six helpers for existing definitions were first generated while compiling the new modules; their actual compiler module attribution is preserved. Existing declaration signatures are unchanged. The registry now contains 1,440 declarations in 44 files; the dependency closure contains 5,954 declarations. No foundation module or logical axiom was added. The audited axioms remain propext, Classical.choice and Quot.sound.

Local validation passed: the full Lean build, exported closure and frozen registry; source hashes and regenerated catalogue; all seven negative gates (including rejection of complete coverage); all 14 Python presentation tests; English gloss coverage and viewer generation; site-link checks; browser-script syntax; and methodology-skill validation. The browser suite now contains 34 checks, adding the RDFS conditions, coverage equivalence, countermodel scope, literal-value consistency and coextensive-class witness. Browser execution and Pages publication are checked separately in CI.

## Remaining obligations

Concrete IRI/literal syntax and equality, actual language-literal coverage, and correspondence to prescribed datatype libraries remain open. So do general RDF/RDFS compatibility and arbitrary-graph consistency, full rule completeness and finite procedures, the recorded Appendix A container-selection question, generalized interpolation scope, lean/proper-instance consequences, exact Skolem lifting, additional informative consequences, and dataset-extension admissibility.

Expert review, finer context grounding, a Lean grounding-certificate proof, and executable links to the pinned W3C tests remain outstanding. No npm/JS/WASM implementation path is refined by this construction. Model existence helps prevent vacuous proofs over an empty model class; preventing package defects additionally requires certified representations and refinement across ingestion, storage and wrappers.
