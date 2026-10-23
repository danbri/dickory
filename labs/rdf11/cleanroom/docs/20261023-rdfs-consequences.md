# RDFS valid typings and an empty-class witness

23 October 2026. Fifteenth working increment. The source's additional conclusions are derived from the existing axioms, while a refined interpretation supplies an empty-class witness.

## Source distinctions

Normative §9 paragraph 13 introduces the additional-valid-triples table and explicitly says the list is incomplete. The table lists 14 class typings and nine property typings. Its entries are claimed consequences, not another axiom family. Incompleteness concerns the enumeration of valid triples; it does not weaken the claimed validity of each listed entry.

The twelve core class entries and all nine property entries are now proved. XMLLiteral and HTML have class-typing proofs when recognized in D. The printed table omits that premise; `Q-OPTIONAL-DATATYPE-CLASSES` remains open, with no countermodel or declared erratum. Generic recognized-datatype typing does not silently discharge those unqualified entries.

Paragraph 4 contains different kinds of claim: an empty class extension is permitted, distinct classes can be coextensive, and rdfs:Class belongs to its own extension. The last is a universal consequence, not just a permitted configuration. Empty-extension permission is split out as `MT11-RDFS-EMPTY-CLASS-PERMITTED`; the original class-structure record delegates that clause.

AI close reading selected and checked these assertions and their scope. The source locator binds their unchanged archived passages. This remains AI working evidence, not accepted expert review. The paragraph highlight includes adjacent claims; it is not a claim that every highlighted character states the empty-extension assertion.

## Connected derivations

`RDFSConsequences.lean` keeps the source order of the twelve core class names and all nine property names. The two optional datatype names are expressly excluded from the core list and handled by the conditional recognition theorem. Domain/range and hierarchy axioms produce the class typings; the ContainerMembershipProperty conclusion uses one member of the already formalized infinite container family. Property typings follow through the domain of rdfs:domain.

Shared `RDFSDerives.domain`, `range` and `subclass` helpers apply the existing rules to already derived premises. The collection-typing proofs now reuse these helpers too. The semantic entailment theorems use the existing shared-assignment derivation soundness proof. The new lists are not assumed as axioms, and no rule-completeness claim is added.

The class and property conclusion graphs are RDFS-entailed by any premise graph, including the empty graph. The class result covers twelve entries; the property result covers every entry in the printed nine-entry family. Neither graph enumerates all valid RDFS typings.

`SimpleInterpretation.rdfs_class_self_membership` holds in every RDFS model. `rdfs_resource_nonempty` uses the nonempty universe and the Resource extension condition. These provide explicit guards against reading empty-class permission as permission for every particular class to be empty.

## A model with an empty class

The existing carrier has embedded external values, separate IRI name-objects and an extra unnamed resource. Its type-extension function now gives the unnamed object an empty column. Named columns remain universal, and datatype-object columns retain their exact identity-indexed spaces. The RDF and RDFS semantic conditions are unchanged; all dependent model proofs are rebuilt.

The extra object still belongs to IC because rdfs:Class's named column contains all resources in this witness family. Its own class extension is empty. `unnamed_empty_class` proves those two facts, and `empty_class_model` packages an actual RDFS interpretation with that class.

The witness uses the constructor's existing sufficient compatibility and language-literal-coverage assumptions. It needs no empty-datatype-space premise, does not require a named empty class, and adds no closed-world reading of absent graph triples. It settles the permission within this parameterized model. The mapping retains the external concrete datatype/domain-realization boundary, consistently with the other model-construction records.

## Scope and remaining work

The catalogue has 169 mappings among 216 preliminary records, including partial mappings. Twenty-three new authored declarations have curated glosses. The two additional class typings without recognition, full concrete datatype meanings, general model/graph consistency, rule completeness, source-accountability acceptance, expert review and all package refinement remain open. These proofs establish neither complete RDF/RDFS formalization nor verification of Factoidal's JS/WASM paths.

## Deliberate registry audit

The registry adds 29 declarations: 23 authored declarations and six generated helpers. All existing authored declaration types remain unchanged. The typeExtension equation and case-analysis helper change type to distinguish named from unnamed columns; these two intentional generated-signature changes are explicitly reviewed. Three axiom-list reduction equations acquire RDFSConsequences compiler attribution because they are now requested earlier in the import order, retaining existing parent grounding.

The inventory has 1,666 local declarations in 57 formal files and a closure through 6,286 declarations. No new foundation modules or logical axioms are introduced. The allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`. All dependent model/example proofs were rebuilt after the witness relation changed.

## Validation

The full Lean build, frozen-registry audit, seven rejection checks, 15 Python tests, viewer generation, site staging/link checks, JavaScript syntax check and methodology-skill validation pass. The complete-coverage gate still rejects the draft. The short reviewer route is unchanged at 371 lines.

Five browser checks cover the nine derived property typings, recognition-qualified datatype class typing, universal class self-membership, the actual empty-class model, and the changed unnamed column alongside Resource nonemptiness. The configured suite contains 62 checks; Pages deployment requires the Chromium job to pass. These checks do not accept either expert-review stage or establish full specification/package coverage.
