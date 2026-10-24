# RDF 1.1 Semantics: fresh Lean 4 reconstruction

**Seventeenth working increment: bounded simple countermodels and pre-interpretations, 24 October 2026. Not complete RDF formalization or package verification.**

This project reconstructs definitions and proofs from the pinned RDF 1.1 specifications. It imports no Factoidal implementation modules and copies no existing Factoidal proofs. The author has previously reviewed that implementation: “clean-room” here means a separate, source-first reconstruction, not an independently isolated team with no prior exposure.

For a short mathematical review, read [Statements.lean](RDF11/Statements.lean), [Syntax.lean](RDF11/Syntax.lean) and [Simple.lean](RDF11/Simple.lean). Together they are under 400 lines. The headline file restates the empty-graph, subgraph, instance, finite-blank lean/proper-instance, binary merging, interpolation, compactness, isomorphism Skolem conservativity/exact-lifting and the bounded simple countermodel results with source anchors and one-line proof aliases. Its explicit types retain ordinary/generalized scope, finiteness and freshness hypotheses. The empty-graph result has two clauses. Only interpolation and compactness are explicitly named in the source; the other headings are local review names. Follow dependencies for supporting definitions such as entailment, instances and Skolemization; these three files are an entry point, not a self-contained proof audit.

The [repository methodology skill](../../../.agents/skills/rdf11-spec2lean/SKILL.md) records the working method. AI close reading selects assertions; HTML parsing only locates those selected passages in the hash-pinned source. Mappings distinguish definitions from proved consequences and resolve contextual words to their antecedents. Every authored declaration has a draft English gloss, every local declaration has explicit grounding, and the registry is updated deliberately rather than automatically enrolled. Source-to-claim review and claim-to-Lean review are separate obligations. Neither compilation nor an AI source pass counts as accepted expert review.

The [edition and specification-family design](docs/20261023-spec-versions-and-families.md) extends Spec2Lean with explicit baseline bundles, claim lineage, errata overlays and checked bridges. It prepares RDF 1.2, OWL and SPARQL as distinct tracks. These catalogue/UI/bridge extensions are requirements, not implemented coverage; RDF 1.1 remains the current formalization baseline.

Start with the [source review prototype](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html), [notation and assurance boundary](docs/20261021-first-increment.md), and [mapping records](catalogue/mapping-review.json). The viewer offers an annotated rendered reading copy and an exact original-HTML tab. Search and colour-coded status filters distinguish mapped, partial and unmapped claims. Every displayed local Lean declaration has an expandable **ⓘ Plain-English explanation**, including generated dependency helpers. A Connected claims panel follows actual declaration dependencies and distinguishes shared bindings. Definitions and proof bodies remain visible; source links are pinned to the build commit. Try [ordinary instance entailment](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html#claim=MT11-INSTANCE-ENTAILMENT) or [isomorphism](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html#claim=MT11-ISOMORPHISM).

The reading copy adapts styling and disables active content/external resources. Its annotations are attached at original source-element offsets, and original source characters remain authoritative. A highlighted element can contain unextracted statements; highlighting is not complete passage coverage. The glosses are draft explanatory prose, not kernel-checked translations. Curated glosses are required for authored declarations; generated helpers receive explicitly labelled role/parent explanations. These presentation checks do not replace the fuller [Spec2Lean requirements](../spec2lean-requirements.md).

The viewer's trusted presentation tool, `tools/lean_sources.py`, obtains declaration ranges from Lean compiler metadata and slices the hash-checked source files at those Unicode positions. When a projection range contains only a field name, the viewer shows and labels its containing structure using that structure's compiler range, retaining the original identifier range in the evidence. Missing source for a mapped declaration fails generation. File links are pinned to the build's Git commit; full-file context includes imports and namespaces. Dependencies come from the existing elaborated evidence, with library dependencies listed separately and compiler-generated declarations identified when they lack a source range. This adds presentation evidence, not expert approval or a proof of mapping fidelity.

## What is checked

The full library builds with **Lean 4.33.1**, using only its standard distribution. There are no added axioms, proof placeholders, native-decision proofs, or unsafe local declarations. The audited logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.

- Graphs are extensional sets, including possibly infinite graphs. Repetition and order cannot distinguish sets with the same members.
- Ordinary triples enforce the subject/predicate/object categories. Generalized triples have a separate type.
- Simple interpretations retain W3C’s `IR`, `IP`, `IEXT`, `IS`, and partial `IL`. An infinite family of abstract IRI names makes the graph of IS non-enumerable by any finite list, even in a simple interpretation with just one resource. Concrete name-domain correspondence remains external.
- Graph truth requires one shared blank-node assignment. Assignment restriction, ground truth, empty-graph truth and undefined-literal falsity are proved.
- Simple entailment is defined by all interpretations, with subgraph entailment, premise monotonicity, universal simple satisfiability, and the empty-graph entailment property proved.
- Binary merge uses disjoint blank-node domains. Its satisfaction is equivalent to separately satisfying its two inputs. A proved counterexample distinguishes merge from union.
- Partial term substitutions, instances, vocabulary restrictions and properness are defined. Identity, composition, triple origin and ordinary instance entailment are proved.
- Graph isomorphisms use inverse renamings on occurring blanks; mutual instantiation and semantic equivalence are proved. Ground graphs are lean. Both directions of interpolation are proved for ordinary conclusions, including infinite graphs.
- A lean graph with finitely many occurring blanks does not simply entail a proper instance. Finite graphs have finite blank support, but the stronger theorem also permits infinite triple sets. An unrestricted equivalence isolates absence of proper self-instances as the exact remaining obligation for lean graphs. A constructed infinite proper self-instance is proved non-lean; it does not refute the source theorem.
- Compactness reuses finite enumeration images and interpolation. Vocabulary inclusion yields absent-IRI non-entailment.
- Skolemization connects to instances, groundness, leanness and fresh-vocabulary conservativity. Exact lifting now constructs an ordinary entailed graph with separate source/conclusion blank copies and proves that reapplication recovers the conclusion exactly. The semantic lifting proof also covers generalized graphs and distinct blank domains; neither proof requires finite graphs or Avoids-H. The source's implicit blank-scope convention remains under review.
- Datatype interpretations use fixed external meanings, partial lexical-to-value mappings and one shared value domain. Every recognized IRI, including langString, must denote its fixed datatype; aliases share both referent and value space. The language datatype has its pair space even though its L2V evaluation is nowhere defined. An explicit model construction proves that a graph is D-satisfiable exactly when it contains no ill-typed literal. Empty-D equivalence and recognition monotonicity are proved. Simultaneous same-value literal replacement preserves satisfaction in every position. Concrete XSD and literal syntax remain external obligations.
- RDF conditions and the full infinite axiom family are represented. A new explicit RDF model family proves inhabitation under sufficient compatibility hypotheses, discharged for the base recognition set. The family reuses the D-model literal construction and permits arbitrary non-type property extensions. Recognizing an empty-valued rdf:Property datatype is proved incompatible with every RDF model. rdfD1 uses one fresh shared witness; rdfD2 reuses the existing property proof. Generalized instance entailment remains conditional at the simple-semantics level.
- RDFS conditions define ICEXT through rdf:type, keeping classes, properties and literal values in one universe. An explicit RDFS model family now satisfies every condition and the full infinite axiom family. With base datatype recognition and aligned langString names, model existence in the current parameterized interfaces is equivalent to coverage of every language value by an actual tagged literal. Witnesses allow overlapping roles, distinct coextensive classes, self-membership/application, and an IRI typed rdfs:Literal. Two countermodels refute automatic transfer of an rdf:value assertion between a class and an individual member. All 14 named RDFS rules have shared-assignment soundness proofs; derivations compose into graph entailment and disjoint-datatype inconsistency.
- The additional-valid-triples table is derived rather than assumed: all nine property typings and twelve core class typings are proved. The XMLLiteral/HTML entries retain recognition premises and an open source question. Class self-membership is proved for every RDFS model; Resource is nonempty. The model family now supplies an unnamed class with exactly empty extension under its existing constructor hypotheses.
- Reification has ordinary four-triple syntax. RDFS countermodels separate describing a triple from asserting it, including an existential reification target, and separate metadata on two distinct named reifications with identical components. A checked positive entailment isolates an open question about the specification's printed standalone blank-node conclusion.
- Container countermodels preserve the printed conclusion shapes: Bag permutation has only membership edges, and the missing-index conclusion has two existential blanks. Bag/Seq overlap and container/member metadata non-transfer are witnessed. A new ordinary ground graph contains every indexed edge and has no finite enumeration. Under the existing constructor hypotheses, an RDFS model satisfies it and gives a Bag infinitely many distinct members. The same model covers all displayed finite prefixes and their next-edge extensions. Fixed-count expressivity and arbitrary membership-addition consistency remain separate, unmapped obligations.
- Collection descriptions retain the printed first/rest structure. General typing consequences reuse the existing domain/range axioms and sound RDFS rules. Countermodels refute permutation entailment for arbitrary distinct unrecognized item IRIs, permit at least two distinct heads and tails, and allow a first edge with no rest edge anywhere. A derived nil self-edge witness separates baseline semantics from the empty-collection convention; it does not imply nontermination of a traversal that stops at nil. The broad existence-closure and optional extension claims remain unmapped.
- Generalized RDF/RDFS closure uses Appendix A's conclusion-specific axiom seed, base datatype set, object-literal GrdfD1 and rdfD2. Rule saturation and positive instance checks are proved sound. Finite generation and completeness remain open, including a recorded container-axiom selection question.
- Datasets retain unique IRI-or-blank graph names and distinguish present empty graphs from absent names. One global isomorphism preserves blank sharing across keys and contents. A checked example shows that equivalent default-graph replacement can destroy dataset isomorphism; another proof identifies the graph-name presence information that quad-only storage loses.
- Optional dataset-policy interfaces keep the default-content recommendation explicit. Graph consequences compose with the existing entailment proofs; fixed-truth model restrictions preserve entailment. Checked examples distinguish truth changes from model restrictions, matching-name comparison from isomorphism, and name/graph pairing from denotation in simple interpretations. These are partial §10 mappings, not a certified universal dataset semantics.
- Appendix B's vocabulary restriction has a precise structure, reusing §5 with partial IL and separate IR/IP roles. Name completion preserves truth over its vocabulary. A separate compression proof now gives an N+B+1 bound on IR union IP, hence IR, and bounded-pre-interpretation equivalences for simple entailment and satisfiability. Finite graph inputs supply exact union-name and shared-blank enumerations. Compression retains one premise witness and conclusion falsity; it does not preserve every original positive graph. Full-name interpretations may have finite active domains despite infinite name mappings. Datatype/RDF/RDFS bounds and executable search remain open.
- Finite enumerations carry both membership and uniqueness proofs. Any two enumerations of the same set have the same length; each member occurs at most once.

The source catalogue has **172 mappings among 217 preliminary claim records**. Several mappings are partial. These numbers are not a compliance percentage. No extraction or formalization review is marked accepted.

Why some countermodels use `rdf:value`: [Semantics §8](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#rdf-interpretations) requires its `rdf:Property` typing, and [§9](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#rdfs-interpretations) requires its Resource domain and range. These axioms are included in our models. [Schema §5.4.3](https://www.w3.org/TR/2014/REC-rdf-schema-20140225/#ch_value) describes a structured-value idiom without giving the property a special operational meaning. The proofs choose its subject/object relation to exhibit counterexamples; they do not treat it as a literal evaluator, require a single value, or identify a resource with its value. This example choice is separate from the datatype theory's lexical-to-value mapping.

## Where to read

| File | Responsibility |
|---|---|
| [Statements.lean](RDF11/Statements.lean) | Short, source-anchored headline statements with one-line aliases to proved theorems |
| [Set.lean](RDF11/Set.lean) | Predicate sets, extensionality, union and membership algebra |
| [Syntax.lean](RDF11/Syntax.lean) | Ordinary/generalized syntax, occurrence and renaming |
| [Simple.lean](RDF11/Simple.lean) | Interpretation components and truth conditions |
| [Entailment.lean](RDF11/Entailment.lean) | Model-theoretic entailment and initial consequences |
| [Merge.lean](RDF11/Merge.lean) | Disjoint-domain merge and assignment transport |
| [Instances.lean](RDF11/Instances.lean) | Simultaneous substitution, properness, isomorphism, leanness and ordinary instance entailment |
| [Interpolation.lean](RDF11/Interpolation.lean) | Canonical model and ordinary interpolation equivalence |
| [FiniteEntailment.lean](RDF11/FiniteEntailment.lean) | Certified enumeration images and finite-conclusion compactness |
| [FiniteInstances.lean](RDF11/FiniteInstances.lean) | Finite blank support, proper substitution composition, exact self-instance obstruction and scoped non-entailment |
| [InstanceExamples.lean](RDF11/InstanceExamples.lean) | Infinite ordinary proper self-instance, infinitude and explicit non-leanness |
| [Vocabulary.lean](RDF11/Vocabulary.lean) / [VocabularyEntailment.lean](RDF11/VocabularyEntailment.lean) | Names, embedded datatype IRIs and absent-name non-entailment |
| [NameMaps.lean](RDF11/NameMaps.lean) | Name transport, interpretation pullback and truth preservation with blank sharing intact |
| [Preinterpretations.lean](RDF11/Preinterpretations.lean) | Restricted name domains, exact completion, local entailment and finite comparison vocabulary |
| [DomainRestriction.lean](RDF11/DomainRestriction.lean) | Induced resource/property domains, assignment transport and asymmetric satisfaction preservation |
| [FiniteSimpleModels.lean](RDF11/FiniteSimpleModels.lean) | N+B+1 active-domain bound, finite countermodels and bounded-pre-interpretation equivalences |
| [Skolemization.lean](RDF11/Skolemization.lean) | Fresh/injective naming, retraction and conservativity |
| [SkolemLifting.lean](RDF11/SkolemLifting.lean) | Separate blank copies, model transfer, ordinary syntax and exact Skolem lifting |
| [Transformations.lean](RDF11/Transformations.lean) | Satisfiability, process validity and composition |
| [RDFProperty.lean](RDF11/RDFProperty.lean) | One RDF condition, rdfD2 and conditional generalized substitution |
| [Datatypes.lean](RDF11/Datatypes.lean) | Fixed datatype meanings, normalized language values, D-models and consequences |
| [DatatypeModels.lean](RDF11/DatatypeModels.lean) | Explicit D-model construction and exact ill-typedness/satisfiability characterization |
| [LiteralSubstitution.lean](RDF11/LiteralSubstitution.lean) | Recognized values and simultaneous value-preserving literal substitution |
| [RDFModels.lean](RDF11/RDFModels.lean) | Full-domain RDF model family, base-recognition inhabitation, non-type triple independence and an incompatible datatype case |
| [RDFSModelConstraints.lean](RDF11/RDFSModelConstraints.lean) | Necessary tagged-literal coverage and transfer of RDF-unsatisfiability to RDFS |
| [RDFSModelRelations.lean](RDF11/RDFSModelRelations.lean) | Sufficient RDFS constructor parameters and chosen property/class relations |
| [RDFSModels.lean](RDF11/RDFSModels.lean) | All RDFS conditions and axioms, model existence and the base language-coverage equivalence |
| [RDFSModelExamples.lean](RDF11/RDFSModelExamples.lean) | Role overlap, coextensive classes, IRI literal-value consistency and class/member countermodels |
| [RDF.lean](RDF11/RDF.lean) / [RDFRules.lean](RDF11/RDFRules.lean) | RDF conditions, full axiom family, rdfD1/rdfD2 and datatype inconsistency |
| [RDFS.lean](RDF11/RDFS.lean) / [RDFSRules.lean](RDF11/RDFSRules.lean) | Class semantics, full RDFS axioms, rule and derivation soundness |
| [RDFSConsequences.lean](RDF11/RDFSConsequences.lean) | Derived additional typings, recognized-datatype class typing and universal class/Resource consequences |
| [Relations.lean](RDF11/Relations.lean) | Bridges between typed IEXT, relation notation and triple truth |
| [EntailmentClosure.lean](RDF11/EntailmentClosure.lean) | Appendix A axiom selection, generalized saturation and positive-check soundness |
| [ContainerEntailment.lean](RDF11/ContainerEntailment.lean) | Indexed-to-generic membership through the full RDFS axioms and rules |
| [RDFSFreeProperties.lean](RDF11/RDFSFreeProperties.lean) | Shared relation calculations for free example properties, including existential blank subjects |
| [Reification.lean](RDF11/Reification.lean) | Ordinary component-description syntax and the checked printed-conclusion source question |
| [ReificationExamples.lean](RDF11/ReificationExamples.lean) | Assertion/reification and distinct-resource metadata countermodels |
| [Collections.lean](RDF11/Collections.lean) | Ordinary head/tail, two-cell, branching and first-only source shapes |
| [CollectionEntailment.lean](RDF11/CollectionEntailment.lean) | Shared domain/range derivations, collection typing and semantic entailment |
| [CollectionExamples.lean](RDF11/CollectionExamples.lean) | Exact existential permutation, branching, missing-rest and nil self-edge witnesses |
| [NameInfinitude.lean](RDF11/NameInfinitude.lean) | Infinite IS graph and a one-resource simple witness |
| [ContainerInfinitude.lean](RDF11/ContainerInfinitude.lean) | Infinite ordinary graph, conditional RDFS satisfiability, infinite members and common-model finite prefixes |
| [ContainerExamples.lean](RDF11/ContainerExamples.lean) | Exact permutation/gap conclusion shapes, overlapping types and member-property countermodels |
| [Datasets.lean](RDF11/Datasets.lean) | Ordinary dataset structure, name uniqueness, empty-graph presence and representation equality |
| [DatasetIsomorphism.lean](RDF11/DatasetIsomorphism.lean) | Global blank bijections, component isomorphisms and equivalence |
| [DatasetExamples.lean](RDF11/DatasetExamples.lean) | Equivalent-default replacement breaks sharing; empty named graphs cannot disappear |
| [DatasetPolicies.lean](RDF11/DatasetPolicies.lean) | Explicit candidate regimes, adopted default-content conditions and graph-consequence transfer |
| [DatasetPolicyExamples.lean](RDF11/DatasetPolicyExamples.lean) | A fixed-IRI presence condition changes entailment while retaining default content and isomorphism invariance |
| [DatasetNameDenotation.lean](RDF11/DatasetNameDenotation.lean) | Full-domain simple-interpretation families allowing either name/graph identity or nonidentity |
| [DatasetNamedComparison.lean](RDF11/DatasetNamedComparison.lean) | Illustrative matching-name comparison and its structural limits |
| [ScopeExample.lean](RDF11/ScopeExample.lean) | Checked shared-witness counterexample |
| [GeneralizedScope.lean](RDF11/GeneralizedScope.lean) | Checked countermodel for an explicit source-scope review question |
| [Enumeration.lean](RDF11/Enumeration.lean) | Finite implementation contract, separate from graph semantics |
| [Coverage.lean](Audit/Coverage.lean) | General range-partition and reference-validity proofs |
| [Snapshot.lean](Audit/Snapshot.lean) | Concrete draft certificates for both archived specifications |
| [Export.lean](Audit/Export.lean) | Trusted extractor of actual elaborated types and dependencies |

[registry.json](catalogue/registry.json) inventories every local Lean file and 1,831 declarations, including generated helpers. [declarations.json](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/declarations.json) records their closure through 6,472 declarations. The checker rejects unregistered files even when they are not imported.

## Reproduce

Use Python **3.14.7** (recorded in the frozen catalogue) and run from this directory. Generated evidence and the viewer are published by CI rather than committed:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 tools/verify.py
python3 tools/negative_checks.py
python3 -m unittest discover -s tools -p 'test_*.py'
python3 tools/review_viewer.py
```

The verifier builds both libraries, extracts dependencies, checks the frozen inventory and re-derives the source catalogue. [Verification evidence](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/verification.json) and [negative checks](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/negative-checks.json) describe the result.

`python3 tools/verify.py --require-complete` deliberately exits **2**: unresolved text, incomplete mappings, pending expert reviews and absent implementation refinement must prevent a complete-coverage claim. A normal draft verification passes without pretending those obligations are closed.

After an intentional formal edit, update the explicit registry and review the diff. The verifier never auto-enrols new declarations or files. `tools/source_catalogue.py` regenerates the draft catalogue and source certificate; it does not accept reviews.

## Remaining work

See the [bounded simple-model increment](docs/20261024-finite-simple-models.md), [vocabulary pre-interpretation increment](docs/20261023-preinterpretations.md), [RDFS consequence increment](docs/20261023-rdfs-consequences.md), [lean/proper-instance increment](docs/20261023-finite-instances.md), [exact Skolem lifting increment](docs/20261023-skolem-lifting.md), [collection typing and countermodel increment](docs/20261023-collections.md), [name, graph and container infinitude increment](docs/20261023-infinitude.md), [reification/container witnesses and blank-node source question](docs/20261023-reification-containers.md), [RDFS model construction and source-facing witnesses](docs/20261023-rdfs-model-existence.md), [RDF model construction and RDFS compatibility work](docs/20261023-rdf-model-existence.md), [global-name correction](docs/20261023-global-name-scope.md), [dataset-policy increment](docs/20261023-dataset-policies.md), [dataset increment](docs/20261023-datasets.md), [D-models and generalized-closure increment](docs/20261023-models-and-closure.md), [datatype/RDF/RDFS review method](docs/20261023-datatypes-rdfs-review.md) and earlier [connected-proof audit](docs/20261023-connected-entailment.md). The principal gaps are concrete IRI/literal definitions and equality; literal/vocabulary coverage and concrete datatype libraries; generalized interpolation scope, unrestricted infinite-blank lean/proper-instance non-entailment and expert resolution of exact Skolem lifting's source blank-scope convention; general RDF/RDFS compatibility and arbitrary-graph consistency characterizations and full rule-completeness proofs; datatype/RDF/RDFS finite-pre-interpretation bounds and finite decision procedures; dataset-policy conformance and semantic-extension admissibility; and remaining informative/general requirements. D-, RDF- and RDFS-model families are proved. The base RDF recognition set admits a model when the langString names agree; the base RDFS model class additionally requires, and is inhabited given, actual language-literal coverage. Arbitrary recognized sets can contradict the RDF conditions. The RDFS constructor uses universal IR, IP, IC and LV as a witness choice while keeping recognized datatype class extensions exact. The external Value domain supplies values and datatype descriptors; it is not asserted to exhaust LV. These facts do not certify concrete built-in meanings or arbitrary-graph satisfiability.

The complete requirement set also needs finer context-resolution ranges, expert review records for both mapping stages, and a Lean proof of the declaration-grounding certificate itself. The current rendered view and glosses aid review but do not certify fidelity.

The [generalized-instance review question](docs/generalized-instance-question.md) records a checked conflict between an unrestricted generalized-graph reading of the instance consequence and the currently transcribed interpretation domains. It is not a declared specification erratum and does not refute the ordinary-RDF consequence.

The W3C test repository remains pinned at `d5d930b03ee6b63b388d0bb28fdb29ee78a59ec0` in [w3c/rdf-tests](https://github.com/w3c/rdf-tests/tree/d5d930b03ee6b63b388d0bb28fdb29ee78a59ec0). This fresh model has no parser or decision procedure connected to those fixtures yet. Earlier test successes belong to the separate implementation experiment and are not claimed here.

No Factoidal JS/WASM wrapper, package artifact, ingestion path, query engine, or serialization path is refined by these proofs yet. Preventing the observed npm defects requires those boundaries to consume certified representations and preserve their contracts.

