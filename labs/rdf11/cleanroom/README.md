# RDF 1.1 Semantics: fresh Lean 4 reconstruction

**Eighth working increment: RDF models and datatype fidelity, 23 October 2026. Not complete RDF formalization or package verification.**

This project reconstructs definitions and proofs from the pinned RDF 1.1 specifications. It imports no Factoidal implementation modules and copies no existing Factoidal proofs. The author has previously reviewed that implementation: “clean-room” here means a separate, source-first reconstruction, not an independently isolated team with no prior exposure.

For a short mathematical review, read [Statements.lean](RDF11/Statements.lean), [Syntax.lean](RDF11/Syntax.lean) and [Simple.lean](RDF11/Simple.lean). Together they are under 400 lines. The headline file restates the empty-graph, subgraph, instance, binary merging, interpolation, compactness, isomorphism and Skolem conservativity results with source anchors and one-line proof aliases. Its explicit types retain ordinary/generalized scope, finiteness and freshness hypotheses. The empty-graph result has two clauses. Only interpolation and compactness are explicitly named in the source; the other headings are local review names. Follow dependencies for supporting definitions such as entailment, instances and Skolemization; these three files are an entry point, not a self-contained proof audit.

The [repository methodology skill](../../../.agents/skills/rdf11-spec2lean/SKILL.md) records the working method. AI close reading selects assertions; HTML parsing only locates those selected passages in the hash-pinned source. Mappings distinguish definitions from proved consequences and resolve contextual words to their antecedents. Every authored declaration has a draft English gloss, every local declaration has explicit grounding, and the registry is updated deliberately rather than automatically enrolled. Source-to-claim review and claim-to-Lean review are separate obligations. Neither compilation nor an AI source pass counts as accepted expert review.

Start with the [source review prototype](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html), [notation and assurance boundary](docs/20261021-first-increment.md), and [mapping records](catalogue/mapping-review.json). The viewer offers an annotated rendered reading copy and an exact original-HTML tab. Search and colour-coded status filters distinguish mapped, partial and unmapped claims. Every displayed local Lean declaration has an expandable **ⓘ Plain-English explanation**, including generated dependency helpers. A Connected claims panel follows actual declaration dependencies and distinguishes shared bindings. Definitions and proof bodies remain visible; source links are pinned to the build commit. Try [ordinary instance entailment](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html#claim=MT11-INSTANCE-ENTAILMENT) or [isomorphism](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html#claim=MT11-ISOMORPHISM).

The reading copy adapts styling and disables active content/external resources. Its annotations are attached at original source-element offsets, and original source characters remain authoritative. A highlighted element can contain unextracted statements; highlighting is not complete passage coverage. The glosses are draft explanatory prose, not kernel-checked translations. Curated glosses are required for authored declarations; generated helpers receive explicitly labelled role/parent explanations. These presentation checks do not replace the fuller [Spec2Lean requirements](../spec2lean-requirements.md).

The viewer's trusted presentation tool, `tools/lean_sources.py`, obtains declaration ranges from Lean compiler metadata and slices the hash-checked source files at those Unicode positions. When a projection range contains only a field name, the viewer shows and labels its containing structure using that structure's compiler range, retaining the original identifier range in the evidence. Missing source for a mapped declaration fails generation. File links are pinned to the build's Git commit; full-file context includes imports and namespaces. Dependencies come from the existing elaborated evidence, with library dependencies listed separately and compiler-generated declarations identified when they lack a source range. This adds presentation evidence, not expert approval or a proof of mapping fidelity.

## What is checked

The full library builds with **Lean 4.33.1**, using only its standard distribution. There are no added axioms, proof placeholders, native-decision proofs, or unsafe local declarations. The audited logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.

- Graphs are extensional sets, including possibly infinite graphs. Repetition and order cannot distinguish sets with the same members.
- Ordinary triples enforce the subject/predicate/object categories. Generalized triples have a separate type.
- Simple interpretations retain W3C’s `IR`, `IP`, `IEXT`, `IS`, and partial `IL`.
- Graph truth requires one shared blank-node assignment. Assignment restriction, ground truth, empty-graph truth and undefined-literal falsity are proved.
- Simple entailment is defined by all interpretations, with subgraph entailment, premise monotonicity, universal simple satisfiability, and the empty-graph entailment property proved.
- Binary merge uses disjoint blank-node domains. Its satisfaction is equivalent to separately satisfying its two inputs. A proved counterexample distinguishes merge from union.
- Partial term substitutions, instances, vocabulary restrictions and properness are defined. Identity, composition, triple origin and ordinary instance entailment are proved.
- Graph isomorphisms use inverse renamings on occurring blanks; mutual instantiation and semantic equivalence are proved. Ground graphs are lean. Both directions of interpolation are proved for ordinary conclusions, including infinite graphs.
- Compactness reuses finite enumeration images and interpolation. Vocabulary inclusion yields absent-IRI non-entailment.
- Skolemization connects to instances, groundness, leanness and fresh-vocabulary conservativity, with explicit freshness and ordinary-source boundaries.
- Datatype interpretations use fixed external meanings, partial lexical-to-value mappings and one shared value domain. Every recognized IRI, including langString, must denote its fixed datatype; aliases share both referent and value space. The language datatype has its pair space even though its L2V evaluation is nowhere defined. An explicit model construction proves that a graph is D-satisfiable exactly when it contains no ill-typed literal. Empty-D equivalence and recognition monotonicity are proved. Simultaneous same-value literal replacement preserves satisfaction in every position. Concrete XSD and literal syntax remain external obligations.
- RDF conditions and the full infinite axiom family are represented. A new explicit RDF model family proves inhabitation under sufficient compatibility hypotheses, discharged for the base recognition set. The family reuses the D-model literal construction and permits arbitrary non-type property extensions. Recognizing an empty-valued rdf:Property datatype is proved incompatible with every RDF model. rdfD1 uses one fresh shared witness; rdfD2 reuses the existing property proof. Generalized instance entailment remains conditional at the simple-semantics level.
- RDFS conditions define ICEXT through rdf:type, keeping classes, properties and literal values in one universe. Any RDFS model is now proved to require tagged-literal representatives for all language-string values; the abstract literal interface does not yet supply that coverage. Both finite axiom lists, the hierarchy axioms and all positive container indices are included. All 14 named RDFS rules have a shared-assignment soundness proof; derivations compose into graph entailment and disjoint-datatype inconsistency.
- Generalized RDF/RDFS closure uses Appendix A's conclusion-specific axiom seed, base datatype set, object-literal GrdfD1 and rdfD2. Rule saturation and positive instance checks are proved sound. Finite generation and completeness remain open, including a recorded container-axiom selection question.
- Datasets retain unique IRI-or-blank graph names and distinguish present empty graphs from absent names. One global isomorphism preserves blank sharing across keys and contents. A checked example shows that equivalent default-graph replacement can destroy dataset isomorphism; another proof identifies the graph-name presence information that quad-only storage loses.
- Optional dataset-policy interfaces keep the default-content recommendation explicit. Graph consequences compose with the existing entailment proofs; fixed-truth model restrictions preserve entailment. Checked examples distinguish truth changes from model restrictions, matching-name comparison from isomorphism, and name/graph pairing from denotation in simple interpretations. These are partial §10 mappings, not a certified universal dataset semantics.
- Finite enumerations carry both membership and uniqueness proofs. Any two enumerations of the same set have the same length; each member occurs at most once.

The source catalogue has **144 mappings among 204 preliminary claim records**. Several mappings are partial. These numbers are not a compliance percentage. No extraction or formalization review is marked accepted.

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
| [Vocabulary.lean](RDF11/Vocabulary.lean) / [VocabularyEntailment.lean](RDF11/VocabularyEntailment.lean) | Names, embedded datatype IRIs and absent-name non-entailment |
| [Skolemization.lean](RDF11/Skolemization.lean) | Fresh/injective naming, retraction and conservativity |
| [Transformations.lean](RDF11/Transformations.lean) | Satisfiability, process validity and composition |
| [RDFProperty.lean](RDF11/RDFProperty.lean) | One RDF condition, rdfD2 and conditional generalized substitution |
| [Datatypes.lean](RDF11/Datatypes.lean) | Fixed datatype meanings, normalized language values, D-models and consequences |
| [DatatypeModels.lean](RDF11/DatatypeModels.lean) | Explicit D-model construction and exact ill-typedness/satisfiability characterization |
| [LiteralSubstitution.lean](RDF11/LiteralSubstitution.lean) | Recognized values and simultaneous value-preserving literal substitution |
| [RDFModels.lean](RDF11/RDFModels.lean) | Full-domain RDF model family, base-recognition inhabitation, non-type triple independence and an incompatible datatype case |
| [RDFSModelConstraints.lean](RDF11/RDFSModelConstraints.lean) | Necessary tagged-literal coverage and transfer of RDF-unsatisfiability to RDFS |
| [RDF.lean](RDF11/RDF.lean) / [RDFRules.lean](RDF11/RDFRules.lean) | RDF conditions, full axiom family, rdfD1/rdfD2 and datatype inconsistency |
| [RDFS.lean](RDF11/RDFS.lean) / [RDFSRules.lean](RDF11/RDFSRules.lean) | Class semantics, full RDFS axioms, rule and derivation soundness |
| [Relations.lean](RDF11/Relations.lean) | Bridges between typed IEXT, relation notation and triple truth |
| [EntailmentClosure.lean](RDF11/EntailmentClosure.lean) | Appendix A axiom selection, generalized saturation and positive-check soundness |
| [ContainerEntailment.lean](RDF11/ContainerEntailment.lean) | Indexed-to-generic membership through the full RDFS axioms and rules |
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

[registry.json](catalogue/registry.json) inventories every local Lean file and 1,378 declarations, including generated helpers. [declarations.json](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/declarations.json) records their closure through 5,892 declarations. The checker rejects unregistered files even when they are not imported.

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

See the [RDF model construction and RDFS compatibility work](docs/20261023-rdf-model-existence.md), [global-name correction](docs/20261023-global-name-scope.md), [dataset-policy increment](docs/20261023-dataset-policies.md), [dataset increment](docs/20261023-datasets.md), [D-models and generalized-closure increment](docs/20261023-models-and-closure.md), [datatype/RDF/RDFS review method](docs/20261023-datatypes-rdfs-review.md) and earlier [connected-proof audit](docs/20261023-connected-entailment.md). The principal gaps are concrete IRI/literal definitions and equality; literal/vocabulary coverage and concrete datatype libraries; generalized interpolation scope, lean/proper-instance non-entailment and exact skolem lifting; general RDF compatibility, RDFS model-existence and full rule-completeness proofs; finite decision procedures; dataset-policy conformance and semantic-extension admissibility; and remaining informative/general requirements. D-model existence and an RDF model family are proved. The base RDF recognition set admits a model when the langString names agree; arbitrary recognized sets can contradict the RDF conditions. Full RDFS model construction remains open and must meet the proved language-literal coverage obligation as well as the remaining RDFS conditions.

The complete requirement set also needs finer context-resolution ranges, expert review records for both mapping stages, and a Lean proof of the declaration-grounding certificate itself. The current rendered view and glosses aid review but do not certify fidelity.

The [generalized-instance review question](docs/generalized-instance-question.md) records a checked conflict between an unrestricted generalized-graph reading of the instance consequence and the currently transcribed interpretation domains. It is not a declared specification erratum and does not refute the ordinary-RDF consequence.

The W3C test repository remains pinned at `d5d930b03ee6b63b388d0bb28fdb29ee78a59ec0` in [w3c/rdf-tests](https://github.com/w3c/rdf-tests/tree/d5d930b03ee6b63b388d0bb28fdb29ee78a59ec0). This fresh model has no parser or decision procedure connected to those fixtures yet. Earlier test successes belong to the separate implementation experiment and are not claimed here.

No Factoidal JS/WASM wrapper, package artifact, ingestion path, query engine, or serialization path is refined by these proofs yet. Preventing the observed npm defects requires those boundaries to consume certified representations and preserve their contracts.

