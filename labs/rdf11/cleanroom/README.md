# RDF 1.1 Semantics: fresh Lean 4 reconstruction

**First working increment, 21 October 2026. Not complete RDF formalization or package verification.**

This project reconstructs definitions and proofs from the pinned RDF 1.1 specifications. It imports no Factoidal implementation modules and copies no existing Factoidal proofs. The author has previously reviewed that implementation: “clean-room” here means a separate, source-first reconstruction, not an independently isolated team with no prior exposure.

Start with the [source review prototype](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html), [notation and assurance boundary](docs/20261021-first-increment.md), and [mapping records](catalogue/mapping-review.json). The prototype displays the original HTML as raw source with clickable scalar ranges. Claim entries show actual Lean definition and proof bodies, with expandable source context, elaborated types and dependency declarations. For example, [triple term domains](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/source-review.html#claim=MT11-TRIPLE-TERM-DOMAINS) shows the `Triple`, `Subject` and `Term` source immediately. It is not yet the faithful rendered-document viewer specified in [Spec2Lean requirements](../spec2lean-requirements.md).

The viewer's trusted presentation tool, `tools/lean_sources.py`, obtains declaration ranges from Lean compiler metadata and slices the hash-checked source files at those Unicode positions. Missing source for a mapped declaration fails generation. File links are pinned to the build's Git commit; full-file context includes imports and namespaces. Dependencies come from the existing elaborated evidence, with library dependencies listed separately and compiler-generated declarations identified when they lack a source range. This adds presentation evidence, not expert approval or a proof of mapping fidelity.

## What is checked

The full library builds with **Lean 4.33.1**, using only its standard distribution. There are no added axioms, proof placeholders, native-decision proofs, or unsafe local declarations. The audited logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.

- Graphs are extensional sets, including possibly infinite graphs. Repetition and order cannot distinguish sets with the same members.
- Ordinary triples enforce the subject/predicate/object categories. Generalized triples have a separate type.
- Simple interpretations retain W3C’s `IR`, `IP`, `IEXT`, `IS`, and partial `IL`.
- Graph truth requires one shared blank-node assignment. Assignment restriction, ground truth, empty-graph truth and undefined-literal falsity are proved.
- Simple entailment is defined by all interpretations, with subgraph entailment, premise monotonicity, universal simple satisfiability, and the empty-graph entailment property proved.
- Binary merge uses disjoint blank-node domains. Its satisfaction is equivalent to separately satisfying its two inputs. A proved counterexample distinguishes merge from union.
- Finite enumerations carry both membership and uniqueness proofs. Any two enumerations of the same set have the same length; each member occurs at most once.

The source catalogue has **34 initial mappings among 195 preliminary claim records**. Several mappings are partial. These numbers are not a compliance percentage. No extraction or formalization review is marked accepted.

## Where to read

| File | Responsibility |
|---|---|
| [Set.lean](RDF11/Set.lean) | Predicate sets, extensionality, union and membership algebra |
| [Syntax.lean](RDF11/Syntax.lean) | Ordinary/generalized syntax, occurrence and renaming |
| [Simple.lean](RDF11/Simple.lean) | Interpretation components and truth conditions |
| [Entailment.lean](RDF11/Entailment.lean) | Model-theoretic entailment and initial consequences |
| [Merge.lean](RDF11/Merge.lean) | Disjoint-domain merge and assignment transport |
| [ScopeExample.lean](RDF11/ScopeExample.lean) | Checked shared-witness counterexample |
| [GeneralizedScope.lean](RDF11/GeneralizedScope.lean) | Checked countermodel for an explicit source-scope review question |
| [Enumeration.lean](RDF11/Enumeration.lean) | Finite implementation contract, separate from graph semantics |
| [Coverage.lean](Audit/Coverage.lean) | General range-partition and reference-validity proofs |
| [Snapshot.lean](Audit/Snapshot.lean) | Concrete draft certificates for both archived specifications |
| [Export.lean](Audit/Export.lean) | Trusted extractor of actual elaborated types and dependencies |

[registry.json](catalogue/registry.json) inventories every local Lean file and 370 declarations, including generated helpers. [declarations.json](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/declarations.json) records their closure through 2,323 declarations. The checker rejects unregistered files even when they are not imported.

## Reproduce

Use Python **3.14.7** (recorded in the frozen catalogue) and run from this directory. Generated evidence and the viewer are published by CI rather than committed:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 tools/verify.py
python3 tools/negative_checks.py
python3 tools/review_viewer.py
```

The verifier builds both libraries, extracts dependencies, checks the frozen inventory and re-derives the source catalogue. [Verification evidence](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/verification.json) and [negative checks](https://danbri.github.io/dickory/labs/rdf11/cleanroom/artifacts/negative-checks.json) describe the result.

`python3 tools/verify.py --require-complete` deliberately exits **2**: unresolved text, incomplete mappings, pending expert reviews and absent implementation refinement must prevent a complete-coverage claim. A normal draft verification passes without pretending those obligations are closed.

After an intentional formal edit, update the explicit registry and review the diff. The verifier never auto-enrols new declarations or files. `tools/source_catalogue.py` regenerates the draft catalogue and source certificate; it does not accept reviews.

## Remaining work

Concrete IRI/literal definitions and equality, general instances, graph isomorphism, interpolation and compactness, skolemization, datatype interpretations, RDF/RDFS conditions and rules, datasets, and the remaining informative/general requirements are open. The complete requirement set also needs a rendered HTML viewer, finer context-resolution ranges, independent expert review records, and a Lean proof of the declaration-grounding certificate itself.

The [generalized-instance review question](docs/generalized-instance-question.md) records a checked conflict between an unrestricted generalized-graph reading of the instance consequence and the currently transcribed interpretation domains. It is not a declared specification erratum and does not refute the ordinary-RDF consequence.

The W3C test repository remains pinned at `d5d930b03ee6b63b388d0bb28fdb29ee78a59ec0` in [w3c/rdf-tests](https://github.com/w3c/rdf-tests/tree/d5d930b03ee6b63b388d0bb28fdb29ee78a59ec0). This fresh model has no parser or decision procedure connected to those fixtures yet. Earlier test successes belong to the separate implementation experiment and are not claimed here.

No Factoidal JS/WASM wrapper, package artifact, ingestion path, query engine, or serialization path is refined by these proofs yet. Preventing the observed npm defects requires those boundaries to consume certified representations and preserve their contracts.

