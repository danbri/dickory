# Lean graphs, proper instances and finite blank support

23 October 2026. Fourteenth working increment. The finite-support consequence and the unrestricted reduction are proved; the full infinite-blank consequence remains open.

## Source and exact remaining obligation

The informative consequence is in [RDF 1.1 Semantics §5.3](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties), paragraph 13. Appendix C paragraphs 12–13 repeat it and give its proof. The governing definitions of proper instance and lean graph are normative §4. AI close reading selected and reviewed these passages; the source locator only binds the selected unchanged text.

The definitions distinguish two notions. A proper substitution replaces an occurring blank with a name or identifies distinct occurring blanks. A proper subgraph is a strict subset of triples. Leanness excludes an instance that is a proper subgraph. Neither definition silently adds inequality between a graph and the image of every proper substitution.

The source proof uses interpolation to obtain a subgraph that is a proper instance, then concludes non-leanness. Strict inclusion needs a separate justification. The new `lean_proper_nonentailment_iff` identifies the entire remaining obstruction under the current definitions: for a lean G, excluding entailment of every proper instance is equivalent to excluding `ProperInstance G G`.

This reduction uses the necessary direction of interpolation, composition of substitutions, preservation of properness through composition, leanness and entailment reflexivity. It needs no finiteness and works for generalized graphs. It does not rely on the unresolved converse instance-entailment direction for unrestricted generalized syntax.

## Finite-support proof

`FiniteBlankSupport G` means that the occurring blank set has an exact duplicate-free enumeration. It does not require a finite ambient blank type or finitely many triples. A finite graph implies finite blank support: collect blanks from each triple and reuse the existing enumeration constructor to remove repetitions with exact membership proved.

If a substitution maps G onto itself, every occurring output blank has a predecessor among the source blanks. Choose one predecessor for each blank. This choice is an injective self-map of the occurring blank set. The finite enumeration theorem makes it surjective too, ruling out both name replacement and collisions. Thus a graph with finite blank support cannot be a proper instance of itself.

Combining this with the unrestricted reduction proves that a lean graph with finite blank support does not simply entail a proper instance. The finite-graph corollary follows. Both results permit generalized syntax. `Statements.lean_proper_instance_finite_blank_lemma` is a one-line alias with the finite-blank premise visible; the source's unqualified claim remains partially mapped.

## Infinite diagnostic example

The constructed ordinary graph has one triple `_:b_n p o` for every natural n, with fixed IRI predicate and object. Mapping n to floor(n/2) identifies blanks 0 and 1 while preserving the entire triple set: 2n supplies a predecessor for every output triple. The graph is therefore a proper instance of itself, with literal set equality. Its blank set and triple set are both proved to lack finite enumerations.

The graph is also proved non-lean: mapping all blanks to 0 gives a singleton proper subgraph. This is **not a counterexample to the specification's theorem about lean graphs**. It is a checked diagnostic for the difference between proper instance and proper subgraph, not an example printed in the specification.

`Q-LEAN-PROPER-INFINITE-SCOPE` asks whether an arbitrary lean graph can admit a proper self-instance and what supplies the printed proof's strictness step. No counterexample to the headline source theorem or specification erratum has been established. An AI fidelity review is recorded as working evidence, not accepted expert review.

## Integration and boundaries

The catalogue has 166 mappings among 215 preliminary records, including partial mappings. Twenty-six authored declarations, including the new headline alias, have curated English glosses. The reviewer route remains below 400 lines. The proofs reuse the existing set syntax, proper-instance and leanness definitions, substitution composition, canonical-model interpolation and finite enumeration contract.

The unrestricted infinite-blank consequence remains open. Full source accountability, concrete name and datatype correspondence, other RDF/RDFS semantic and rule-completeness obligations, both expert-review stages and all JS/WASM/package refinement also remain unfinished. The finite theorem does not establish full coverage of the source statement.

## Deliberate registry audit

The registry adds 41 declarations: 26 authored declarations and 15 compiler-generated helpers. Existing declaration types and kinds are unchanged. Four existing blank-occurrence reduction equations acquire FiniteInstances compiler attribution because they are now requested earlier in the import order; their existing parent grounding is retained. New private case helpers retain explicit parents.

There are 1,637 local declarations in 56 formal files and a closure through 6,255 declarations. No new foundation modules or logical axioms are introduced. Allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.

## Validation

The full Lean build, frozen-registry verification, seven rejection checks, 15 Python tests, viewer generation, site staging/link checks, JavaScript syntax check and methodology-skill validation pass. The complete-coverage gate continues to reject this draft. The three-file reviewer route is 371 lines.

Four browser checks cover the finite-blank headline and gloss, the unrestricted self-instance equivalence and finite-graph bridge, the infinite example paired with non-leanness, and the unresolved source question/partial status. The configured suite now contains 57 checks; Pages deployment requires Chromium CI success.

The accompanying [version/family design](20261023-spec-versions-and-families.md) and Spec2Lean VER-01–12 address the user's request to prepare for RDF editions, errata, proposals, OWL and SPARQL. They are requirements and design documentation, not new formal coverage or implemented multi-baseline certification.
