# Name, graph and container infinitude

23 October 2026. Eleventh working increment. This is partial source formalization; expert acceptance and package refinement remain absent.

## Source reading and scope

AI close reading selected the §5 technical note on infinite name mappings, the final §5.3 compactness paragraph explicitly allowing infinite graphs, and Appendix D.2 paragraph 15. HTML parsing locates those selected passages in the unchanged hash-pinned source. All three passages are informative. The normative interpretation table remains the basis for the global domain of IS and partial IL.

D.2 paragraph 15 contains three distinct obligations. The inventory now separates the inability to assert a fixed membership count, the claimed consistency of adding a membership triple, and the absence of a finiteness requirement. The first two have no Lean mapping yet. In particular, the general addition claim needs its premise consistency, datatype, term-freshness and entailment-regime scope made explicit. A particular extendible family does not prove it.

The earlier `MT11-CONTAINER-OPEN-STRUCTURE` record now concerns only gaps and overlapping container types. Its existing witnesses remain unchanged. The new non-finiteness record does not inherit or confer coverage of the other sentences merely because they share one highlighted paragraph.

## Connected formal results

`Enumeration.no_enumeration_of_nat_injection` supplies a general mathematical bridge: a set containing distinct elements indexed by every natural number cannot have a finite certified enumeration. A proposed list of length k cannot accommodate k+1 distinct indexed elements. This reuses the existing membership and uniqueness contract rather than introducing a second notion of finite storage.

`NameInfinitude.lean` applies that bridge to the set-theoretic graph of IS. Distinct input names distinguish the pairs even when their denotations coincide. The indexed RDF vocabulary supplies an abstract infinite family. `one_resource_infinite_name_mapping` explicitly constructs a simple interpretation with a one-element resource domain and a name mapping with no finite enumeration. It is not an RDF/RDFS witness or a finite-vocabulary pre-interpretation. Concrete legal IRI spellings and correspondence to the full name domain are still external obligations.

`ContainerInfinitude.lean` builds an ordinary ground graph containing a Bag typing and every indexed membership edge. The object of each edge is the corresponding indexed IRI. The syntax is legal at the abstract ordinary-triple level, and predicate distinctness proves that the graph has no finite enumeration.

The same module reuses the verified RDFS constructor and its explicit sufficient `Parameters`. One model satisfies the infinite graph and every displayed finite prefix plus its next indexed edge. This result does not assert exact prefix cardinality or that the next edge is fresh. It does not establish consistency of extending an arbitrary premise graph.

In the chosen model, the member denotations are distinct. The existing container-subproperty and subproperty-inclusion conditions yield the generic rdfs:member edges. The resulting member extension has no finite enumeration. Distinct denotations are a witness choice, not a unique-name condition on every interpretation of the graph. Infinitely many distinct triples alone would not have established infinitely many distinct denotations.

## Review and assurance

The catalogue has 157 mappings among 210 preliminary records. The new mappings remain partial because the abstract vocabulary and datatype interfaces still need concrete correspondence. Counts are not compliance percentages; no expert reviews are accepted. The short review route through Statements, Syntax and Simple is unchanged.

Twenty-two newly authored declarations have curated English glosses. The browser checks expose the distinction between infinite naming and a singleton IR, the infinite graph's conditional satisfiability, the member-extension proof, the limited prefix claim, and the two unmapped general obligations. These presentation checks supplement source review; they cannot establish fidelity themselves.

The README also explains why existing countermodels choose rdf:value: its property typing and Resource domain/range axioms remain satisfied, while no value-extraction operation is added. This is separate from the datatype lexical-to-value mapping.

Concrete datatype meanings, general RDF/RDFS graph satisfiability, complete rule procedures, finite pre-interpretation preservation, other unmapped source material, source-accountability acceptance, expert mapping review and every npm/JS/WASM refinement remain outstanding. The complete-coverage gate must continue to reject the draft.

## Deliberate registry audit

The registry adds 28 declarations: 22 authored declarations and six generated helpers. Existing declaration signatures are unchanged. The total is 1,498 local declarations in 50 formal files, with a closure through 6,093 declarations. Newly reached standard-library modules `Init.Data.List.Range` and `Init.Data.List.Nat.Range` provide range length, membership, distinctness and extension facts. No added logical axioms, unsafe local declarations or proof placeholders occur. The audited axiom set remains `propext`, `Classical.choice` and `Quot.sound`. Generated equations for Set.union and indiscriminate and a structure congruence helper retain their actual new-module compiler attribution.

## Local validation

The full Lean build, frozen registry and dependency audit, source regeneration and hashes, seven negative gates, all 15 Python tests, and source/gloss viewer generation pass. JavaScript syntax, methodology-skill validation and whitespace checks pass. The three-file headline review route remains 359 lines. The browser suite now contains 43 checks; Chromium execution and Pages deployment are CI obligations, not a claimed local browser run.
