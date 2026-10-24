# Finite closures, supporting terms and source scope

24 October 2026, twenty-second increment. The unchanged Appendix A closure procedure now has exact finiteness characterizations, cubic size bounds and explicit scope counterexamples. Effective generation, polynomial runtime and entailment completeness remain separate obligations.

## Source reading and claim extraction

The source-reading subagent used AI close reading of Appendix A, its surrounding input definitions, Concepts's graph/term definitions and Semantics's explicit permission for infinite graphs. Parsing located the selected paragraphs; it did not determine their meaning. The input definition is `#entailment-rules-informative > p:nth-of-type(15)`, the procedure paragraph 16, finiteness/complexity paragraph 19, and tautology inclusion paragraph 20. The base recognition set and exact rule list remain those in paragraph 16. Paragraphs 21–22 describe separate fresh-blank and larger-datatype procedures.

Paragraph 19 asserts finite closures without stating a finite-input premise. There is no global finite-graph convention: Concepts defines a set of triples, and Semantics explicitly permits infinite graphs at `#properties-of-simple-entailment-informative > p:nth-of-type(16)`. The inventory's earlier paraphrase had inserted a finite-effective-input qualifier. This increment restores the unqualified source claim and makes the qualified theorem and source question separate evidence.

Paragraph 20's tautology assertion is newly extracted as MT11-CLOSURE-TAUTOLOGIES. It names the original graph vocabulary plus the RDF/RDFS vocabularies, whose indexed container family is infinite. Its intended scope needs review. Both paragraphs are informative; neither question is declared an official erratum.

## Exact finiteness

For both `RDFClosure` and `RDFSClosure`, the proved equivalence is:

```text
The closure of G towards E is finite
iff
G is finite and E's vocabulary contains finitely many indexed container names.
```

Finite G and E are sufficient, but E itself need not be finite. Its other terms, including its blank nodes, are not inserted into the closure. Literal datatype IRIs do contribute to E's selected vocabulary. No assumption of consistency or of the disputed closure-completeness claim is used. The supporting results cover generalized inputs as well as the ordinary inputs named by the source.

Necessity has two parts. Every premise triple belongs to its closure. Also every E-selected index contributes a distinct property-typing axiom. A finite closure therefore bounds both the premise and the selected-index set. The proof uses injectivity of syntax-name binding, not a unique-name assumption on semantic denotations.

For sufficiency, each axiom mentions at most one indexed name. All non-indexed symbols form a finite list; the selected names and possible rdf:_1 fallback add only finitely many more. The exact E-only selection and fallback test are preserved. Selection enumerates actual indices, not all natural numbers below the largest index.

## Term universe and quantitative bounds

`ClosureTermBounds.lean` collects supporting terms from all three triple positions. Every literal contributes its datatype IRI as well as the literal itself, because GrdfD1 can expose that IRI. Fixed axiom/rule names, selected container names and the possible fallback are added. Premise blank identities are preserved. Generalized rules introduce no fresh blank or literal; rdfs1 adds only the two base recognized datatype names.

The finite supporting pool is an overapproximation. It includes some names even when a particular derivation does not use them, and does not claim minimality. A certified duplicate-free enumeration defines K as the number of distinct supporting terms. K is not a named-node count printed by W3C; Concepts's subject/object node terminology should not be substituted for this all-position term count.

The Cartesian cube has exactly K³ list entries. Every derived triple lies within it. Restricting its enumeration to the closure gives a membership-faithful, duplicate-free enumeration of at most K³ triples. `rdf_closure_bound` and `rdfs_closure_bound` expose the actual pool enumeration and closure enumeration in their conclusions.

`insertion_bound` connects an enumerated seed and closure to a duplicate-free list of newly inserted facts: its length is at most the closure size bound minus the seed size. It can be instantiated with the cubic bound. It does not count failed rule matches, repeated consequences or time spent comparing terms.

These constructions use classical choice and noncomputable filtering of arbitrary predicates. They establish mathematical finiteness and cardinality, not an effective saturation implementation. Runtime requires an executable representation, equality, rule matching, duplicate detection, scheduling and a cost model that accounts for input representation. Larger recognition sets and fresh-blank rdfD1 require separate arguments. Closure generation also remains distinct from the subsequent simple-entailment search.

## Checked scope boundaries

`consistent_infinite_closures` reuses the existing ordinary Bag graph containing every indexed membership triple. Its full RDFS satisfying model retains all conditions under explicit sufficient datatype parameters. The RDF and RDFS closures towards the empty conclusion are infinite because they contain that premise. Semantic consistency therefore cannot substitute for the missing finite-input hypothesis.

Every indexed `rdf:_n rdf:type rdf:Property` axiom is RDF-valid and hence RDFS-valid under the same parameters. Every finite graph omits at least one such axiom, since the syntax family is injectively indexed by the natural numbers. Applying the finite-closure theorem to empty inputs therefore gives a valid tautology outside each closure.

The term-pool proof gives a more explicit result: with both inputs empty, every indexed property-typing axiom except the possible rdf:_1 fallback is absent. In particular, `rdf:_2 rdf:type rdf:Property` is valid but absent from both selected closures. These proofs keep the infinite vocabulary intact. They do not silently replace paragraph 20 with a selected-finite-vocabulary claim or prove that possible replacement.

Q-CLOSURE-FINITE-INPUT records the unstated input qualification. Q-CLOSURE-TAUTOLOGY-VOCABULARY records the full-vocabulary inclusion conflict. Both expose exact Lean statements, actual proof bodies and curated English glosses. Source fidelity, concrete IRI spelling, datatype correspondence for model witnesses and any official correction remain outside these kernel results.

## Integration and review

The new proofs reuse the existing `Enumeration`, `FiniteGraph`, vocabulary extraction, least rule closure, individual rule constructors and full RDFS model construction. The four modules are `ClosureTermBounds.lean`, `ClosureVocabulary.lean`, `FiniteClosure.lean` and `ClosureFinitenessScope.lean`. Original axiom-selection and rule definitions are unchanged.

There are 181 mappings among 222 preliminary records, including partial mappings, and thirteen open source questions. These are inventory counts, not coverage percentages. The finiteness/complexity mapping remains partial because effective generation and complexity are unproved. The tautology mapping records counterexample evidence rather than claiming its source assertion proved. All expert reviews remain pending and package refinement remains absent. The short Statements/Syntax/Simple route stays at 393 lines.


## Deliberate registry audit

The increment adds 111 local declarations: 74 authored declarations with curated English glosses and 37 compiler-generated equations, pattern helpers, simplifier proofs and structure-congruence support with explicit parent links. All prior declarations retain their type, kind and module attribution. The existing root import and generated source-range snapshot change; four formal modules are deliberately enrolled. The archived source bytes are unchanged.

The registry now contains 2,453 local declarations across 76 formal files and a dependency closure of 7,136 declarations. The additional standard-library module Init.Data.Zero contributes the two axiom-free definitions connecting Zero and OfNat 0; both were inspected. No new logical axiom is admitted: propext, Classical.choice and Quot.sound remain the allowed set.

## Validation

The 78-job Lean build and exported dependency inventory pass the source/catalogue verifier. All eight rejection checks pass, including the duplicate-bearing Enumeration rejection and the rejection of a request for complete coverage. All fifteen Python tests pass. The offline viewer and site regenerate, local links resolve, the browser script passes its syntax check, and the methodology skill validates.

Five browser interaction checks are added for the finite-input result, exact finiteness characterization, cubic/insertion bounds, consistent infinite-premise witness and explicit missing indexed tautology. They inspect displayed proof bodies, English glosses, partial mapping status and source questions. Actual Chromium execution and deployment are CI gates; local generation alone is not browser evidence.
