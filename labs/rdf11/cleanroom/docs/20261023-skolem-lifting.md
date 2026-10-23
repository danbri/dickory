# Exact Skolem lifting with separate blank copies

23 October 2026. Thirteenth working increment. The mathematical theorem is checked; its mapping to the source's implicit blank-scope convention remains subject to expert review.

## Source scope

RDF 1.1 Semantics §6 paragraph 6 states the lifting consequence; Appendix C paragraphs 16–17 repeat it and give a proof. These passages are informative. §6 paragraphs 2–3 supply the freshness and source-graph context. AI close reading selected these passages; the locator only binds their unchanged source intervals.

The inventory note for original-not-Skolem is corrected: the source does supply the nonempty-blank premise in the paragraph beginning “Suppose G is a graph containing blank nodes.” The previous note incorrectly treated that premise as absent. The existing theorem and its mapping already retained the premise, so no mathematical statement changed.

The exact lifting equation needs an explicit extension of the original naming map. The existing `sk.substitution` names every ambient blank value. That is sufficient for constructing sk(G), but applying it to any other graph grounds all that graph's blanks too. Two new theorems prove this distinction and exclude recovery of a conclusion containing blanks through that ambient-total operation.

## Construction and proof

The lifted graph uses `Sum B C`: left copies represent blanks from G, right copies preserve blanks from H. The caller's input domains need not be disjoint. Inverse naming replaces only generated IRIs with left-copy blanks and preserves existing conclusion blanks as right copies. Reapplication names the left copy while preserving the right copy. Term, triple and graph proofs establish literal recovery of H, rather than only isomorphism or entailment equivalence.

The semantic proof starts with any simple interpretation and assignment satisfying G. It retains IR, IP, IEXT and IL, changing IS only at generated names to use the original blank witnesses. An arbitrary fallback resource handles unused ambient blanks; truth guarantees actual witnesses for the occurring ones. This interpretation satisfies sk(G), so the assumed entailment supplies witnesses for H. Combining original and conclusion assignments on the two blank copies makes the lifted H true in the original interpretation.

This semantic argument works for generalized graphs, different blank domains and infinite graphs. It requires no `Avoids H` condition: H may mention generated IRIs. It does not assume IP is a subset of IR, change partial literal denotation, or claim preservation of datatype/RDF/RDFS extension conditions.

Ordinary syntax is proved separately. In the canonical interpretation, a fixed IRI predicate in an entailed triple must occur as a predicate in the premise. Ordinary source predicates are unchanged by Skolemization and cannot be generated names because of freshness. Inverse lifting therefore retains an IRI predicate, while ordinary subject categories are preserved directly.

`ordinary_exact_lifting` constructs an ordinary H-prime, proves that G simply entails it, proves that every left-copy blank comes from an occurring blank in G, and proves that reapplication gives H exactly. `Statements.skolemization_lifting_lemma` is a one-line alias of that full result. Conservativity remains a separate alias and proof.

## Source-review questions

`Q-SKOLEM-LIFTING-BLANK-SCOPE` asks whether the source's strict equation presumes standardization apart or the convention of treating isomorphic graphs alike. The explicit separate-copy construction avoids capture without requiring disjoint inputs. Its reapplication operation must not be conflated with the ambient-total substitution.

`Q-SKOLEM-PROOF-COMMUTATION` records that disjoint substitution domains alone do not justify the printed commutation: a substitution's output may be a generated IRI subsequently changed by inverse naming. The new proof works directly through interpretations and does not assume that printed step. Neither question is a declared erratum or an accepted expert review.

## Review boundaries

The catalogue now has 165 mappings among 215 preliminary records, including partial mappings. Exact lifting remains a partial source mapping because the interpretation of the printed blank-scope convention awaits review, despite the complete checked theorem for the explicit construction. Thirty-one authored declarations, including the new headline alias, have curated glosses. The short review route remains below 400 lines.

The next unresolved core result is lean/proper-instance non-entailment. The source states it without finiteness, but the printed proper-instance-to-proper-subgraph inference still needs justification. A finite set of occurring blanks supports the usual surjectivity argument; no counterexample to the infinite case has been established. Keep the unrestricted scope open rather than silently adding finiteness.

Concrete syntax and datatype correspondence, remaining semantic/rule-completeness obligations, source-accountability acceptance, expert reviews and all package/JS/WASM refinement remain outstanding. Full coverage is not claimed.

## Deliberate registry audit

The registry adds 72 declarations: 31 authored declarations and 41 generated helpers. Existing declaration types and kinds are unchanged. The compiler attributes three existing Subject/Triple reduction equations to SkolemLifting because the equations are now requested there earlier in the import order; the inventory preserves that attribution and their existing parent grounding. New private case helpers retain explicit parents.

The inventory now contains 1,596 local declarations in 54 formal files and a closure through 6,199 declarations. No new foundation modules or logical axioms are introduced. Allowed axioms remain `propext`, `Classical.choice` and `Quot.sound`.

## Validation

The full Lean build and frozen-registry verification pass. All seven rejection checks pass, including rejection of a duplicate-bearing finite enumeration and refusal of a complete-coverage claim. The 15 Python tests, viewer generation, site staging/link checks, JavaScript syntax check and methodology-skill validation pass. The three-file reviewer route is 365 lines.

The browser suite adds four checks for the exact headline/equality and gloss, interpretation transfer, the ambient-total naming distinction, and the source questions/corrected premise. Its configured total is 53 checks; Pages deployment requires the Chromium job to pass. Compilation and these checks do not accept the source mapping or either expert-review stage.
