# Review question: instances and generalized predicates

**Status:** Lean countermodel checked; source scope and mapping fidelity await expert review. This is not a declared W3C erratum.

The literal combination of three passages needs attention before we assert the full generalized instance/interpolation consequence:

1. Semantics §4 applies the definitions unchanged to generalized RDF triples and graphs.
2. §5 permits IP elements outside IR; §5.1 maps blank nodes into IR.
3. §5.3 states that a graph is simply entailed by any of its instances. Appendix C constructs a blank-node assignment using the denotation of the substituted term.

Take distinct IRIs s and p. Use resources IR = {r}, properties IP = {q}, r ≠ q, IS(s) = r, IS(p) = q, and IEXT(q) = {⟨r,r⟩}. Map every other IRI to r; IL may be everywhere undefined. This is a simple interpretation under the currently transcribed conditions.

| Graph | Truth in that interpretation |
|---|---|
| `s p s .` | True: p denotes q and ⟨r,r⟩ belongs to IEXT(q). |
| `s _:b s .` | False: A(b) must belong to IR, so cannot be the sole property q. |

The first singleton is obtained from the second by substituting p for its blank node. Nevertheless it does not simply entail the second under this reading.

[GeneralizedScope.lean](../RDF11/GeneralizedScope.lean) checks the countermodel for arbitrary IRI and literal domains with two distinct IRIs and decidable IRI equality. It interprets every IRI; it is not a restriction to a two-name vocabulary. The general instance relation is still open, so the specific substitution is displayed directly rather than certified by an already completed Instance predicate.

**The ordinary RDF consequence is not refuted:** ordinary predicates are IRIs, and blank nodes occur only where truth forces resource denotations.

The source’s wording, intended scope, incorporated Concepts definitions and any relevant errata need expert adjudication. Until then, we keep this question explicit and leave the general instance/interpolation mapping open. Imposing IP ⊆ IR or changing blank-node assignment codomains would change the formalized conditions and cannot be used as an unannounced repair.

[catalogue/open-questions.json](../catalogue/open-questions.json) links the claims, character-range passage records and Lean declarations.

