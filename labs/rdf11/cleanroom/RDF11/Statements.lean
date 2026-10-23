import RDF11.FiniteInstances
import RDF11.SkolemLifting

/-!
# Headline statements for RDF 1.1 Semantics review

Read this file with Syntax.lean and Simple.lean. Each declaration below is
only an alias: its proof and precise type come from the named theorem.
Hover or #check an alias to see the elaborated statement; the source viewer
also shows its type, English gloss and dependency link to the proof.

Only interpolation and compactness are explicitly named in the source.
The other headings are local review names for the cited statements.
These are review entry points, not a claim that every scope in the document
has been discharged. Ordinary/generalized syntax, finite conclusions and
freshness assumptions are retained exactly. No new axioms or proofs occur here.
-/
namespace RDF11.Statements

universe u
variable {Iri Literal B B₁ B₂ : Type} {U : Type u} {datatype : Literal → Iri}

/-- Empty graph lemma: the empty graph simply entails only the empty graph.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties
The companion alias below records that every graph entails the empty graph. -/
theorem empty_graph_lemma (E : GeneralizedGraph Iri Literal B₂) (h : SimplyEntails.{u} (Set.empty : GeneralizedGraph Iri Literal B₁) E) : E = Set.empty := RDF11.empty_entails_only_empty E h

/-- Empty graph lemma, other clause: every graph simply entails the empty graph.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties -/
theorem empty_graph_is_entailed (G : GeneralizedGraph Iri Literal B₁) : SimplyEntails.{u} G (Set.empty : GeneralizedGraph Iri Literal B₂) := RDF11.entails_empty G

/-- Subgraph lemma: every graph simply entails each of its subgraphs.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties -/
theorem subgraph_lemma {G E : GeneralizedGraph Iri Literal B} (h : Set.subset E G) : SimplyEntails.{u} G E := RDF11.subgraph_entailment h

/-- Instance lemma: an instance simply entails its original ordinary RDF graph.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties
Both graphs here are ordinary; unrestricted generalized scope remains under review. -/
theorem instance_lemma {G H : Graph Iri Literal B} (h : IsInstance H.generalize G.generalize) : SimplyEntails.{u} H.generalize G.generalize := RDF11.ordinary_instance_entails h

/-- Lean/proper-instance consequence, proved for finite occurring blank support.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties
The source states this without finiteness; its unrestricted scope remains open.
This proof permits generalized syntax and does not require finitely many triples. -/
theorem lean_proper_instance_finite_blank_lemma (G H : GeneralizedGraph Iri Literal B) (hl : LeanGraph G) (hf : FiniteBlankSupport G) (hp : ProperInstance H G) : ¬ SimplyEntails.{u} G H := RDF11.lean_finite_blanks_not_entails_proper_instance G H hl hf hp

/-- Merging lemma, binary model form: an interpretation satisfies the merge
exactly when it satisfies both inputs separately. Blank domains are disjoint.
§4.1 / §5.1.1 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#unions_merges
This alias does not claim the arbitrary-family formulation. -/
theorem merging_lemma (I : SimpleInterpretation Iri Literal U) (G : GeneralizedGraph Iri Literal B₁) (H : GeneralizedGraph Iri Literal B₂) : I.Satisfies (merge G H) ↔ I.Satisfies G ∧ I.Satisfies H := RDF11.satisfies_merge I G H

/-- Interpolation lemma: G simply entails ordinary E exactly when a subgraph
of G is an instance of E. G may be generalized; neither graph need be finite.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#dfn-interpolation -/
theorem interpolation_lemma (G : GeneralizedGraph Iri Literal B) (E : Graph Iri Literal B) : SimplyEntails.{u} G E.generalize ↔ ∃ H, IsInstance H E.generalize ∧ Set.subset H G := RDF11.ordinary_interpolation_instances G E

/-- Compactness: if G entails finite ordinary E, some finite subgraph of G
already entails E. Finiteness is witnessed by an exact, duplicate-free enumeration.
§5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#simple_entailment_properties -/
theorem compactness (G : GeneralizedGraph Iri Literal B) (E : Graph Iri Literal B) (hE : FiniteGraph E.generalize) (h : SimplyEntails.{u} G E.generalize) : ∃ H, Set.subset H G ∧ FiniteGraph H ∧ SimplyEntails.{u} H E.generalize := RDF11.simple_compactness G E hE h

/-- Isomorphism invariance: isomorphic graphs satisfy exactly the same
interpretations. Renamings are inverse on occurring blanks and fix all names.
§4 and §5.3 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#notation -/
theorem isomorphism_invariance {G H : GeneralizedGraph Iri Literal B} (e : GraphIsomorphism G H) (I : SimpleInterpretation Iri Literal U) : I.Satisfies G ↔ I.Satisfies H := RDF11.GraphIsomorphism.satisfies_iff e I

/-- Skolemization lemma, fresh-vocabulary conservativity: sk(G) entails H
exactly when G entails H, for ordinary G and H avoiding the fresh Skolem IRIs.
§6 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#skolemization
Freshness includes datatype IRIs; exact lifting is stated separately below. -/
theorem skolemization_lemma (G H : Graph Iri Literal B) (sk : Skolemization datatype G.generalize) (hf : sk.Avoids H.generalize) : SimplyEntails.{u} sk.graph H.generalize ↔ SimplyEntails.{u} G.generalize H.generalize := RDF11.Skolemization.conservative G H sk hf

/-- Skolemization lemma, exact lifting with separate copies of input blanks.
§6 https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/#skolemization
Reapply original names on the left; preserve conclusion blanks on the right.
No finiteness or fresh-vocabulary condition on H is required. -/
theorem skolemization_lifting_lemma (G : Graph Iri Literal B₁) (H : Graph Iri Literal B₂) (sk : Skolemization datatype G.generalize) (h : SimplyEntails.{u} sk.graph H.generalize) : ∃ H' : Graph Iri Literal (Sum B₁ B₂), SimplyEntails.{u} G.generalize H'.generalize ∧ (∀ b, H'.generalize.hasBlank (.inl b) → G.generalize.hasBlank b) ∧ Set.image sk.applyLiftedTriple H'.generalize = H.generalize := RDF11.Skolemization.ordinary_exact_lifting G sk H h

end RDF11.Statements
