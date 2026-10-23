/-
RDF 1.1 Semantics §5.3: simple entailment cannot introduce an absent IRI.
The stronger name-vocabulary inclusion follows from interpolation's necessary
direction, and is reused by skolemization non-entailment.
-/
import RDF11.Interpolation
import RDF11.Vocabulary

namespace RDF11

theorem Term.names_substitute (datatype : Literal → Iri) (μ : Substitution Iri Literal B)
    (q : Term Iri Literal B) (n : Name Iri Literal) (hn : q.names datatype n) :
    (q.substitute μ).names datatype n := by
  cases q with
  | iri _ => exact hn
  | literal _ => exact hn
  | blank _ => exact False.elim hn

theorem vocabulary_substitution (datatype : Literal → Iri) (G : GeneralizedGraph Iri Literal B)
    (μ : Substitution Iri Literal B) : Set.subset (G.vocabulary datatype) ((G.substitute μ).vocabulary datatype) := by
  rintro n ⟨t, ht, hn⟩
  refine ⟨t.substitute μ, ⟨t, ht, rfl⟩, ?_⟩
  rcases hn with h | h | h
  · exact Or.inl (t.subject.names_substitute datatype μ n h)
  · exact Or.inr (Or.inl (t.predicate.names_substitute datatype μ n h))
  · exact Or.inr (Or.inr (t.object.names_substitute datatype μ n h))

theorem vocabulary_subset (datatype : Literal → Iri) {G H : GeneralizedGraph Iri Literal B}
    (h : Set.subset H G) : Set.subset (H.vocabulary datatype) (G.vocabulary datatype) := by
  rintro n ⟨t, ht, hn⟩
  exact ⟨t, h t ht, hn⟩

theorem entailment_vocabulary (datatype : Literal → Iri) {G E : GeneralizedGraph Iri Literal B}
    (h : SimplyEntails.{u} G E) : Set.subset (E.vocabulary datatype) (G.vocabulary datatype) := by
  obtain ⟨μ, hμ⟩ := entailment_has_instance_subgraph h
  exact Set.subset_trans (vocabulary_substitution datatype E μ) (vocabulary_subset datatype hμ)

theorem fresh_iri_nonentailment (datatype : Literal → Iri) (G E : GeneralizedGraph Iri Literal B)
    (i : Iri) (hG : ¬ G.vocabulary datatype (.inl i)) (hE : E.vocabulary datatype (.inl i)) :
    ¬ SimplyEntails.{u} G E := fun h => hG (entailment_vocabulary datatype h _ hE)

end RDF11
