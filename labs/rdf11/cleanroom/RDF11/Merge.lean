/-
RDF 1.1 Semantics §4.1, §5.1.1.
A binary merge uses disjoint copies of the two blank-node domains.
An ordinary union keeps their identities. These are different operations.
-/
import RDF11.Entailment

namespace RDF11

namespace SimpleInterpretation

theorem denote_mapBlank (I : SimpleInterpretation Iri Literal U)
    (f : B₁ → B₂) (A : I.Assignment B₂) (t : Term Iri Literal B₁) :
    I.denote A (t.mapBlank f) = I.denote (A ∘ f) t := by
  cases t <;> rfl

theorem tripleTrue_mapBlank (I : SimpleInterpretation Iri Literal U)
    (f : B₁ → B₂) (A : I.Assignment B₂) (t : GeneralizedTriple Iri Literal B₁) :
    I.TripleTrue A (t.mapBlank f) ↔ I.TripleTrue (A ∘ f) t := by
  simp only [TripleTrue, GeneralizedTriple.mapBlank, denote_mapBlank]

theorem graphTrue_mapBlank (I : SimpleInterpretation Iri Literal U)
    (f : B₁ → B₂) (A : I.Assignment B₂) (G : GeneralizedGraph Iri Literal B₁) :
    I.GraphTrue A (G.mapBlank f) ↔ I.GraphTrue (A ∘ f) G := by
  constructor
  · intro h t ht
    exact (I.tripleTrue_mapBlank f A t).mp (h _ ⟨t, ht, rfl⟩)
  · rintro h _ ⟨t, ht, rfl⟩
    exact (I.tripleTrue_mapBlank f A t).mpr (h t ht)

theorem satisfies_mapBlank_implies (I : SimpleInterpretation Iri Literal U)
    (f : B₁ → B₂) (G : GeneralizedGraph Iri Literal B₁)
    (h : I.Satisfies (G.mapBlank f)) : I.Satisfies G := by
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp h
  exact (I.satisfies_iff_exists_graphTrue G).mpr
    ⟨A ∘ f, (I.graphTrue_mapBlank f A G).mp hA⟩

theorem graphTrue_union (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (G H : GeneralizedGraph Iri Literal B) :
    I.GraphTrue A (Set.union G H) ↔ I.GraphTrue A G ∧ I.GraphTrue A H := by
  constructor
  · exact fun h => ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨hG, hH⟩ t (ht | ht)
    · exact hG t ht
    · exact hH t ht

end SimpleInterpretation

def merge (G : GeneralizedGraph Iri Literal B₁) (H : GeneralizedGraph Iri Literal B₂) :
    GeneralizedGraph Iri Literal (Sum B₁ B₂) :=
  Set.union (G.mapBlank Sum.inl) (H.mapBlank Sum.inr)

theorem satisfies_merge (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal B₁) (H : GeneralizedGraph Iri Literal B₂) :
    I.Satisfies (merge G H) ↔ I.Satisfies G ∧ I.Satisfies H := by
  constructor
  · intro h
    have hG := I.satisfies_subgraph (fun _ ht => Or.inl ht) h
    have hH := I.satisfies_subgraph (fun _ ht => Or.inr ht) h
    exact ⟨I.satisfies_mapBlank_implies Sum.inl G hG,
      I.satisfies_mapBlank_implies Sum.inr H hH⟩
  · rintro ⟨hG, hH⟩
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
    obtain ⟨B, hB⟩ := (I.satisfies_iff_exists_graphTrue H).mp hH
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨Sum.elim A B, ?_⟩
    apply (I.graphTrue_union _ _ _).mpr
    constructor
    · exact (I.graphTrue_mapBlank Sum.inl _ G).mpr hA
    · exact (I.graphTrue_mapBlank Sum.inr _ H).mpr hB

theorem union_entails_merge (G H : GeneralizedGraph Iri Literal B) :
    SimplyEntails.{u} (Set.union G H) (merge G H) := by
  intro U I h
  apply (satisfies_merge I G H).mpr
  exact ⟨I.satisfies_subgraph (fun _ ht => Or.inl ht) h,
    I.satisfies_subgraph (fun _ ht => Or.inr ht) h⟩

theorem renamed_entails_original (f : B₁ → B₂)
    (G : GeneralizedGraph Iri Literal B₁) : SimplyEntails.{u} (G.mapBlank f) G :=
  fun _ I => I.satisfies_mapBlank_implies f G

end RDF11

