/-
An executable simple-entailment decision for finite inputs and an ordinary
conclusion. The instance search itself accepts generalized syntax; its positive
simple-semantic interpretation retains the existing ordinary-conclusion bound.
Separate input blank domains are embedded explicitly, with truth preservation.
-/
import RDF11.InstanceSearch
import RDF11.Datasets

namespace RDF11.InstanceSearch

variable {Iri Literal B B₁ B₂ : Type} {U : Type u}

theorem singleton_list (t : α) : Set.ofList [t] = Set.singleton t := by
  apply Set.ext
  intro x
  simp [Set.ofList, Set.singleton]

theorem generalize_list (E : List (Triple Iri Literal B)) :
    Set.ofList (E.map Triple.generalize) = Graph.generalize (Set.ofList E) := by
  apply Set.ext
  intro t
  simp [Graph.generalize, Set.ofList, Set.image]

theorem mapBlank_list (G : List (GeneralizedTriple Iri Literal B₁)) (f : B₁ → B₂) :
    Set.ofList (G.map (GeneralizedTriple.mapBlank f)) =
      GeneralizedGraph.mapBlank f (Set.ofList G) := by
  apply Set.ext
  intro t
  simp [GeneralizedGraph.mapBlank, Set.ofList, Set.image]

theorem ordinary_mapBlank_list (E : List (Triple Iri Literal B₁)) (f : B₁ → B₂) :
    Set.ofList (E.map (Triple.mapBlank f)) = Graph.mapBlank f (Set.ofList E) := by
  apply Set.ext
  intro t
  simp [Graph.mapBlank, Set.ofList, Set.image]

theorem satisfies_left (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal B₁) :
    I.Satisfies (G.mapBlank (Sum.inl : B₁ → Sum B₁ B₂)) ↔ I.Satisfies G := by
  constructor
  · exact I.satisfies_mapBlank_implies _ _
  · intro h
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp h
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    exact ⟨Sum.elim A (fun _ => none), (I.graphTrue_mapBlank _ _ G).mpr hA⟩

theorem satisfies_right (I : SimpleInterpretation Iri Literal U)
    (E : GeneralizedGraph Iri Literal B₂) :
    I.Satisfies (E.mapBlank (Sum.inr : B₂ → Sum B₁ B₂)) ↔ I.Satisfies E := by
  constructor
  · exact I.satisfies_mapBlank_implies _ _
  · intro h
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue E).mp h
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    exact ⟨Sum.elim (fun _ => none) A, (I.graphTrue_mapBlank _ _ E).mpr hA⟩

theorem entailment_apart_iff (G : GeneralizedGraph Iri Literal B₁)
    (E : GeneralizedGraph Iri Literal B₂) :
    SimplyEntails.{u} (G.mapBlank (Sum.inl : B₁ → Sum B₁ B₂))
      (E.mapBlank (Sum.inr : B₂ → Sum B₁ B₂)) ↔ SimplyEntails.{u} G E := by
  constructor
  · intro h U I hG
    exact (satisfies_right I E).mp (h U I ((satisfies_left I G).mpr hG))
  · intro h U I hG
    exact (satisfies_right I E).mpr (h U I ((satisfies_left I G).mp hG))

theorem ordinary_interpolation_apart (G : GeneralizedGraph Iri Literal B₁)
    (E : Graph Iri Literal B₂) :
    SimplyEntails.{u} G E.generalize ↔
      ∃ μ, Set.subset ((E.generalize.mapBlank (Sum.inr : B₂ → Sum B₁ B₂)).substitute μ)
        (G.mapBlank Sum.inl) := by
  rw [← entailment_apart_iff G E.generalize, ← Graph.generalize_mapBlank,
    ordinary_interpolation]

variable [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B]

def ordinaryCheck (G : List (GeneralizedTriple Iri Literal B))
    (E : List (Triple Iri Literal B)) : Bool := check G (E.map Triple.generalize)

theorem ordinaryCheck_iff (G : List (GeneralizedTriple Iri Literal B))
    (E : List (Triple Iri Literal B)) :
    ordinaryCheck G E = true ↔ SimplyEntails.{u} (Set.ofList G) (Graph.generalize (Set.ofList E)) := by
  rw [ordinaryCheck, check_iff, ordinary_interpolation, ← generalize_list E]

def ordinaryDecision (G : List (GeneralizedTriple Iri Literal B))
    (E : List (Triple Iri Literal B)) :
    Decidable (SimplyEntails.{u} (Set.ofList G) (Graph.generalize (Set.ofList E))) :=
  decidable_of_iff (ordinaryCheck G E = true) (ordinaryCheck_iff G E)

theorem negative_countermodel (G E : List (GeneralizedTriple Iri Literal B))
    (h : check G E = false) :
    (Herbrand.interpretation.{u} (Set.ofList G)).Satisfies (Set.ofList G) ∧
      ¬ (Herbrand.interpretation.{u} (Set.ofList G)).Satisfies (Set.ofList E) := by
  refine ⟨Herbrand.satisfies _, ?_⟩
  intro he
  obtain ⟨A, hA⟩ := ((Herbrand.interpretation (Set.ofList G)).satisfies_iff_exists_graphTrue _).mp he
  have hc : check G E = true := (check_iff G E).mpr ⟨Herbrand.substitution (Set.ofList G) A, ?_⟩
  · rw [h] at hc
    contradiction
  · rintro _ ⟨t, ht, rfl⟩
    exact Herbrand.true_triple_decodes (Set.ofList G) A t (hA t ht)

theorem negative_not_entails (G E : List (GeneralizedTriple Iri Literal B))
    (h : check G E = false) : ¬ SimplyEntails.{u} (Set.ofList G) (Set.ofList E) := by
  intro he
  obtain ⟨hs, hn⟩ := negative_countermodel.{u} G E h
  exact hn (he _ _ hs)

omit [DecidableEq B] in
def apartCheck [DecidableEq B₁] [DecidableEq B₂]
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (Triple Iri Literal B₂)) : Bool :=
  ordinaryCheck (G.map (GeneralizedTriple.mapBlank Sum.inl)) (E.map (Triple.mapBlank Sum.inr))

omit [DecidableEq B] in
theorem apartCheck_iff [DecidableEq B₁] [DecidableEq B₂]
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (Triple Iri Literal B₂)) :
    apartCheck G E = true ↔ SimplyEntails.{u} (Set.ofList G) (Graph.generalize (Set.ofList E)) := by
  rw [apartCheck, ordinaryCheck_iff, mapBlank_list, ordinary_mapBlank_list,
    Graph.generalize_mapBlank, entailment_apart_iff]

omit [DecidableEq B] in
def apartDecision [DecidableEq B₁] [DecidableEq B₂]
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (Triple Iri Literal B₂)) :
    Decidable (SimplyEntails.{u} (Set.ofList G) (Graph.generalize (Set.ofList E))) :=
  decidable_of_iff (apartCheck G E = true) (apartCheck_iff G E)

end RDF11.InstanceSearch
