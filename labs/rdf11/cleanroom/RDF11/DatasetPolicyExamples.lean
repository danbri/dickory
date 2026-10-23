/-
Derived guard for Semantics §10's optional policies: adding a dataset-dependent
truth condition differs from restricting models while preserving truth.
Both example policies retain default content, yet their entailments differ.
-/
import RDF11.DatasetPolicies

namespace RDF11.DatasetPolicyExample

def nameRequired (n : Iri) : DatasetRegime Iri Literal B
    (Sigma fun U : Type u => SimpleInterpretation Iri Literal U) where
  Satisfies := fun m D => DatasetRegime.simpleDefault.Satisfies m D ∧ D.HasName (.iri n)

theorem nameRequired_includes_default (n : Iri) :
    (nameRequired n : DatasetRegime Iri Literal B _).IncludesDefault
      (fun m => m.1) (fun m => m.2) := fun _ _ h => h.1

theorem nameRequired_isomorphism_invariant (n : Iri) {D E : Dataset Iri Literal B}
    (e : DatasetIsomorphism D E)
    (m : Sigma fun U : Type u => SimpleInterpretation Iri Literal U) :
    (nameRequired n).Satisfies m D ↔ (nameRequired n).Satisfies m E :=
  and_congr (DatasetRegime.simpleDefault_isomorphism_invariant e m) (e.iri_name_present_iff n)

theorem default_only_entails_absent (n : GraphName Iri B) :
    DatasetRegime.simpleDefault.{u}.Entails (Dataset.emptyNamed n : Dataset Iri Literal B)
      Dataset.empty := by
  intro m _
  change m.2.Satisfies (Graph.generalize (Set.empty : Graph Iri Literal B))
  rw [Graph.generalize_empty]
  exact m.2.satisfies_empty

theorem nameRequired_not_entails_absent (n : Iri) :
    ¬ (nameRequired.{u} n).Entails (Dataset.emptyNamed (.iri n) : Dataset Iri Literal B)
      Dataset.empty := by
  intro h
  have hp : (nameRequired.{u} n).Satisfies ⟨ULift.{u} Unit, indiscriminate⟩
      (Dataset.emptyNamed (.iri n) : Dataset Iri Literal B) := by
    refine ⟨?_, ⟨Set.empty, Dataset.emptyNamed_present (.iri n)⟩⟩
    change indiscriminate.Satisfies (Graph.generalize (Set.empty : Graph Iri Literal B))
    rw [Graph.generalize_empty]
    exact indiscriminate.satisfies_empty
  obtain ⟨G, hG⟩ := (h _ hp).2
  cases hG

end RDF11.DatasetPolicyExample
