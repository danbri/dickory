/-
RDF 1.1 Semantics §5.3: compactness for a finite conclusion.
The existing certified Enumeration supplies finiteness, exact membership and
uniqueness. No finiteness assumption is made about the premise graph.
-/
import RDF11.Interpolation
import RDF11.Enumeration

namespace RDF11
namespace Enumeration

/-- A finite set image has a certified enumeration, even when f identifies elements. -/
noncomputable def image (f : α → β) (e : Enumeration G) : Enumeration (Set.image f G) := by
  classical
  let result := fromList (e.triples.map f)
  refine ⟨result.triples, result.nodup, ?_⟩
  intro y
  rw [result.membership]
  change y ∈ e.triples.map f ↔ ∃ x, G x ∧ f x = y
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x, (e.membership x).mp hx, he⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨x, (e.membership x).mpr hx, he⟩

end Enumeration

/-- Finiteness is existence of a membership-faithful, duplicate-free enumeration. -/
def FiniteGraph (G : GeneralizedGraph Iri Literal B) : Prop := Nonempty (Enumeration G)

theorem finite_substitution (G : GeneralizedGraph Iri Literal B) (h : FiniteGraph G)
    (μ : Substitution Iri Literal B) : FiniteGraph (G.substitute μ) := by
  obtain ⟨e⟩ := h
  exact ⟨e.image (GeneralizedTriple.substitute μ)⟩

/-- Interpolation chooses a finite instance of E inside G as the finite premise. -/
theorem simple_compactness (G : GeneralizedGraph Iri Literal B) (E : Graph Iri Literal B)
    (hE : FiniteGraph E.generalize) (h : SimplyEntails.{u} G E.generalize) :
    ∃ H, Set.subset H G ∧ FiniteGraph H ∧ SimplyEntails.{u} H E.generalize := by
  obtain ⟨μ, hμ⟩ := (ordinary_interpolation G E).mp h
  exact ⟨E.generalize.substitute μ, hμ, finite_substitution _ hE μ,
    ordinary_substitution_entails E μ⟩

end RDF11
