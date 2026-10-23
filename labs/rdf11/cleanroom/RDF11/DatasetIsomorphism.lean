/-
RDF 1.1 Concepts §4.1: one global renaming, including blank graph names.
The maps extend the source bijection to the ambient blank type. Their inverse
laws concern only occurring blanks, not unused ambient identities.
Pair preservation in both directions includes present empty named graphs.
-/
import RDF11.Datasets

namespace RDF11

structure DatasetIsomorphism (D E : Dataset Iri Literal B) where
  toFun : B → B
  invFun : B → B
  left_inv : ∀ b, D.hasBlank b → invFun (toFun b) = b
  right_inv : ∀ b, E.hasBlank b → toFun (invFun b) = b
  default_eq : D.defaultGraph.mapBlank toFun = E.defaultGraph
  named_forward : ∀ n G, D.HasNamedGraph n G →
    E.HasNamedGraph (n.mapBlank toFun) (G.mapBlank toFun)
  named_backward : ∀ n G, E.HasNamedGraph n G →
    D.HasNamedGraph (n.mapBlank invFun) (G.mapBlank invFun)

namespace DatasetIsomorphism

def default_isomorphism {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E) :
    GraphIsomorphism D.defaultGraph.generalize E.defaultGraph.generalize where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := fun b hb => e.left_inv b (Or.inl hb)
  right_inv := fun b hb => e.right_inv b (Or.inl hb)
  image_eq := (D.defaultGraph.generalize_mapBlank e.toFun).symm.trans
    (congrArg Graph.generalize e.default_eq)

theorem inverse_default {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E) :
    E.defaultGraph.mapBlank e.invFun = D.defaultGraph := by
  apply Graph.generalize_injective
  rw [Graph.generalize_mapBlank]
  exact e.default_isomorphism.inverse_image

def symm {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E) :
    DatasetIsomorphism E D where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  default_eq := e.inverse_default
  named_forward := e.named_backward
  named_backward := e.named_forward

theorem maps_blank {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (b : B) (hb : D.hasBlank b) : E.hasBlank (e.toFun b) := by
  rcases hb with hd | ⟨n, G, hn, hb | hb⟩
  · left
    rw [← e.default_eq, Graph.generalize_mapBlank]
    exact (D.defaultGraph.generalize.hasBlank_mapBlank e.toFun _).mpr ⟨b, hd, rfl⟩
  · right
    refine ⟨n.mapBlank e.toFun, G.mapBlank e.toFun, e.named_forward n G hn, Or.inl ?_⟩
    rw [Subject.toTerm_mapBlank]
    exact (n.toTerm.hasBlank_mapBlank e.toFun _).mpr ⟨b, hb, rfl⟩
  · right
    refine ⟨n.mapBlank e.toFun, G.mapBlank e.toFun, e.named_forward n G hn, Or.inr ?_⟩
    rw [Graph.generalize_mapBlank]
    exact (G.generalize.hasBlank_mapBlank e.toFun _).mpr ⟨b, hb, rfl⟩

theorem injective_on_blanks {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (b c : B) (hb : D.hasBlank b) (hc : D.hasBlank c) (h : e.toFun b = e.toFun c) :
    b = c := (e.left_inv b hb).symm.trans ((congrArg e.invFun h).trans (e.left_inv c hc))

theorem surjective_on_blanks {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (b : B) (hb : E.hasBlank b) : ∃ a, D.hasBlank a ∧ e.toFun a = b :=
  ⟨e.invFun b, e.symm.maps_blank b hb, e.right_inv b hb⟩

def refl (D : Dataset Iri Literal B) : DatasetIsomorphism D D where
  toFun := id
  invFun := id
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl
  default_eq := D.defaultGraph.mapBlank_id
  named_forward := by intro n G h; simpa only [Subject.mapBlank_id, Graph.mapBlank_id] using h
  named_backward := by intro n G h; simpa only [Subject.mapBlank_id, Graph.mapBlank_id] using h

def trans {D E F : Dataset Iri Literal B}
    (e : DatasetIsomorphism D E) (h : DatasetIsomorphism E F) : DatasetIsomorphism D F where
  toFun := h.toFun ∘ e.toFun
  invFun := e.invFun ∘ h.invFun
  left_inv := by
    intro b hb
    simp only [Function.comp_apply, h.left_inv _ (e.maps_blank b hb), e.left_inv b hb]
  right_inv := by
    intro b hb
    have he : E.hasBlank (h.invFun b) := h.symm.maps_blank b hb
    change h.toFun (e.toFun (e.invFun (h.invFun b))) = b
    rw [e.right_inv _ he, h.right_inv b hb]
  default_eq := by rw [← Graph.mapBlank_comp, e.default_eq, h.default_eq]
  named_forward := by
    intro n G hn
    simpa only [Subject.mapBlank_comp, Graph.mapBlank_comp] using
      h.named_forward _ _ (e.named_forward n G hn)
  named_backward := by
    intro n G hn
    simpa only [Subject.mapBlank_comp, Graph.mapBlank_comp] using
      e.named_backward _ _ (h.named_backward n G hn)

/-- The source's iff ranges over nodes and graphs in the domain of its bijection. -/
theorem named_iff {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (n : GraphName Iri B) (G : Graph Iri Literal B)
    (hn : ∀ b, (n.toTerm : Term Iri Literal B).hasBlank b → D.hasBlank b)
    (hG : ∀ b, G.generalize.hasBlank b → D.hasBlank b) :
    D.HasNamedGraph n G ↔ E.HasNamedGraph (n.mapBlank e.toFun) (G.mapBlank e.toFun) := by
  constructor
  · exact e.named_forward n G
  · intro h
    have back := e.named_backward _ _ h
    have hnfix := Subject.mapBlank_of_fixes (e.invFun ∘ e.toFun) n
      (fun b hb => e.left_inv b (hn b hb))
    have hGfix := Graph.mapBlank_of_fixes (e.invFun ∘ e.toFun) G
      (fun b hb => e.left_inv b (hG b hb))
    rw [Subject.mapBlank_comp, Graph.mapBlank_comp, hnfix, hGfix] at back
    exact back

def named_isomorphism {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (n : GraphName Iri B) (G : Graph Iri Literal B) (hn : D.HasNamedGraph n G) :
    GraphIsomorphism G.generalize (G.mapBlank e.toFun).generalize where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := fun b hb => e.left_inv b (Or.inr ⟨n, G, hn, Or.inr hb⟩)
  right_inv := fun b hb => e.right_inv b
    (Or.inr ⟨n.mapBlank e.toFun, G.mapBlank e.toFun, e.named_forward n G hn, Or.inr hb⟩)
  image_eq := (G.generalize_mapBlank e.toFun).symm

theorem default_equivalent {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E) :
    LogicallyEquivalent.{u} D.defaultGraph.generalize E.defaultGraph.generalize :=
  e.default_isomorphism.equivalent

theorem named_equivalent {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (n : GraphName Iri B) (G : Graph Iri Literal B) (hn : D.HasNamedGraph n G) :
    LogicallyEquivalent.{u} G.generalize (G.mapBlank e.toFun).generalize :=
  (e.named_isomorphism n G hn).equivalent

theorem iri_name_present_iff {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (n : Iri) : D.HasName (.iri n) ↔ E.HasName (.iri n) := by
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨G.mapBlank e.toFun, e.named_forward (.iri n) G hG⟩
  · rintro ⟨G, hG⟩
    exact ⟨G.mapBlank e.invFun, e.named_backward (.iri n) G hG⟩

end DatasetIsomorphism
end RDF11
