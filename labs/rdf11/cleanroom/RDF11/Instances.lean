/-
RDF 1.1 Semantics §4, §5.3: instances, isomorphism and lean graphs.
Partial substitutions share an ambient blank identity domain. Replacement is
simultaneous; names stay fixed. Semantic instance entailment below has an
ORDINARY source graph; no IP ⊆ IR assumption is added.
-/
import RDF11.Merge

namespace RDF11

abbrev Substitution (Iri Literal B : Type) := B → Option (Term Iri Literal B)

def Substitution.resolve (μ : Substitution Iri Literal B) (b : B) : Term Iri Literal B :=
  (μ b).getD (.blank b)

def Term.substitute (μ : Substitution Iri Literal B) : Term Iri Literal B → Term Iri Literal B
  | .iri i => .iri i
  | .literal l => .literal l
  | .blank b => μ.resolve b

def GeneralizedTriple.substitute (μ : Substitution Iri Literal B)
    (t : GeneralizedTriple Iri Literal B) : GeneralizedTriple Iri Literal B :=
  ⟨t.subject.substitute μ, t.predicate.substitute μ, t.object.substitute μ⟩

def GeneralizedGraph.substitute (μ : Substitution Iri Literal B)
    (G : GeneralizedGraph Iri Literal B) : GeneralizedGraph Iri Literal B :=
  Set.image (GeneralizedTriple.substitute μ) G

def IsInstance (H G : GeneralizedGraph Iri Literal B) : Prop :=
  ∃ μ, H = G.substitute μ

/-- Only names introduced by substitution must lie in V; existing names stay fixed. -/
def InstanceWithVocabulary (V : Set (Sum Iri Literal))
    (H G : GeneralizedGraph Iri Literal B) : Prop :=
  ∃ μ, H = G.substitute μ ∧ ∀ b, G.hasBlank b →
    (∀ i, μ.resolve b = .iri i → V (.inl i)) ∧
    (∀ l, μ.resolve b = .literal l → V (.inr l))

def Substitution.then (μ ν : Substitution Iri Literal B) : Substitution Iri Literal B :=
  fun b => some ((μ.resolve b).substitute ν)

theorem Term.substitute_id (t : Term Iri Literal B) : t.substitute (fun _ => none) = t := by
  cases t <;> rfl

theorem Term.substitute_comp (μ ν : Substitution Iri Literal B) (t : Term Iri Literal B) :
    (t.substitute μ).substitute ν = t.substitute (μ.then ν) := by
  cases t <;> rfl

theorem GeneralizedGraph.substitute_id (G : GeneralizedGraph Iri Literal B) :
    G.substitute (fun _ => none) = G := by
  have ht (t : GeneralizedTriple Iri Literal B) : t.substitute (fun _ => none) = t := by
    cases t
    simp [GeneralizedTriple.substitute, Term.substitute_id]
  apply Set.ext
  intro t
  simp [substitute, Set.image, ht]

theorem GeneralizedGraph.substitute_comp (μ ν : Substitution Iri Literal B)
    (G : GeneralizedGraph Iri Literal B) :
    (G.substitute μ).substitute ν = G.substitute (μ.then ν) := by
  have ht (t : GeneralizedTriple Iri Literal B) :
      (t.substitute μ).substitute ν = t.substitute (μ.then ν) := by
    simp [GeneralizedTriple.substitute, Term.substitute_comp]
  apply Set.ext
  intro t
  constructor
  · rintro ⟨s, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (ht r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.substitute μ, ⟨r, hr, rfl⟩, ht r⟩

theorem instance_refl (G : GeneralizedGraph Iri Literal B) : IsInstance G G :=
  ⟨fun _ => none, G.substitute_id.symm⟩

theorem instance_trans {F G H : GeneralizedGraph Iri Literal B}
    (hHG : IsInstance H G) (hGF : IsInstance G F) : IsInstance H F := by
  obtain ⟨ν, rfl⟩ := hHG
  obtain ⟨μ, rfl⟩ := hGF
  exact ⟨μ.then ν, F.substitute_comp μ ν⟩

theorem instance_triple_origin (μ : Substitution Iri Literal B)
    (G : GeneralizedGraph Iri Literal B) {t : GeneralizedTriple Iri Literal B}
    (ht : G.substitute μ t) : ∃ s, G s ∧ s.substitute μ = t := ht

/-- Properness is tested only on occurring blanks, after resolving omitted replacements. -/
def ProperSubstitution (G : GeneralizedGraph Iri Literal B) (μ : Substitution Iri Literal B) : Prop :=
  (∃ b, G.hasBlank b ∧ ((∃ i, μ.resolve b = .iri i) ∨ (∃ l, μ.resolve b = .literal l))) ∨
  (∃ b c, G.hasBlank b ∧ G.hasBlank c ∧ b ≠ c ∧ μ.resolve b = μ.resolve c)

def ProperInstance (H G : GeneralizedGraph Iri Literal B) : Prop :=
  ∃ μ, H = G.substitute μ ∧ ProperSubstitution G μ

def LeanGraph (G : GeneralizedGraph Iri Literal B) : Prop :=
  ∀ H, IsInstance H G → Set.subset H G → H = G

theorem ground_substitute (G : GeneralizedGraph Iri Literal B) (hG : G.ground)
    (μ : Substitution Iri Literal B) : G.substitute μ = G := by
  have ht (t : GeneralizedTriple Iri Literal B) (h : G t) : t.substitute μ = t := by
    have hn : ∀ b, ¬ t.hasBlank b := fun b hb => hG b ⟨t, h, hb⟩
    have term (q : Term Iri Literal B) (hq : ∀ b, q.hasBlank b → t.hasBlank b) :
        q.substitute μ = q := by
      cases q with
      | iri _ => rfl
      | literal _ => rfl
      | blank b => exact False.elim (hn b (hq b rfl))
    have hs := term t.subject (fun _ hb => Or.inl hb)
    have hp := term t.predicate (fun _ hb => Or.inr (Or.inl hb))
    have ho := term t.object (fun _ hb => Or.inr (Or.inr hb))
    simp [GeneralizedTriple.substitute, hs, hp, ho]
  apply Set.ext
  intro t
  constructor
  · rintro ⟨s, hs, he⟩
    rw [ht s hs] at he
    exact he ▸ hs
  · intro h
    exact ⟨t, h, ht t h⟩

theorem ground_is_lean (G : GeneralizedGraph Iri Literal B) (hG : G.ground) : LeanGraph G := by
  rintro H ⟨μ, rfl⟩ _
  exact ground_substitute G hG μ

theorem GeneralizedGraph.mapBlank_comp (f : B₁ → B₂) (g : B₂ → B₃)
    (G : GeneralizedGraph Iri Literal B₁) :
    (G.mapBlank f).mapBlank g = G.mapBlank (g ∘ f) := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨s, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (r.mapBlank_comp f g).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.mapBlank f, ⟨r, hr, rfl⟩, r.mapBlank_comp f g⟩

theorem GeneralizedGraph.mapBlank_of_fixes (f : B → B) (G : GeneralizedGraph Iri Literal B)
    (hf : ∀ b, G.hasBlank b → f b = b) : G.mapBlank f = G := by
  have ht (t : GeneralizedTriple Iri Literal B) (h : G t) : t.mapBlank f = t := by
    have term (q : Term Iri Literal B) (hq : ∀ b, q.hasBlank b → t.hasBlank b) :
        q.mapBlank f = q := by
      cases q with
      | iri _ => rfl
      | literal _ => rfl
      | blank b => simp [Term.mapBlank, hf b ⟨t, h, hq b rfl⟩]
    have hs := term t.subject (fun _ hb => Or.inl hb)
    have hp := term t.predicate (fun _ hb => Or.inr (Or.inl hb))
    have ho := term t.object (fun _ hb => Or.inr (Or.inr hb))
    simp [GeneralizedTriple.mapBlank, hs, hp, ho]
  apply Set.ext
  intro t
  constructor
  · rintro ⟨s, hs, he⟩
    rw [ht s hs] at he
    exact he ▸ hs
  · intro h
    exact ⟨t, h, ht t h⟩

theorem mapBlank_is_instance (f : B → B) (G : GeneralizedGraph Iri Literal B) :
    IsInstance (G.mapBlank f) G := by
  refine ⟨fun b => some (.blank (f b)), ?_⟩
  have term (q : Term Iri Literal B) :
      q.mapBlank f = q.substitute (fun b => some (.blank (f b))) := by
    cases q <;> rfl
  have triple (t : GeneralizedTriple Iri Literal B) :
      t.mapBlank f = t.substitute (fun b => some (.blank (f b))) := by
    simp [GeneralizedTriple.mapBlank, GeneralizedTriple.substitute, term]
  change Set.image (GeneralizedTriple.mapBlank f) G = _
  rw [funext triple]
  rfl

/-- Inverse laws concern the blank nodes of the graphs, not unused ambient identities. -/
structure GraphIsomorphism (G H : GeneralizedGraph Iri Literal B) where
  toFun : B → B
  invFun : B → B
  left_inv : ∀ b, G.hasBlank b → invFun (toFun b) = b
  right_inv : ∀ b, H.hasBlank b → toFun (invFun b) = b
  image_eq : G.mapBlank toFun = H

theorem GraphIsomorphism.inverse_image {G H : GeneralizedGraph Iri Literal B}
    (e : GraphIsomorphism G H) : H.mapBlank e.invFun = G := by
  calc
    H.mapBlank e.invFun = (G.mapBlank e.toFun).mapBlank e.invFun :=
      congrArg (fun K => K.mapBlank e.invFun) e.image_eq.symm
    _ = G.mapBlank (e.invFun ∘ e.toFun) := G.mapBlank_comp _ _
    _ = G := G.mapBlank_of_fixes _ e.left_inv

theorem GraphIsomorphism.mutual_instances {G H : GeneralizedGraph Iri Literal B}
    (e : GraphIsomorphism G H) : IsInstance H G ∧ IsInstance G H := by
  constructor
  · simpa only [e.image_eq] using mapBlank_is_instance e.toFun G
  · simpa only [e.inverse_image] using mapBlank_is_instance e.invFun H

theorem GraphIsomorphism.satisfies_iff {G H : GeneralizedGraph Iri Literal B}
    (e : GraphIsomorphism G H)
    (I : SimpleInterpretation Iri Literal U) : I.Satisfies G ↔ I.Satisfies H := by
  constructor
  · intro h
    apply I.satisfies_mapBlank_implies e.invFun H
    rwa [e.inverse_image]
  · intro h
    apply I.satisfies_mapBlank_implies e.toFun G
    rwa [e.image_eq]

theorem GraphIsomorphism.equivalent {G H : GeneralizedGraph Iri Literal B}
    (e : GraphIsomorphism G H) : LogicallyEquivalent.{u} G H :=
  ⟨fun _ I => (e.satisfies_iff I).mp, fun _ I => (e.satisfies_iff I).mpr⟩

namespace SimpleInterpretation

/-- Keep a denotation only when it is a resource, as required for a blank assignment. -/
noncomputable def resourceDenote (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (q : Term Iri Literal B) : Option I.Resource := by
  classical
  exact (I.denote A q).bind (fun x => if h : I.IR x then some ⟨x, h⟩ else none)

theorem resourceDenote_of_resource (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (q : Term Iri Literal B) (r : I.Resource)
    (h : I.denote A q = some r.val) : I.resourceDenote A q = some r := by
  simp [resourceDenote, h, r.property]

noncomputable def pullback (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (μ : Substitution Iri Literal B) : I.Assignment B :=
  fun b => I.resourceDenote A (μ.resolve b)

theorem denote_pullback (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (μ : Substitution Iri Literal B)
    (q : Term Iri Literal B) (r : I.Resource)
    (h : I.denote A (q.substitute μ) = some r.val) :
    I.denote (I.pullback A μ) q = some r.val := by
  cases q with
  | iri _ => exact h
  | literal _ => exact h
  | blank b =>
    have hr := I.resourceDenote_of_resource A (μ.resolve b) r h
    simp [denote, pullback, hr]

theorem ordinary_triple_pullback (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (μ : Substitution Iri Literal B) (t : Triple Iri Literal B)
    (h : I.TripleTrue A (t.generalize.substitute μ)) :
    I.TripleTrue (I.pullback A μ) t.generalize := by
  obtain ⟨p, s, o, hp, hs, ho, hext⟩ := h
  exact ⟨p, s, o, hp, I.denote_pullback A μ t.subject.toTerm s hs,
    I.denote_pullback A μ t.object o ho, hext⟩

end SimpleInterpretation

/-- The source graph is ordinary RDF. The image may use generalized syntax. -/
theorem ordinary_substitution_entails (G : Graph Iri Literal B) (μ : Substitution Iri Literal B) :
    SimplyEntails.{u} (G.generalize.substitute μ) G.generalize := by
  intro U I h
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp h
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨I.pullback A μ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact I.ordinary_triple_pullback A μ t (hA _ ⟨t.generalize, ⟨t, ht, rfl⟩, rfl⟩)

/-- Both graphs satisfy the ordinary RDF syntax constraints. -/
theorem ordinary_instance_entails {G H : Graph Iri Literal B}
    (h : IsInstance H.generalize G.generalize) : SimplyEntails.{u} H.generalize G.generalize := by
  obtain ⟨μ, hμ⟩ := h
  rw [hμ]
  exact ordinary_substitution_entails G μ

/-- A subgraph that is also an instance is logically redundant, for ordinary RDF. -/
theorem ordinary_instance_subgraph_equivalent {G H : Graph Iri Literal B}
    (hi : IsInstance H.generalize G.generalize)
    (hs : Set.subset H.generalize G.generalize) :
    LogicallyEquivalent.{u} G.generalize H.generalize :=
  ⟨subgraph_entailment hs, ordinary_instance_entails hi⟩

/-- Sufficient direction of interpolation. Completeness is not asserted. -/
theorem instance_subgraph_entails (G : GeneralizedGraph Iri Literal B) (E : Graph Iri Literal B)
    (μ : Substitution Iri Literal B) (h : Set.subset (E.generalize.substitute μ) G) :
    SimplyEntails.{u} G E.generalize :=
  simplyEntails_trans (subgraph_entailment h) (ordinary_substitution_entails E μ)

end RDF11
