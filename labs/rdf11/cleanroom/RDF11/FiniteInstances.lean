/-
RDF 1.1 Semantics §4 / §5.3 / Appendix C: proper instances and leanness.
The source does not restrict the headline consequence to finite graphs.
We prove the exact self-instance obstruction, then exclude it for finite
occurring blank support. The unrestricted source claim remains open.
-/
import RDF11.FiniteEntailment

namespace RDF11

/-- On an enumerated set, an injective self-map is surjective on that set. -/
theorem Enumeration.injective_surjective {α : Type u} {S : Set α}
    (e : Enumeration S) (f : α → α)
    (hm : ∀ a, S a → S (f a))
    (hi : ∀ a, S a → ∀ b, S b → f a = f b → a = b) :
    ∀ b, S b → ∃ a, S a ∧ f a = b := by
  intro b hb
  classical
  apply Classical.byContradiction
  intro h
  have hn : (e.triples.map f).Nodup := List.pairwise_map.mpr
    (e.nodup.imp_of_mem (fun ha hb hne he =>
      hne (hi _ ((e.membership _).mp ha) _ ((e.membership _).mp hb) he)))
  have hnot : b ∉ e.triples.map f := by
    rintro hmem
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
    exact h ⟨a, (e.membership a).mp ha, he⟩
  have hsub : b :: e.triples.map f ⊆ e.triples := by
    intro x hx
    rcases List.mem_cons.mp hx with he | hx
    · exact he ▸ (e.membership b).mpr hb
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact (e.membership _).mpr (hm a ((e.membership a).mp ha))
  have hl := (List.nodup_cons.mpr ⟨hnot, hn⟩).length_le_of_subset hsub
  simp only [List.length_cons, List.length_map] at hl
  exact (Nat.not_succ_le_self _) hl

/-- Only the occurring blank set is finite; the set of triples may be infinite. -/
def FiniteBlankSupport (G : GeneralizedGraph Iri Literal B) : Prop :=
  Nonempty (Enumeration G.hasBlank)

def GeneralizedTriple.blankList (t : GeneralizedTriple Iri Literal B) : List B :=
  [t.subject, t.predicate, t.object].filterMap (fun
    | .blank b => some b
    | _ => none)

theorem GeneralizedTriple.mem_blankList (t : GeneralizedTriple Iri Literal B) (b : B) :
    b ∈ t.blankList ↔ t.hasBlank b := by
  obtain ⟨s, p, o⟩ := t
  cases s <;> cases p <;> cases o <;>
    simp [blankList, hasBlank, Term.hasBlank, eq_comm]

theorem finite_blank_support_of_finite_graph (G : GeneralizedGraph Iri Literal B)
    (h : FiniteGraph G) : FiniteBlankSupport G := by
  classical
  obtain ⟨e⟩ := h
  let eb := Enumeration.fromList (e.triples.flatMap GeneralizedTriple.blankList)
  refine ⟨⟨eb.triples, eb.nodup, ?_⟩⟩
  intro b
  rw [eb.membership]
  change b ∈ e.triples.flatMap GeneralizedTriple.blankList ↔ ∃ t, G t ∧ t.hasBlank b
  simp only [List.mem_flatMap, GeneralizedTriple.mem_blankList, e.membership]

theorem Term.substitute_blank_origin (q : Term Iri Literal B)
    (μ : Substitution Iri Literal B) (b : B) (h : (q.substitute μ).hasBlank b) :
    ∃ a, q.hasBlank a ∧ μ.resolve a = .blank b := by
  cases q with
  | iri i => contradiction
  | literal l => contradiction
  | blank a =>
    refine ⟨a, rfl, ?_⟩
    change (μ.resolve a).hasBlank b at h
    cases he : μ.resolve a with
    | iri i => simp [he, Term.hasBlank] at h
    | literal l => simp [he, Term.hasBlank] at h
    | blank c => simpa [he, Term.hasBlank] using h

theorem GeneralizedGraph.substitute_blank_origin (G : GeneralizedGraph Iri Literal B)
    (μ : Substitution Iri Literal B) (b : B) (h : (G.substitute μ).hasBlank b) :
    ∃ a, G.hasBlank a ∧ μ.resolve a = .blank b := by
  obtain ⟨_, ⟨t, ht, rfl⟩, hb⟩ := h
  rcases hb with hb | hb | hb
  · obtain ⟨a, ha, he⟩ := t.subject.substitute_blank_origin μ b hb
    exact ⟨a, ⟨t, ht, Or.inl ha⟩, he⟩
  · obtain ⟨a, ha, he⟩ := t.predicate.substitute_blank_origin μ b hb
    exact ⟨a, ⟨t, ht, Or.inr (Or.inl ha)⟩, he⟩
  · obtain ⟨a, ha, he⟩ := t.object.substitute_blank_origin μ b hb
    exact ⟨a, ⟨t, ht, Or.inr (Or.inr ha)⟩, he⟩

/-- Later substitutions cannot undo a name replacement or an identification. -/
theorem ProperSubstitution.then {G : GeneralizedGraph Iri Literal B}
    {μ : Substitution Iri Literal B} (h : ProperSubstitution G μ)
    (ν : Substitution Iri Literal B) : ProperSubstitution G (μ.then ν) := by
  rcases h with ⟨b, hb, ⟨i, hi⟩ | ⟨l, hl⟩⟩ | ⟨b, c, hb, hc, hne, he⟩
  · refine Or.inl ⟨b, hb, Or.inl ⟨i, ?_⟩⟩
    change (μ.resolve b).substitute ν = .iri i
    rw [hi]
    rfl
  · refine Or.inl ⟨b, hb, Or.inr ⟨l, ?_⟩⟩
    change (μ.resolve b).substitute ν = .literal l
    rw [hl]
    rfl
  · exact Or.inr ⟨b, c, hb, hc, hne, congrArg (fun q => q.substitute ν) he⟩

/-- A self-image on finite blank support cannot replace blanks by names or identify blanks. -/
theorem finite_blank_self_substitution_not_proper (G : GeneralizedGraph Iri Literal B)
    (hf : FiniteBlankSupport G) (μ : Substitution Iri Literal B)
    (he : G.substitute μ = G) : ¬ ProperSubstitution G μ := by
  classical
  obtain ⟨e⟩ := hf
  have pre (b : B) (hb : G.hasBlank b) : ∃ a, G.hasBlank a ∧ μ.resolve a = .blank b :=
    G.substitute_blank_origin μ b (he.symm ▸ hb)
  let f : B → B := fun b => if hb : G.hasBlank b then Classical.choose (pre b hb) else b
  have fspec (b : B) (hb : G.hasBlank b) : G.hasBlank (f b) ∧ μ.resolve (f b) = .blank b := by
    simpa only [f, dif_pos hb] using Classical.choose_spec (pre b hb)
  have inj (a : B) (ha : G.hasBlank a) (b : B) (hb : G.hasBlank b)
      (hab : f a = f b) : a = b := by
    exact Term.blank.inj ((fspec a ha).2.symm.trans ((congrArg μ.resolve hab).trans (fspec b hb).2))
  have surj := e.injective_surjective f (fun b hb => (fspec b hb).1) inj
  intro hp
  rcases hp with ⟨b, hb, ⟨i, hi⟩ | ⟨l, hl⟩⟩ | ⟨b, c, hb, hc, hne, hbc⟩
  · obtain ⟨a, ha, rfl⟩ := surj b hb
    rw [(fspec a ha).2] at hi
    contradiction
  · obtain ⟨a, ha, rfl⟩ := surj b hb
    rw [(fspec a ha).2] at hl
    contradiction
  · obtain ⟨a, ha, rfl⟩ := surj b hb
    obtain ⟨d, hd, rfl⟩ := surj c hc
    rw [(fspec a ha).2, (fspec d hd).2] at hbc
    exact hne (congrArg f (Term.blank.inj hbc))

theorem finite_blank_no_proper_self_instance (G : GeneralizedGraph Iri Literal B)
    (hf : FiniteBlankSupport G) : ¬ ProperInstance G G := by
  rintro ⟨μ, he, hp⟩
  exact finite_blank_self_substitution_not_proper G hf μ he.symm hp

/-- Interpolation and leanness isolate the remaining self-instance obstruction.
No finite or ordinary-syntax premise is used in this reduction. -/
theorem lean_entails_proper_gives_self_instance {G H : GeneralizedGraph Iri Literal B}
    (hl : LeanGraph G) (hp : ProperInstance H G) (he : SimplyEntails.{u} G H) :
    ProperInstance G G := by
  obtain ⟨μ, rfl, hμ⟩ := hp
  obtain ⟨ν, hν⟩ := entailment_has_instance_subgraph he
  rw [GeneralizedGraph.substitute_comp] at hν
  exact ⟨μ.then ν, (hl _ ⟨μ.then ν, rfl⟩ hν).symm, hμ.then ν⟩

/-- Exact statement of the obstruction, without assuming the source consequence. -/
theorem lean_proper_nonentailment_iff (G : GeneralizedGraph Iri Literal B)
    (hl : LeanGraph G) :
    (∀ H, ProperInstance H G → ¬ SimplyEntails.{u} G H) ↔ ¬ ProperInstance G G := by
  constructor
  · intro h hp
    exact h G hp (simplyEntails_refl G)
  · intro h H hp he
    exact h (lean_entails_proper_gives_self_instance hl hp he)

/-- Checked finite-blank scope of §5.3's unqualified lean/proper-instance claim. -/
theorem lean_finite_blanks_not_entails_proper_instance (G H : GeneralizedGraph Iri Literal B)
    (hl : LeanGraph G) (hf : FiniteBlankSupport G) (hp : ProperInstance H G) :
    ¬ SimplyEntails.{u} G H :=
  (lean_proper_nonentailment_iff G hl).mpr (finite_blank_no_proper_self_instance G hf) H hp

theorem lean_finite_graph_not_entails_proper_instance (G H : GeneralizedGraph Iri Literal B)
    (hl : LeanGraph G) (hf : FiniteGraph G) (hp : ProperInstance H G) :
    ¬ SimplyEntails.{u} G H :=
  lean_finite_blanks_not_entails_proper_instance G H hl (finite_blank_support_of_finite_graph G hf) hp

end RDF11
