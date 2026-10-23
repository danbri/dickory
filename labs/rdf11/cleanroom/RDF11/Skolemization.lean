/-
RDF 1.1 Semantics §6: all occurring blanks receive distinct fresh IRIs.
The supplied map is not assumed to exist for every abstract IRI domain.
Freshness includes datatype IRIs via the explicit literal datatype projection.
-/
import RDF11.VocabularyEntailment

namespace RDF11

structure Skolemization (datatype : Literal → Iri) (G : GeneralizedGraph Iri Literal B) where
  name : B → Iri
  injective : ∀ b c, G.hasBlank b → G.hasBlank c → name b = name c → b = c
  fresh : ∀ b, G.hasBlank b → ¬ G.vocabulary datatype (.inl (name b))

namespace Skolemization

variable {Iri Literal B : Type} {datatype : Literal → Iri} {G : GeneralizedGraph Iri Literal B}

def substitution (sk : Skolemization datatype G) : Substitution Iri Literal B :=
  fun b => some (.iri (sk.name b))

def graph (sk : Skolemization datatype G) : GeneralizedGraph Iri Literal B :=
  G.substitute sk.substitution

theorem ground (sk : Skolemization datatype G) : sk.graph.ground := by
  rintro b ⟨_, ⟨t, ht, rfl⟩, hb⟩
  have term (q : Term Iri Literal B) : ¬ (q.substitute sk.substitution).hasBlank b := by
    cases q <;> simp [Term.substitute, substitution, Substitution.resolve, Term.hasBlank]
  rcases hb with h | h | h
  · exact term t.subject h
  · exact term t.predicate h
  · exact term t.object h

theorem lean (sk : Skolemization datatype G) : LeanGraph sk.graph :=
  ground_is_lean sk.graph sk.ground

theorem is_instance (sk : Skolemization datatype G) : IsInstance sk.graph G :=
  ⟨sk.substitution, rfl⟩

theorem entails_original (G : Graph Iri Literal B) (sk : Skolemization datatype G.generalize) :
    SimplyEntails.{u} sk.graph G.generalize := ordinary_substitution_entails G sk.substitution

theorem contains_skolem_name {datatype : Literal → Iri} {G : GeneralizedGraph Iri Literal B}
    (sk : Skolemization datatype G) {b : B} (hb : G.hasBlank b) :
    sk.graph.vocabulary datatype (.inl (sk.name b)) := by
  obtain ⟨t, ht, htb⟩ := hb
  refine ⟨t.substitute sk.substitution, ⟨t, ht, rfl⟩, ?_⟩
  have term (q : Term Iri Literal B) (hq : q.hasBlank b) :
      (q.substitute sk.substitution).names datatype (.inl (sk.name b)) := by
    cases q with
    | iri _ => exact False.elim hq
    | literal _ => exact False.elim hq
    | blank c =>
      have hcb : c = b := hq
      subst c
      exact rfl
  rcases htb with h | h | h
  · exact Or.inl (term t.subject h)
  · exact Or.inr (Or.inl (term t.predicate h))
  · exact Or.inr (Or.inr (term t.object h))

theorem original_not_entails {datatype : Literal → Iri} {G : GeneralizedGraph Iri Literal B}
    (sk : Skolemization datatype G) (hb : ∃ b, G.hasBlank b) :
    ¬ SimplyEntails.{u} G sk.graph := by
  obtain ⟨b, hb⟩ := hb
  exact fresh_iri_nonentailment datatype G sk.graph (sk.name b)
    (sk.fresh b hb) (sk.contains_skolem_name hb)

/-- A fresh-vocabulary conclusion mentions none of G's chosen skolem IRIs. -/
def Avoids (sk : Skolemization datatype G) (H : GeneralizedGraph Iri Literal B) : Prop :=
  ∀ b, G.hasBlank b → ¬ H.vocabulary datatype (.inl (sk.name b))

noncomputable def unname (sk : Skolemization datatype G) (i : Iri) : Option B := by
  classical
  exact if h : ∃ b, G.hasBlank b ∧ sk.name b = i then some (Classical.choose h) else none

theorem unname_name (sk : Skolemization datatype G) (b : B) (hb : G.hasBlank b) :
    sk.unname (sk.name b) = some b := by
  classical
  have h : ∃ c, G.hasBlank c ∧ sk.name c = sk.name b := ⟨b, hb, rfl⟩
  have hc := Classical.choose_spec h
  have he := sk.injective (Classical.choose h) b hc.1 hb hc.2
  simp [unname, h, he]

noncomputable def inverseTerm (sk : Skolemization datatype G) : Term Iri Literal B → Term Iri Literal B
  | .iri i => (sk.unname i).map Term.blank |>.getD (.iri i)
  | .literal l => .literal l
  | .blank b => .blank b

noncomputable def inverseTriple (sk : Skolemization datatype G)
    (t : GeneralizedTriple Iri Literal B) : GeneralizedTriple Iri Literal B :=
  ⟨sk.inverseTerm t.subject, sk.inverseTerm t.predicate, sk.inverseTerm t.object⟩

theorem inverseTerm_fixed (sk : Skolemization datatype G) (q : Term Iri Literal B)
    (hf : ∀ b, G.hasBlank b → ¬ q.names datatype (.inl (sk.name b))) : sk.inverseTerm q = q := by
  cases q with
  | iri i =>
    have hn : ¬ ∃ b, G.hasBlank b ∧ sk.name b = i := by
      rintro ⟨b, hb, he⟩
      exact hf b hb (congrArg Sum.inl he)
    simp [inverseTerm, unname, hn]
  | literal _ => rfl
  | blank _ => rfl

theorem inverseTerm_substituted (sk : Skolemization datatype G) (q : Term Iri Literal B)
    (hf : ∀ b, G.hasBlank b → ¬ q.names datatype (.inl (sk.name b)))
    (hq : ∀ b, q.hasBlank b → G.hasBlank b) :
    sk.inverseTerm (q.substitute sk.substitution) = q := by
  cases q with
  | iri i => exact sk.inverseTerm_fixed (.iri i) hf
  | literal _ => rfl
  | blank b =>
    simp [Term.substitute, substitution, Substitution.resolve, inverseTerm,
      sk.unname_name b (hq b rfl)]

theorem inverse_substituted_triple (sk : Skolemization datatype G)
    (t : GeneralizedTriple Iri Literal B) (ht : G t) :
    sk.inverseTriple (t.substitute sk.substitution) = t := by
  have term (q : Term Iri Literal B)
      (hn : ∀ n, q.names datatype n → t.names datatype n)
      (hb : ∀ b, q.hasBlank b → t.hasBlank b) :
      sk.inverseTerm (q.substitute sk.substitution) = q := by
    apply sk.inverseTerm_substituted
    · intro b hbg hqn
      exact sk.fresh b hbg ⟨t, ht, hn _ hqn⟩
    · exact fun b hqb => ⟨t, ht, hb b hqb⟩
  have hs := term t.subject (fun _ h => Or.inl h) (fun _ h => Or.inl h)
  have hp := term t.predicate (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inl h))
  have ho := term t.object (fun _ h => Or.inr (Or.inr h)) (fun _ h => Or.inr (Or.inr h))
  simp [inverseTriple, GeneralizedTriple.substitute, hs, hp, ho]

noncomputable def inverseSubstitution (sk : Skolemization datatype G)
    (μ : Substitution Iri Literal B) : Substitution Iri Literal B :=
  fun b => some (sk.inverseTerm (μ.resolve b))

theorem inverse_substitution_commutes (sk : Skolemization datatype G)
    (μ : Substitution Iri Literal B) (t : GeneralizedTriple Iri Literal B)
    (hf : ∀ b, G.hasBlank b → ¬ t.names datatype (.inl (sk.name b))) :
    sk.inverseTriple (t.substitute μ) = t.substitute (sk.inverseSubstitution μ) := by
  have term (q : Term Iri Literal B) (hn : ∀ n, q.names datatype n → t.names datatype n) :
      sk.inverseTerm (q.substitute μ) = q.substitute (sk.inverseSubstitution μ) := by
    have hq : ∀ b, G.hasBlank b → ¬ q.names datatype (.inl (sk.name b)) :=
      fun b hb h => hf b hb (hn _ h)
    cases q with
    | iri i => exact sk.inverseTerm_fixed (.iri i) hq
    | literal _ => rfl
    | blank _ => rfl
  have hs := term t.subject (fun _ h => Or.inl h)
  have hp := term t.predicate (fun _ h => Or.inr (Or.inl h))
  have ho := term t.object (fun _ h => Or.inr (Or.inr h))
  simp [inverseTriple, GeneralizedTriple.substitute, hs, hp, ho]

/-- Ordinary G and H, no finiteness restriction. Freshness includes datatype IRIs. -/
theorem conservative (G H : Graph Iri Literal B) (sk : Skolemization datatype G.generalize)
    (hf : sk.Avoids H.generalize) :
    SimplyEntails.{u} sk.graph H.generalize ↔ SimplyEntails.{u} G.generalize H.generalize := by
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := entailment_has_instance_subgraph h
    apply (ordinary_interpolation G.generalize H).mpr
    refine ⟨sk.inverseSubstitution μ, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs, he⟩ := hμ _ ⟨t, ht, rfl⟩
    have hinv := sk.inverse_substituted_triple s hs
    have hcomm := sk.inverse_substitution_commutes μ t
      (fun b hb hn => hf b hb ⟨t, ht, hn⟩)
    rw [he, hcomm] at hinv
    exact hinv.symm ▸ hs
  · intro h
    exact simplyEntails_trans (sk.entails_original G) h

end Skolemization
end RDF11
