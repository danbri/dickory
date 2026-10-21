/-
RDF 1.1 Semantics §5–5.2: simple interpretations and truth conditions.
IR, IP, IEXT, IS, IL and A follow the source notation.
An ambient U lets IR and IP overlap without assuming IP ⊆ IR.
Option models partial IL; blank assignments have exactly the graph's domain.
-/
import RDF11.Syntax

namespace RDF11

structure SimpleInterpretation (Iri Literal : Type) (U : Type u) where
  IR : Set U
  IR_nonempty : ∃ x, IR x
  IP : Set U
  IEXT : {p : U // IP p} → Set ({x : U // IR x} × {y : U // IR y})
  IS : Iri → {x : U // IR x ∨ IP x}
  IL : Literal → Option {x : U // IR x}

namespace SimpleInterpretation

abbrev Resource (I : SimpleInterpretation Iri Literal U) := {x : U // I.IR x}
abbrev Property (I : SimpleInterpretation Iri Literal U) := {x : U // I.IP x}
abbrev Assignment (I : SimpleInterpretation Iri Literal U) (Blank : Type) :=
  Blank → Option I.Resource

def AssignmentOn (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) (A : I.Assignment Blank) : Prop :=
  ∀ b, (∃ x, A b = some x) ↔ G.hasBlank b

/-- The specification's extended interpretation [I+A]. -/
def denote (I : SimpleInterpretation Iri Literal U) (A : I.Assignment Blank) :
    Term Iri Literal Blank → Option U
  | .iri i => some (I.IS i).val
  | .literal l => (I.IL l).map Subtype.val
  | .blank b => (A b).map Subtype.val

def TripleTrue (I : SimpleInterpretation Iri Literal U) (A : I.Assignment Blank)
    (t : GeneralizedTriple Iri Literal Blank) : Prop :=
  ∃ p : I.Property, ∃ s o : I.Resource,
    I.denote A t.predicate = some p.val ∧
    I.denote A t.subject = some s.val ∧
    I.denote A t.object = some o.val ∧ I.IEXT p (s, o)

def GraphTrue (I : SimpleInterpretation Iri Literal U) (A : I.Assignment Blank)
    (G : GeneralizedGraph Iri Literal Blank) : Prop :=
  ∀ t, G t → I.TripleTrue A t

def Satisfies (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) : Prop :=
  ∃ A, I.AssignmentOn G A ∧ I.GraphTrue A G

noncomputable def restrict (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) (A : I.Assignment Blank) :
    I.Assignment Blank := by
  classical
  exact fun b => if G.hasBlank b then A b else none

theorem denote_agrees (I : SimpleInterpretation Iri Literal U)
    {A B : I.Assignment Blank} (t : Term Iri Literal Blank)
    (h : ∀ b, t.hasBlank b → A b = B b) :
    I.denote A t = I.denote B t := by
  cases t with
  | iri i => rfl
  | literal l => rfl
  | blank b => simp only [denote, h b rfl]

theorem tripleTrue_agrees (I : SimpleInterpretation Iri Literal U)
    {A B : I.Assignment Blank} (t : GeneralizedTriple Iri Literal Blank)
    (h : ∀ b, t.hasBlank b → A b = B b) :
    I.TripleTrue A t ↔ I.TripleTrue B t := by
  have hs := I.denote_agrees t.subject (fun b hb => h b (Or.inl hb))
  have hp := I.denote_agrees t.predicate (fun b hb => h b (Or.inr (Or.inl hb)))
  have ho := I.denote_agrees t.object (fun b hb => h b (Or.inr (Or.inr hb)))
  simp only [TripleTrue, hs, hp, ho]

theorem graphTrue_restrict (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) (A : I.Assignment Blank) :
    I.GraphTrue (I.restrict G A) G ↔ I.GraphTrue A G := by
  have ht : ∀ t, G t → (I.TripleTrue (I.restrict G A) t ↔ I.TripleTrue A t) := by
    intro t hG
    apply I.tripleTrue_agrees
    intro b hb
    have hGb : G.hasBlank b := ⟨t, hG, hb⟩
    simp [restrict, hGb]
  exact ⟨fun h t hG => (ht t hG).mp (h t hG),
    fun h t hG => (ht t hG).mpr (h t hG)⟩

theorem tripleTrue_blank_defined (I : SimpleInterpretation Iri Literal U)
    {A : I.Assignment Blank} {t : GeneralizedTriple Iri Literal Blank}
    (h : I.TripleTrue A t) {b : Blank} (hb : t.hasBlank b) :
    ∃ x, A b = some x := by
  obtain ⟨p, s, o, hp, hs, ho, _⟩ := h
  have defined (q : Term Iri Literal Blank) (x : U)
      (hd : I.denote A q = some x) (hq : q.hasBlank b) : ∃ r, A b = some r := by
    cases q with
    | iri i => exact False.elim hq
    | literal l => exact False.elim hq
    | blank c =>
      have hcb : c = b := hq
      subst c
      cases he : A b with
      | none => simp [denote, he] at hd
      | some r => exact ⟨r, rfl⟩
  rcases hb with hb | hb | hb
  · exact defined t.subject s.val hs hb
  · exact defined t.predicate p.val hp hb
  · exact defined t.object o.val ho hb

/-- Extra unused assignments do not change satisfaction: restriction is proved. -/
theorem satisfies_iff_exists_graphTrue (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) :
    I.Satisfies G ↔ ∃ A, I.GraphTrue A G := by
  constructor
  · rintro ⟨A, _, h⟩
    exact ⟨A, h⟩
  · rintro ⟨A, h⟩
    refine ⟨I.restrict G A, ?_, (I.graphTrue_restrict G A).mpr h⟩
    intro b
    constructor
    · rintro ⟨x, hx⟩
      classical
      by_cases hb : G.hasBlank b
      · exact hb
      · simp [restrict, hb] at hx
    · intro hb
      obtain ⟨t, ht, htb⟩ := hb
      obtain ⟨x, hx⟩ := I.tripleTrue_blank_defined (h t ht) htb
      refine ⟨x, ?_⟩
      have hGb : G.hasBlank b := ⟨t, ht, htb⟩
      simp [restrict, hGb, hx]

theorem satisfies_empty (I : SimpleInterpretation Iri Literal U) :
    I.Satisfies (Set.empty : GeneralizedGraph Iri Literal Blank) :=
  (I.satisfies_iff_exists_graphTrue _).mpr ⟨fun _ => none, fun _ h => False.elim h⟩

theorem satisfies_subgraph (I : SimpleInterpretation Iri Literal U)
    {G H : GeneralizedGraph Iri Literal Blank} (hHG : Set.subset H G)
    (hG : I.Satisfies G) : I.Satisfies H := by
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  exact (I.satisfies_iff_exists_graphTrue H).mpr ⟨A, fun t ht => hA t (hHG t ht)⟩

theorem undefined_literal_false (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment Blank) (l : Literal) (hl : I.IL l = none)
    (s p : Term Iri Literal Blank) : ¬ I.TripleTrue A ⟨s, p, .literal l⟩ := by
  rintro ⟨_, _, _, _, _, ho, _⟩
  simp [denote, hl] at ho

theorem undefined_literal_any_position (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment Blank) (l : Literal) (hl : I.IL l = none)
    (t : GeneralizedTriple Iri Literal Blank) (ht : t.hasLiteral l) :
    ¬ I.TripleTrue A t := by
  rintro ⟨p, s, o, hp, hs, ho, _⟩
  have undef (q : Term Iri Literal Blank) (x : U)
      (hd : I.denote A q = some x) (hq : q.hasLiteral l) : False := by
    cases q with
    | iri _ => exact hq
    | blank _ => exact hq
    | literal k =>
      have hkl : k = l := hq
      subst k
      simp [denote, hl] at hd
  rcases ht with ht | ht | ht
  · exact undef t.subject s.val hs ht
  · exact undef t.predicate p.val hp ht
  · exact undef t.object o.val ho ht

theorem graph_with_undefined_literal_false (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) (l : Literal) (hl : I.IL l = none)
    (t : GeneralizedTriple Iri Literal Blank) (ht : G t) (hlit : t.hasLiteral l) :
    ¬ I.Satisfies G := by
  rintro ⟨A, _, h⟩
  exact I.undefined_literal_any_position A l hl t hlit (h t ht)

theorem ground_satisfaction (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal Blank) (hG : G.ground) :
    I.Satisfies G ↔ I.GraphTrue (fun _ => none) G := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp h
    intro t ht
    apply (I.tripleTrue_agrees t ?_).mp (hA t ht)
    intro b hb
    exact False.elim (hG b ⟨t, ht, hb⟩)
  · exact fun h => (I.satisfies_iff_exists_graphTrue G).mpr ⟨_, h⟩

end SimpleInterpretation
end RDF11

