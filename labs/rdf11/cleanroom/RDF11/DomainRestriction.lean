/-
Supporting construction for informative Appendix B: restrict the active semantic
domain while retaining all interpreted names. U is only an ambient carrier; the
resource universe IR and property set IP are both intersected with the kept set.
No assumption IP ⊆ IR is made. This is a construction for simple semantics.
-/
import RDF11.Simple

namespace RDF11.SimpleInterpretation

structure DomainRestriction (I : SimpleInterpretation Iri Literal U) where
  keep : Set U
  resource : {r : I.Resource // keep r.val}
  names : ∀ i, keep (I.IS i).val
  literals : ∀ l r, I.IL l = some r → keep r.val

namespace DomainRestriction

variable {Iri Literal : Type} {U : Type u} {I : SimpleInterpretation Iri Literal U}

def interpretation (R : I.DomainRestriction) : SimpleInterpretation Iri Literal U where
  IR := fun x => I.IR x ∧ R.keep x
  IR_nonempty := ⟨R.resource.val.val, R.resource.val.property, R.resource.property⟩
  IP := fun x => I.IP x ∧ R.keep x
  IEXT := fun p pair => I.IEXT ⟨p.val, p.property.1⟩
    (⟨pair.1.val, pair.1.property.1⟩, ⟨pair.2.val, pair.2.property.1⟩)
  IS := fun i => ⟨(I.IS i).val, (I.IS i).property.elim
    (fun h => Or.inl ⟨h, R.names i⟩) (fun h => Or.inr ⟨h, R.names i⟩)⟩
  IL := fun l => match h : I.IL l with
    | none => none
    | some r => some ⟨r.val, r.property, R.literals l r h⟩

/-- Forget the kept-domain evidence without changing any assigned value. -/
def liftAssignment (R : I.DomainRestriction) (A : R.interpretation.Assignment B) :
    I.Assignment B := fun b => (A b).map (fun r => ⟨r.val, r.property.1⟩)

theorem denote_lift (R : I.DomainRestriction) (A : R.interpretation.Assignment B)
    (t : Term Iri Literal B) :
    R.interpretation.denote A t = I.denote (R.liftAssignment A) t := by
  cases t with
  | iri i => rfl
  | literal l =>
    dsimp [denote, interpretation]
    split <;> simp_all
  | blank b => cases h : A b <;> simp [denote, liftAssignment, h]

theorem denote_kept (R : I.DomainRestriction) (A : R.interpretation.Assignment B)
    (t : Term Iri Literal B) {x : U} (h : R.interpretation.denote A t = some x) :
    R.keep x := by
  cases t with
  | iri i =>
    have he : (I.IS i).val = x := Option.some.inj h
    exact he ▸ R.names i
  | literal l =>
    change (R.interpretation.IL l).map Subtype.val = some x at h
    obtain ⟨r, _, he⟩ := Option.map_eq_some_iff.mp h
    exact he ▸ r.property.2
  | blank b =>
    obtain ⟨r, _, he⟩ := Option.map_eq_some_iff.mp h
    exact he ▸ r.property.2

theorem tripleTrue_iff (R : I.DomainRestriction) (A : R.interpretation.Assignment B)
    (t : GeneralizedTriple Iri Literal B) :
    R.interpretation.TripleTrue A t ↔ I.TripleTrue (R.liftAssignment A) t := by
  constructor
  · rintro ⟨p, s, o, hp, hs, ho, he⟩
    exact ⟨⟨p.val, p.property.1⟩, ⟨s.val, s.property.1⟩, ⟨o.val, o.property.1⟩,
      (R.denote_lift A t.predicate).symm.trans hp,
      (R.denote_lift A t.subject).symm.trans hs,
      (R.denote_lift A t.object).symm.trans ho, he⟩
  · rintro ⟨p, s, o, hp, hs, ho, he⟩
    have hp' := (R.denote_lift A t.predicate).trans hp
    have hs' := (R.denote_lift A t.subject).trans hs
    have ho' := (R.denote_lift A t.object).trans ho
    exact ⟨⟨p.val, p.property, R.denote_kept A _ hp'⟩,
      ⟨s.val, s.property, R.denote_kept A _ hs'⟩,
      ⟨o.val, o.property, R.denote_kept A _ ho'⟩, hp', hs', ho', he⟩

theorem graphTrue_iff (R : I.DomainRestriction) (A : R.interpretation.Assignment B)
    (G : GeneralizedGraph Iri Literal B) :
    R.interpretation.GraphTrue A G ↔ I.GraphTrue (R.liftAssignment A) G :=
  ⟨fun h t ht => (R.tripleTrue_iff A t).mp (h t ht),
   fun h t ht => (R.tripleTrue_iff A t).mpr (h t ht)⟩

/-- Every conclusion model in the restriction is also a model in the original. -/
theorem satisfies_lift (R : I.DomainRestriction) (G : GeneralizedGraph Iri Literal B)
    (h : R.interpretation.Satisfies G) : I.Satisfies G := by
  obtain ⟨A, hA⟩ := (R.interpretation.satisfies_iff_exists_graphTrue G).mp h
  exact (I.satisfies_iff_exists_graphTrue G).mpr ⟨R.liftAssignment A, (R.graphTrue_iff A G).mp hA⟩

def lowerAssignment (R : I.DomainRestriction) (A : I.Assignment B)
    (hA : ∀ b r, A b = some r → R.keep r.val) : R.interpretation.Assignment B :=
  fun b => match h : A b with
    | none => none
    | some r => some ⟨r.val, r.property, hA b r h⟩

theorem lift_lower (R : I.DomainRestriction) (A : I.Assignment B)
    (hA : ∀ b r, A b = some r → R.keep r.val) :
    R.liftAssignment (R.lowerAssignment A hA) = A := by
  funext b
  dsimp [liftAssignment, lowerAssignment]
  split <;> simp_all

/-- Retaining the values of one premise witness keeps that whole premise true. -/
theorem satisfies_lower (R : I.DomainRestriction) (G : GeneralizedGraph Iri Literal B)
    (A : I.Assignment B) (hA : ∀ b r, A b = some r → R.keep r.val)
    (hG : I.GraphTrue A G) : R.interpretation.Satisfies G := by
  apply (R.interpretation.satisfies_iff_exists_graphTrue G).mpr
  refine ⟨R.lowerAssignment A hA, (R.graphTrue_iff _ G).mpr ?_⟩
  simpa only [R.lift_lower] using hG

end DomainRestriction
end RDF11.SimpleInterpretation
