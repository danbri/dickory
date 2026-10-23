/-
RDF 1.1 Semantics §7.2.1: ill-typed literals are the only source of
simple D-unsatisfiability. Construct one model with full property extensions.
This is an existence witness, not an extra condition on all interpretations.
-/
import RDF11.Datatypes
import RDF11.Interpolation

namespace RDF11
namespace DatatypeModel

abbrev Carrier.{u} (Value : Type) := ULift.{u} (Sum Value Unit)

def embed (v : Value) : Carrier.{u} Value := ⟨.inl v⟩

def unnamed : Carrier.{u} Value := ⟨.inr ()⟩

def realization : ValueRealization Value (Carrier.{u} Value) where
  value := fun v => some (embed v)
  injective := fun v w _ hv hw => by
    have he : embed v = embed w := Option.some.inj (hv.trans hw.symm)
    exact Sum.inl.inj (congrArg ULift.down he)

noncomputable def literal (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (l : Literal) : Option (Carrier.{u} Value) := by
  classical
  exact if D (T.literalSyntax.datatype l) then
    match T.literalSyntax.language l with
    | some tag => some (embed (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag)))
    | none => (T.L2V (T.identified (T.literalSyntax.datatype l)) (T.literalSyntax.lexical l)).map embed
  else some unnamed

noncomputable def interpretation (T : DatatypeTheory Iri Literal Value) (D : Set Iri) :
    SimpleInterpretation Iri Literal (Carrier.{u} Value) := by
  classical
  exact {
    IR := fun _ => True
    IR_nonempty := ⟨unnamed, True.intro⟩
    IP := fun _ => True
    IEXT := fun _ _ => True
    IS := fun a => ⟨if D a then embed (T.identified a) else unnamed,
      Or.inl True.intro⟩
    IL := fun l => (literal T D l).map (fun x => ⟨x, True.intro⟩)
  }

theorem language_none (T : DatatypeTheory Iri Literal Value) (l : Literal)
    (h : T.literalSyntax.datatype l ≠ T.literalSyntax.langString) :
    T.literalSyntax.language l = none := by
  cases ht : T.literalSyntax.language l with
  | none => rfl
  | some tag => exact False.elim (h ((T.literalSyntax.tagged_iff l).mp ⟨tag, ht⟩))

theorem conditions (T : DatatypeTheory Iri Literal Value) (D : Set Iri) :
    (interpretation.{u} T D).DConditions T D realization := by
  classical
  constructor
  · intro hd
    simp [realization, interpretation, hd]
  · intro l tag hd ht
    have htype := (T.literalSyntax.tagged_iff l).mp ⟨tag, ht⟩
    refine ⟨⟨embed (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag)), True.intro⟩, ?_, rfl⟩
    simp [interpretation, literal, htype, hd, ht]
  · intro a ha hn
    constructor
    · simp [realization, interpretation, ha]
    · intro l hl
      have ht := language_none T l (fun he => hn (hl.symm.trans he))
      cases hv : T.L2V (T.identified a) (T.literalSyntax.lexical l) with
      | none => simp [interpretation, literal, hl, ha, ht, hv]
      | some v =>
        refine ⟨⟨embed v, True.intro⟩, ?_, rfl⟩
        simp [interpretation, literal, hl, ha, ht, hv]

theorem model (T : DatatypeTheory Iri Literal Value) (D : Set Iri) :
    (interpretation.{u} T D).DModel T D := ⟨realization, conditions T D⟩

theorem literal_defined (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (l : Literal)
    (h : ¬ T.IllTyped D l) : ∃ r, (interpretation.{u} T D).IL l = some r := by
  classical
  by_cases hd : D (T.literalSyntax.datatype l)
  · cases ht : T.literalSyntax.language l with
    | some tag =>
      exact ⟨⟨embed (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag)), True.intro⟩,
        by simp [interpretation, literal, hd, ht]⟩
    | none =>
      have hn : T.literalSyntax.datatype l ≠ T.literalSyntax.langString := by
        intro he
        obtain ⟨tag, htag⟩ := (T.literalSyntax.tagged_iff l).mpr he
        simp [ht] at htag
      cases hv : T.L2V (T.identified (T.literalSyntax.datatype l)) (T.literalSyntax.lexical l) with
      | none => exact False.elim (h ⟨hd, hn, hv⟩)
      | some v => exact ⟨⟨embed v, True.intro⟩, by simp [interpretation, literal, hd, ht, hv]⟩
  · exact ⟨⟨unnamed, True.intro⟩, by simp [interpretation, literal, hd]⟩

def assignment (T : DatatypeTheory Iri Literal Value) (D : Set Iri) :
    (interpretation.{u} T D).Assignment B := fun _ => some ⟨unnamed, True.intro⟩

theorem term_defined (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (t : Term Iri Literal B) (h : ∀ l, t.hasLiteral l → ¬ T.IllTyped D l) :
    ∃ x : (interpretation.{u} T D).Resource,
      (interpretation T D).denote (assignment T D) t = some x.val := by
  cases t with
  | iri a => exact ⟨⟨((interpretation T D).IS a).val, True.intro⟩, rfl⟩
  | literal l =>
    obtain ⟨r, hr⟩ := literal_defined T D l (h l rfl)
    exact ⟨r, by simp [SimpleInterpretation.denote, hr]⟩
  | blank b => exact ⟨⟨unnamed, True.intro⟩, rfl⟩

theorem satisfies (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B)
    (h : ∀ t, G t → ∀ l, t.hasLiteral l → ¬ T.IllTyped D l) :
    (interpretation.{u} T D).Satisfies G := by
  apply ((interpretation T D).satisfies_iff_exists_graphTrue G).mpr
  refine ⟨assignment T D, ?_⟩
  intro t ht
  obtain ⟨p, hp⟩ := term_defined T D t.predicate (fun l hl => h t ht l (Or.inr (Or.inl hl)))
  obtain ⟨s, hs⟩ := term_defined T D t.subject (fun l hl => h t ht l (Or.inl hl))
  obtain ⟨o, ho⟩ := term_defined T D t.object (fun l hl => h t ht l (Or.inr (Or.inr hl)))
  exact ⟨⟨p.val, True.intro⟩, s, o, hp, hs, ho, True.intro⟩

end DatatypeModel

theorem d_satisfiable_iff_no_illTyped (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) :
    DSatisfiable.{u} T D G ↔ ∀ t, G t → ∀ l, t.hasLiteral l → ¬ T.IllTyped D l := by
  constructor
  · intro hG t ht l hl hi
    exact illTyped_graph_unsatisfiable T D G t ht hl hi hG
  · intro h
    exact ⟨DatatypeModel.Carrier Value, DatatypeModel.interpretation T D,
      DatatypeModel.model T D, DatatypeModel.satisfies T D G h⟩

theorem d_unsatisfiable_iff_illTyped (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) :
    DUnsatisfiable.{u} T D G ↔ ∃ t, G t ∧ ∃ l, t.hasLiteral l ∧ T.IllTyped D l := by
  classical
  unfold DUnsatisfiable
  rw [d_satisfiable_iff_no_illTyped]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    exact h (fun t ht l hl hi => hn ⟨t, ht, l, hl, hi⟩)
  · rintro ⟨t, ht, l, hl, hi⟩ h
    exact h t ht l hl hi

theorem empty_d_satisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri) :
    DSatisfiable.{u} T D (Set.empty : GeneralizedGraph Iri Literal B) :=
  (d_satisfiable_iff_no_illTyped T D Set.empty).mpr (fun _ h => False.elim h)

/-- An explicit ill-typed literal witnesses failure of the printed reverse entailment direction. -/
theorem d_entailment_not_simple_of_illTyped (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (l : Literal) (hi : T.IllTyped D l) :
    ∃ G E : Graph Iri Literal Empty,
      DEntails.{u} T D G.generalize E.generalize ∧ ¬ SimplyEntails.{u} G.generalize E.generalize := by
  let a := T.literalSyntax.langString
  let g : Triple Iri Literal Empty := ⟨.iri a, a, .literal l⟩
  let e : Triple Iri Literal Empty := ⟨.iri a, a, .iri a⟩
  let G : Graph Iri Literal Empty := Set.singleton g
  let E : Graph Iri Literal Empty := Set.singleton e
  refine ⟨G, E, ?_, ?_⟩
  · apply d_ex_falso T D (illTyped_graph_unsatisfiable T D G.generalize g.generalize
      ⟨g, rfl, rfl⟩ (Or.inr (Or.inr rfl)) hi)
  · intro h
    have hg : E.generalize.ground := fun b => nomatch b
    obtain ⟨t, ht, he⟩ := (ground_entailment_iff_subset G.generalize E.generalize hg).mp h
      e.generalize ⟨e, rfl, rfl⟩
    have ht' : t = g := ht
    subst t
    have ho := congrArg GeneralizedTriple.object he
    cases ho

end RDF11
