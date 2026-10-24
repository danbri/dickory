/-
Appendix B datatype completion. Complete fixed values in a larger carrier and
retain old property extensions on embedded old endpoints. Whole-graph truth is
reflected for ordinary graphs; generalized predicate blanks need separate scope.
-/
import RDF11.DatatypePreinterpretations
import RDF11.Relations
import RDF11.OrdinaryPreinterpretations
import RDF11.FiniteDatatypeModels

namespace RDF11

namespace ValueRealization

def embed (ρ : ValueRealization Value U) (v : Value) : Sum U Value :=
  match ρ.value v with
  | some x => .inl x
  | none => .inr v

theorem embed_of_defined (ρ : ValueRealization Value U) (h : ρ.value v = some x) :
    ρ.embed v = .inl x := by simp [embed, h]

theorem embed_injective (ρ : ValueRealization Value U) {v w : Value}
    (h : ρ.embed v = ρ.embed w) : v = w := by
  cases hv : ρ.value v with
  | none =>
    cases hw : ρ.value w with
    | none => simpa [embed, hv, hw] using h
    | some y => simp [embed, hv, hw] at h
  | some x =>
    cases hw : ρ.value w with
    | none => simp [embed, hv, hw] at h
    | some y =>
      have he : x = y := by simpa [embed, hv, hw] using h
      exact ρ.injective v w y (he ▸ hv) hw

def complete (ρ : ValueRealization Value U) : ValueRealization Value (Sum U Value) where
  value := fun v => some (ρ.embed v)
  injective := fun _ _ _ hv hw => ρ.embed_injective (Option.some.inj (hv.trans hw.symm))

end ValueRealization

namespace DatatypeCompletion

variable {Iri Literal Value : Type} {U : Type u} {V : Set (Name Iri Literal)}
  {T : DatatypeTheory Iri Literal Value} {D : Set Iri} {ρ : ValueRealization Value U}

noncomputable def iriValue (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (i : Iri) : Sum U Value := by
  classical
  exact if hi : V (.inl i) then .inl (P.IS ⟨i, hi⟩).val else
    if D i then ρ.embed (T.identified i) else .inl (Classical.choose P.IR_nonempty)

noncomputable def literalValue (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (l : Literal) : Option (Sum U Value) := by
  classical
  exact if D (T.literalSyntax.datatype l) then
    if T.literalSyntax.datatype l = T.literalSyntax.langString then
      (T.literalSyntax.language l).map
        (fun tag => ρ.embed (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag)))
    else (T.L2V (T.identified (T.literalSyntax.datatype l)) (T.literalSyntax.lexical l)).map ρ.embed
  else if hl : V (.inr l) then (P.IL ⟨l, hl⟩).map (fun r => .inl r.val) else none

/-- Universal IR/IP are a construction choice; edges still require old roles. -/
noncomputable def interpretation (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) : SimpleInterpretation Iri Literal (Sum U Value) where
  IR := fun _ => True
  IR_nonempty := ⟨.inl (Classical.choose P.IR_nonempty), True.intro⟩
  IP := fun _ => True
  IEXT := fun p pair => match p.val, pair.1.val, pair.2.val with
    | .inl q, .inl x, .inl y => P.Relates q x y
    | _, _, _ => False
  IS := fun i => ⟨iriValue P T D ρ i, Or.inl True.intro⟩
  IL := fun l => (literalValue P T D ρ l).map (fun x => ⟨x, True.intro⟩)

theorem iriValue_local (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (i : VocabularyIRI V) :
    iriValue P T D ρ i.val = .inl (P.IS i).val := by simp [iriValue, i.property]

theorem iriValue_recognized (P : PreInterpretation V U)
    (h : PreInterpretation.DConditions P T D ρ) (i : Iri) (hd : D i) :
    iriValue P T D ρ i = ρ.embed (T.identified i) := by
  classical
  by_cases hi : V (.inl i)
  · simpa [iriValue, hi] using (ρ.embed_of_defined (h.recognized_denotation ⟨i, hi⟩ hd)).symm
  · simp [iriValue, hi, hd]

theorem literalValue_language (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (l : Literal) (tag : String)
    (hd : D T.literalSyntax.langString) (ht : T.literalSyntax.language l = some tag) :
    literalValue P T D ρ l = some (ρ.embed (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag))) := by
  have he := (T.literalSyntax.tagged_iff l).mp ⟨tag, ht⟩
  simp [literalValue, he, hd, ht]

theorem literalValue_ordinary (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (l : Literal)
    (hd : D (T.literalSyntax.datatype l)) (hn : T.literalSyntax.datatype l ≠ T.literalSyntax.langString) :
    literalValue P T D ρ l =
      (T.L2V (T.identified (T.literalSyntax.datatype l)) (T.literalSyntax.lexical l)).map ρ.embed := by
  simp [literalValue, hd, hn]

theorem literalValue_local (P : PreInterpretation V U)
    (h : PreInterpretation.DConditions P T D ρ) (l : VocabularyLiteral V) :
    literalValue P T D ρ l.val = (P.IL l).map (fun r => .inl r.val) := by
  classical
  by_cases hd : D (T.literalSyntax.datatype l.val)
  · by_cases he : T.literalSyntax.datatype l.val = T.literalSyntax.langString
    · obtain ⟨tag, ht⟩ := (T.literalSyntax.tagged_iff l.val).mpr he
      have hlang : D T.literalSyntax.langString := he ▸ hd
      obtain ⟨r, hr, hv⟩ := h.language l tag hlang ht
      rw [literalValue_language P T D ρ l.val tag hlang ht, hr, ρ.embed_of_defined hv]
      rfl
    · rw [literalValue_ordinary P T D ρ l.val hd he]
      have hc := h.ordinary l hd he
      cases hv : T.L2V (T.identified (T.literalSyntax.datatype l.val)) (T.literalSyntax.lexical l.val) with
      | none =>
        have hl : P.IL l = none := by simpa only [hv] using hc
        simp [hl]
      | some v =>
        have hc' : P.LiteralValue ρ l v := by simpa only [hv] using hc
        obtain ⟨r, hr, hv'⟩ := hc'
        simp [hr, ρ.embed_of_defined hv']
  · simp [literalValue, hd, l.property]

theorem conditions (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ) :
    (interpretation P T D ρ).DConditions T D ρ.complete where
  language_denotation := fun hd => congrArg some (iriValue_recognized P h _ hd).symm
  language := by
    intro l tag hd ht
    refine ⟨⟨ρ.embed (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag)), True.intro⟩, ?_, rfl⟩
    simp only [interpretation, literalValue_language P T D ρ l tag hd ht, Option.map_some]
  ordinary := by
    intro a hd hn
    refine ⟨congrArg some (iriValue_recognized P h a hd).symm, ?_⟩
    intro l hl
    have hd' : D (T.literalSyntax.datatype l) := hl.symm ▸ hd
    have hn' : T.literalSyntax.datatype l ≠ T.literalSyntax.langString := fun he => hn (hl.symm.trans he)
    have hv := literalValue_ordinary P T D ρ l hd' hn'
    rw [hl] at hv
    cases he : T.L2V (T.identified a) (T.literalSyntax.lexical l) with
    | none => simp only [interpretation, hv, he, Option.map_none]
    | some v =>
      refine ⟨⟨ρ.embed v, True.intro⟩, ?_, rfl⟩
      simp only [interpretation, hv, he, Option.map_some]

theorem relates_iff (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (p s o : Sum U Value) :
    (interpretation P T D ρ).Relates p s o ↔
      ∃ q x y : U, p = .inl q ∧ s = .inl x ∧ o = .inl y ∧ P.Relates q x y := by
  cases p <;> cases s <;> cases o <;> simp [SimpleInterpretation.Relates, interpretation]

def liftAssignment (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (A : P.Assignment B) :
    (interpretation P T D ρ).Assignment B :=
  fun b => (A b).map (fun r => ⟨.inl r.val, True.intro⟩)

theorem denote_lift (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (A : P.Assignment B) (t : Term (VocabularyIRI V) (VocabularyLiteral V) B) :
    (interpretation P T D ρ).denote (liftAssignment P T D ρ A) (t.mapNames Subtype.val Subtype.val) =
      (P.denote A t).map Sum.inl := by
  cases t with
  | iri i => simp [SimpleInterpretation.denote, Term.mapNames, interpretation, iriValue_local]
  | literal l =>
    simp [SimpleInterpretation.denote, Term.mapNames, interpretation, literalValue_local P h,
      Option.map_map, Function.comp_def]
  | blank b => simp [SimpleInterpretation.denote, Term.mapNames, liftAssignment, Option.map_map,
      Function.comp_def]

/-- All triples preserve truth for the same embedded assignment. -/
theorem tripleTrue_lift_iff (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (A : P.Assignment B) (t : GeneralizedTriple (VocabularyIRI V) (VocabularyLiteral V) B) :
    (interpretation P T D ρ).TripleTrue (liftAssignment P T D ρ A)
      (t.mapNames Subtype.val Subtype.val) ↔ P.TripleTrue A t := by
  rw [(interpretation P T D ρ).tripleTrue_iff_relates, P.tripleTrue_iff_relates]
  constructor
  · rintro ⟨p, s, o, hp, hs, ho, hr⟩
    obtain ⟨q, x, y, rfl, rfl, rfl, hOld⟩ := (relates_iff P T D ρ p s o).mp hr
    change (interpretation P T D ρ).denote (liftAssignment P T D ρ A)
      (t.predicate.mapNames Subtype.val Subtype.val) = _ at hp
    change (interpretation P T D ρ).denote (liftAssignment P T D ρ A)
      (t.subject.mapNames Subtype.val Subtype.val) = _ at hs
    change (interpretation P T D ρ).denote (liftAssignment P T D ρ A)
      (t.object.mapNames Subtype.val Subtype.val) = _ at ho
    rw [denote_lift P h] at hp hs ho
    simp only [Option.map_eq_some_iff, Sum.inl.injEq, exists_eq_right] at hp hs ho
    exact ⟨q, x, y, hp, hs, ho, hOld⟩
  · rintro ⟨q, x, y, hp, hs, ho, hr⟩
    refine ⟨.inl q, .inl x, .inl y, ?_, ?_, ?_, (relates_iff P T D ρ _ _ _).mpr
      ⟨q, x, y, rfl, rfl, rfl, hr⟩⟩ <;>
      simp only [GeneralizedTriple.mapNames, denote_lift P h, hp, hs, ho, Option.map_some]

theorem graphTrue_lift_iff (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (A : P.Assignment B) (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B) :
    (interpretation P T D ρ).GraphTrue (liftAssignment P T D ρ A)
      (G.mapNames Subtype.val Subtype.val) ↔ P.GraphTrue A G := by
  constructor
  · intro hg t ht
    exact (tripleTrue_lift_iff P h A t).mp (hg _ ⟨t, ht, rfl⟩)
  · rintro hg _ ⟨t, ht, rfl⟩
    exact (tripleTrue_lift_iff P h A t).mpr (hg t ht)

theorem satisfies_forward (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B) (hg : P.Satisfies G) :
    (interpretation P T D ρ).Satisfies (G.mapNames Subtype.val Subtype.val) := by
  obtain ⟨A, hA⟩ := (P.satisfies_iff_exists_graphTrue G).mp hg
  exact ((interpretation P T D ρ).satisfies_iff_exists_graphTrue _).mpr
    ⟨liftAssignment P T D ρ A, (graphTrue_lift_iff P h A G).mpr hA⟩

/-- Keep only assigned values that are embedded old resources. -/
noncomputable def lowerAssignment (P : PreInterpretation V U) (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (ρ : ValueRealization Value U) (A : (interpretation P T D ρ).Assignment B) :
    P.Assignment B := by
  classical
  exact fun b => match A b with
    | none => none
    | some r => match r.val with
      | .inl x => if hx : P.IR x then some ⟨x, hx⟩ else none
      | .inr _ => none

theorem denote_reflect_resource (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (A : (interpretation P T D ρ).Assignment B)
    (t : Term (VocabularyIRI V) (VocabularyLiteral V) B) (x : U) (hx : P.IR x)
    (ht : (interpretation P T D ρ).denote A (t.mapNames Subtype.val Subtype.val) = some (.inl x)) :
    P.denote (lowerAssignment P T D ρ A) t = some x := by
  cases t with
  | iri i =>
    have hm := denote_lift P h (lowerAssignment P T D ρ A) (.iri i)
    have he := hm.symm.trans ht
    simpa only [Option.map_eq_some_iff, Sum.inl.injEq, exists_eq_right] using he
  | literal l =>
    have hm := denote_lift P h (lowerAssignment P T D ρ A) (.literal l)
    have he := hm.symm.trans ht
    simpa only [Option.map_eq_some_iff, Sum.inl.injEq, exists_eq_right] using he
  | blank b =>
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp ht
    simp [SimpleInterpretation.denote, lowerAssignment, hr, he, hx]

theorem ordinary_triple_reflect (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (A : (interpretation P T D ρ).Assignment B)
    (t : Triple (VocabularyIRI V) (VocabularyLiteral V) B)
    (ht : (interpretation P T D ρ).TripleTrue A (t.generalize.mapNames Subtype.val Subtype.val)) :
    P.TripleTrue (lowerAssignment P T D ρ A) t.generalize := by
  obtain ⟨p, s, o, hp, hs, ho, hr⟩ := ((interpretation P T D ρ).tripleTrue_iff_relates _ _).mp ht
  obtain ⟨q, x, y, rfl, rfl, rfl, hOld⟩ := (relates_iff P T D ρ p s o).mp hr
  apply P.tripleTrue_of_relates
    (p := q) (s := x) (o := y)
  · have hm := denote_lift P h (lowerAssignment P T D ρ A) (.iri t.predicate)
    have he := hm.symm.trans hp
    simpa only [Option.map_eq_some_iff, Sum.inl.injEq, exists_eq_right, Triple.generalize] using he
  · exact denote_reflect_resource P h A _ x (P.relates_subject hOld) hs
  · exact denote_reflect_resource P h A _ y (P.relates_object hOld) ho
  · exact hOld

/-- One lowered assignment reflects every ordinary triple in the graph. -/
theorem ordinary_satisfies_iff (P : PreInterpretation V U) (h : PreInterpretation.DConditions P T D ρ)
    (G : Graph (VocabularyIRI V) (VocabularyLiteral V) B) :
    (interpretation P T D ρ).Satisfies (G.generalize.mapNames Subtype.val Subtype.val) ↔
      P.Satisfies G.generalize := by
  constructor
  · intro hg
    obtain ⟨A, hA⟩ := ((interpretation P T D ρ).satisfies_iff_exists_graphTrue _).mp hg
    apply (P.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨lowerAssignment P T D ρ A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact ordinary_triple_reflect P h A t (hA _ ⟨t.generalize, ⟨t, ht, rfl⟩, rfl⟩)
  · exact satisfies_forward P h G.generalize

end DatatypeCompletion

/-- Exact datatype entailment comparison with ordinary conclusions, over all local models. -/
theorem d_entailment_iff_preinterpretations_ordinary (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (V : Set (Name Iri Literal))
    (G : GeneralizedGraph (VocabularyIRI V) (VocabularyLiteral V) B₁)
    (E : Graph (VocabularyIRI V) (VocabularyLiteral V) B₂) :
    DEntails.{u} T D (G.mapNames Subtype.val Subtype.val) (E.generalize.mapNames Subtype.val Subtype.val) ↔
      ∀ (U : Type u) (P : PreInterpretation V U), PreInterpretation.DModel P T D →
        P.Satisfies G → P.Satisfies E.generalize := by
  constructor
  · intro h U P hP hg
    obtain ⟨ρ, hρ⟩ := hP
    let I := DatatypeCompletion.interpretation P T D ρ
    have hi : I.DModel T D := ⟨ρ.complete, DatatypeCompletion.conditions P hρ⟩
    exact (DatatypeCompletion.ordinary_satisfies_iff P hρ E).mp
      (h _ I hi (DatatypeCompletion.satisfies_forward P hρ G hg))
  · intro h U I hI hg
    let P := I.comapNames (fun i : VocabularyIRI V => i.val) (fun l : VocabularyLiteral V => l.val)
    obtain ⟨ρ, hρ⟩ := hI
    have hp : PreInterpretation.DModel P T D := ⟨ρ, PreInterpretation.conditions_of_full I hρ⟩
    exact (I.satisfies_mapNames _ _ E.generalize).mpr (h U P hp ((I.satisfies_mapNames _ _ G).mp hg))

/-- Combine full completion with finite compression; the conclusion stays ordinary. -/
theorem d_entailment_iff_bounded_preinterpretations_ordinary (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (V : Set (Name Iri Literal)) (S : Set B₁)
    (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B₁) (E : Graph Iri Literal B₂)
    (hG : Set.subset (G.vocabulary T.literalSyntax.datatype) V)
    (hE : Set.subset (E.generalize.vocabulary T.literalSyntax.datatype) V)
    (hB : Set.subset G.hasBlank S) :
    DEntails.{u} T D G E.generalize ↔
      ∀ (U : Type u) (P : PreInterpretation V U),
        P.BoundedDomain (v.triples.length + b.triples.length + 1) →
        PreInterpretation.DModel P T D →
        P.Satisfies (G.restrictNames T.literalSyntax.datatype V hG) →
        P.Satisfies (E.generalize.restrictNames T.literalSyntax.datatype V hE) := by
  constructor
  · intro h U P _ hP hg
    obtain ⟨ρ, hρ⟩ := hP
    let I := DatatypeCompletion.interpretation P T D ρ
    let E₀ := E.restrictNames T.literalSyntax.datatype V hE
    have hI : I.DModel T D := ⟨ρ.complete, DatatypeCompletion.conditions P hρ⟩
    have hginc := G.include_restrictNames T.literalSyntax.datatype V hG
    have he := E.generalize_restrictNames T.literalSyntax.datatype V hE
    have heinc : E₀.generalize.mapNames Subtype.val Subtype.val = E.generalize := by
      rw [Graph.generalize_restrictNames]
      exact E.generalize.include_restrictNames T.literalSyntax.datatype V hE
    have hIG : I.Satisfies G := (congrArg (fun X => I.Satisfies X) hginc).mp
      (DatatypeCompletion.satisfies_forward P hρ _ hg)
    have hIE := h _ I hI hIG
    have hPE := (DatatypeCompletion.ordinary_satisfies_iff P hρ E₀).mp
      ((congrArg (fun X => I.Satisfies X) heinc).mpr hIE)
    exact (congrArg (fun X => P.Satisfies X) he).mp hPE
  · exact d_entailment_of_bounded_preinterpretations T D v b G E.generalize hG hE hB

end RDF11
