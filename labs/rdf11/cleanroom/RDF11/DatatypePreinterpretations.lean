/-
RDF 1.1 Semantics, informative Appendix B, datatype paragraph, read with §7.
Only vocabulary literals impose literal-value obligations; recognized names
still denote their fixed datatype identities. This makes the sketch precise
using §5's IR/IP distinction and partial IL. Completion is a separate obligation.
-/
import RDF11.Datatypes
import RDF11.Preinterpretations
import RDF11.DomainRestriction

namespace RDF11

namespace PreInterpretation

variable {Iri Literal Value : Type} {U : Type u} {V : Set (Name Iri Literal)}

/-- Localized §7 obligations, with the original external datatype theory. -/
structure DConditions (P : PreInterpretation V U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (ρ : ValueRealization Value U) : Prop where
  recognized_denotation : ∀ a : VocabularyIRI V, D a.val →
    ρ.value (T.identified a.val) = some (P.IS a).val
  language : ∀ (l : VocabularyLiteral V) tag, D T.literalSyntax.langString →
    T.literalSyntax.language l.val = some tag →
    P.LiteralValue ρ l (T.languageValue (T.literalSyntax.lexical l.val) (asciiLower tag))
  ordinary : ∀ l : VocabularyLiteral V, D (T.literalSyntax.datatype l.val) →
    T.literalSyntax.datatype l.val ≠ T.literalSyntax.langString →
    match T.L2V (T.identified (T.literalSyntax.datatype l.val)) (T.literalSyntax.lexical l.val) with
    | none => P.IL l = none
    | some v => P.LiteralValue ρ l v

def DModel (P : PreInterpretation V U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) : Prop :=
  ∃ ρ, DConditions P T D ρ

theorem conditions_of_full (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T D ρ) :
    DConditions (I.comapNames (fun i : VocabularyIRI V => i.val)
      (fun l : VocabularyLiteral V => l.val)) T D ρ where
  recognized_denotation := fun _a ha => I.recognized_datatype_denotation h ha
  language := fun l tag hd ht => h.language l.val tag hd ht
  ordinary := fun l hd hn => (h.ordinary _ hd hn).2 l.val rfl

/-- If the vocabulary includes every name, localization loses no §7 condition. -/
theorem conditions_full_iff (I : SimpleInterpretation Iri Literal U)
    (hI : ∀ i, V (.inl i)) (hL : ∀ l, V (.inr l)) :
    DConditions (I.comapNames (fun i : VocabularyIRI V => i.val)
      (fun l : VocabularyLiteral V => l.val)) T D ρ ↔ I.DConditions T D ρ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact fun hd => h.recognized_denotation ⟨_, hI _⟩ hd
    · exact fun l tag hd ht => h.language ⟨l, hL l⟩ tag hd ht
    · intro a hd hn
      refine ⟨h.recognized_denotation ⟨a, hI a⟩ hd, ?_⟩
      intro l hl
      have hc := h.ordinary ⟨l, hL l⟩ (hl.symm ▸ hd) (fun he => hn (hl.symm.trans he))
      cases he : T.L2V (T.identified a) (T.literalSyntax.lexical l) <;>
        simpa only [hl, he, SimpleInterpretation.comapNames, SimpleInterpretation.LiteralValue,
          Function.comp_apply] using hc
  · exact conditions_of_full I

theorem conditions_empty (P : PreInterpretation V U)
    (T : DatatypeTheory Iri Literal Value) : DConditions P T Set.empty ValueRealization.empty := by
  constructor
  · intro _ h; exact False.elim h
  · intro _ _ h; exact False.elim h
  · intro _ h; exact False.elim h

theorem recognized_aliases (P : PreInterpretation V U) (h : DConditions P T D ρ)
    (a b : VocabularyIRI V) (ha : D a.val) (hb : D b.val)
    (he : T.identified a.val = T.identified b.val) : (P.IS a).val = (P.IS b).val := by
  have hda := h.recognized_denotation a ha
  have hdb := h.recognized_denotation b hb
  rw [he, hdb] at hda
  exact (Option.some.inj hda).symm

theorem illTyped_undefined (P : PreInterpretation V U) (h : DConditions P T D ρ)
    (l : VocabularyLiteral V) (hi : T.IllTyped D l.val) : P.IL l = none := by
  have hc := h.ordinary l hi.1 hi.2.1
  simpa only [hi.2.2] using hc

end PreInterpretation

namespace SimpleInterpretation.DomainRestriction

variable {Iri Literal Value : Type} {U : Type u} {I : SimpleInterpretation Iri Literal U}

theorem literalValue_iff (R : I.DomainRestriction) (ρ : ValueRealization Value U)
    (l : Literal) (v : Value) : R.interpretation.LiteralValue ρ l v ↔ I.LiteralValue ρ l v := by
  have hm : (R.interpretation.IL l).map Subtype.val = (I.IL l).map Subtype.val :=
    R.denote_lift (fun _ : Unit => none) (.literal l)
  constructor
  · rintro ⟨r, hr, hv⟩
    have hh : (I.IL l).map Subtype.val = some r.val := hm.symm.trans (by rw [hr]; rfl)
    obtain ⟨s, hs, he⟩ := Option.map_eq_some_iff.mp hh
    exact ⟨s, hs, he.symm ▸ hv⟩
  · rintro ⟨r, hr, hv⟩
    have hh : (R.interpretation.IL l).map Subtype.val = some r.val := hm.trans (by rw [hr]; rfl)
    obtain ⟨s, hs, he⟩ := Option.map_eq_some_iff.mp hh
    exact ⟨s, hs, he.symm ▸ hv⟩

theorem literal_undefined_iff (R : I.DomainRestriction) (l : Literal) :
    R.interpretation.IL l = none ↔ I.IL l = none := by
  have hm : (R.interpretation.IL l).map Subtype.val = (I.IL l).map Subtype.val :=
    R.denote_lift (fun _ : Unit => none) (.literal l)
  cases hl : R.interpretation.IL l <;> cases hr : I.IL l <;> simp_all

end SimpleInterpretation.DomainRestriction

namespace PreInterpretation

variable {Iri Literal Value : Type} {U : Type u} {V : Set (Name Iri Literal)}

/-- Retaining all local name values retains the localized datatype conditions. -/
theorem conditions_domainRestriction (P : PreInterpretation V U) (R : P.DomainRestriction)
    (h : DConditions P T D ρ) : DConditions R.interpretation T D ρ where
  recognized_denotation := h.recognized_denotation
  language := fun l tag hd ht => (R.literalValue_iff ρ l _).mpr (h.language l tag hd ht)
  ordinary := by
    intro l hd hn
    have hc := h.ordinary l hd hn
    cases he : T.L2V (T.identified (T.literalSyntax.datatype l.val)) (T.literalSyntax.lexical l.val) with
    | none => exact (R.literal_undefined_iff l).mpr (by simpa only [he] using hc)
    | some v => exact (R.literalValue_iff ρ l v).mpr (by simpa only [he] using hc)

end PreInterpretation
end RDF11
