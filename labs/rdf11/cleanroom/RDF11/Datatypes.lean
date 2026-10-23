/-
RDF 1.1 Semantics §7–7.2. D is a set of recognized IRIs; the datatype
identification and lexical-to-value functions are fixed external parameters.
One shared value domain permits overlapping datatype value spaces and aliases.
The D-table predicate deliberately does not add a langString referent equality.
-/
import RDF11.Transformations
import RDF11.Vocabulary

namespace RDF11

/-- Lean's Char.toLower changes ASCII uppercase letters only. -/
def asciiLower (s : String) : String := s.map Char.toLower

structure LiteralSyntax (Iri Literal : Type) where
  langString : Iri
  lexical : Literal → String
  datatype : Literal → Iri
  language : Literal → Option String
  languageTag : Set String
  tag_valid : ∀ l tag, language l = some tag → languageTag tag
  lower_valid : ∀ tag, languageTag tag → languageTag (asciiLower tag)
  tagged_iff : ∀ l, (∃ tag, language l = some tag) ↔ datatype l = langString

/-- These functions are fixed across models; no particular XSD implementation is assumed. -/
structure DatatypeTheory (Iri Literal Value : Type) where
  literalSyntax : LiteralSyntax Iri Literal
  identified : Iri → Value
  L2V : Value → String → Option Value
  languageValue : String → String → Value
  language_injective : ∀ s t s' t', languageValue s t = languageValue s' t' → s = s' ∧ t = t'

namespace DatatypeTheory

def lexicalSpace (T : DatatypeTheory Iri Literal Value) (d : Value) : Set String :=
  fun s => ∃ v, T.L2V d s = some v

def valueSpace (T : DatatypeTheory Iri Literal Value) (d : Value) : Set Value :=
  fun v => ∃ s, T.L2V d s = some v

def languageSpace (T : DatatypeTheory Iri Literal Value) : Set Value :=
  fun v => ∃ s tag, T.literalSyntax.languageTag tag ∧ T.languageValue s (asciiLower tag) = v

/-- langString has its pair value space, with no L2V application. -/
def recognizedSpace (T : DatatypeTheory Iri Literal Value) (a : Iri) : Set Value := by
  classical
  exact if a = T.literalSyntax.langString then T.languageSpace else T.valueSpace (T.identified a)

def IllTyped (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (l : Literal) : Prop :=
  D (T.literalSyntax.datatype l) ∧ T.literalSyntax.datatype l ≠ T.literalSyntax.langString ∧
    T.L2V (T.identified (T.literalSyntax.datatype l)) (T.literalSyntax.lexical l) = none

theorem language_not_illTyped (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (l : Literal) (h : T.literalSyntax.datatype l = T.literalSyntax.langString) : ¬ T.IllTyped D l :=
  fun hi => hi.2.1 h

theorem unrecognized_not_illTyped (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (l : Literal) (h : ¬ D (T.literalSyntax.datatype l)) : ¬ T.IllTyped D l := fun hi => h hi.1

end DatatypeTheory

/-- Only values actually needed by recognized datatypes must be realized.
This permits the empty recognition set without enlarging every model carrier. -/
structure ValueRealization (Value : Type) (U : Type u) where
  value : Value → Option U
  injective : ∀ v w x, value v = some x → value w = some x → v = w

def ValueRealization.empty : ValueRealization Value U where
  value := fun _ => none
  injective := fun _ _ _ h => by cases h

namespace SimpleInterpretation

def LiteralValue (I : SimpleInterpretation Iri Literal U) (ρ : ValueRealization Value U)
    (l : Literal) (v : Value) : Prop :=
  ∃ r : I.Resource, I.IL l = some r ∧ ρ.value v = some r.val

structure DConditions (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (ρ : ValueRealization Value U) : Prop where
  language : ∀ l tag, D T.literalSyntax.langString → T.literalSyntax.language l = some tag →
    I.LiteralValue ρ l (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag))
  ordinary : ∀ a, D a → a ≠ T.literalSyntax.langString →
    ρ.value (T.identified a) = some (I.IS a).val ∧
    ∀ l, T.literalSyntax.datatype l = a →
      match T.L2V (T.identified a) (T.literalSyntax.lexical l) with
      | none => I.IL l = none
      | some v => I.LiteralValue ρ l v

def DModel (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) : Prop :=
  ∃ ρ, I.DConditions T D ρ

theorem dConditions_empty (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) : I.DConditions T Set.empty ValueRealization.empty := by
  constructor
  · intro _ _ h; exact False.elim h
  · intro _ h; exact False.elim h

theorem dModel_empty (I : SimpleInterpretation Iri Literal U) (T : DatatypeTheory Iri Literal Value) :
    I.DModel T Set.empty := ⟨_, I.dConditions_empty T⟩

theorem dConditions_restrict (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T E ρ) (hDE : Set.subset D E) : I.DConditions T D ρ where
  language := fun l tag hd ht => h.language l tag (hDE _ hd) ht
  ordinary := fun a hd hn => h.ordinary a (hDE _ hd) hn

theorem dModel_restrict (I : SimpleInterpretation Iri Literal U)
    (h : I.DModel T E) (hDE : Set.subset D E) : I.DModel T D := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, I.dConditions_restrict hρ hDE⟩

theorem illTyped_undefined (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T D ρ) (hi : T.IllTyped D l) : I.IL l = none := by
  have hl := (h.ordinary (T.literalSyntax.datatype l) hi.1 hi.2.1).2 l rfl
  simpa only [hi.2.2] using hl

theorem literalValue_unique (I : SimpleInterpretation Iri Literal U)
    (hl : I.LiteralValue ρ l v) (hk : I.LiteralValue ρ k v) : I.IL l = I.IL k := by
  obtain ⟨r, hr, hv⟩ := hl
  obtain ⟨s, hs, hv'⟩ := hk
  have he : r.val = s.val := Option.some.inj (hv.symm.trans hv')
  exact hr.trans ((congrArg some (Subtype.ext he)).trans hs.symm)

theorem same_value_literals (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T D ρ) (ha : D a) (hb : D b)
    (hna : a ≠ T.literalSyntax.langString) (hnb : b ≠ T.literalSyntax.langString)
    (hl : T.literalSyntax.datatype l = a) (hk : T.literalSyntax.datatype k = b)
    (hv : T.L2V (T.identified a) (T.literalSyntax.lexical l) = some v)
    (hw : T.L2V (T.identified b) (T.literalSyntax.lexical k) = some v) : I.IL l = I.IL k := by
  have hvl := (h.ordinary a ha hna).2 l hl
  have hvk := (h.ordinary b hb hnb).2 k hk
  rw [hv] at hvl
  rw [hw] at hvk
  exact I.literalValue_unique hvl hvk

/-- A recognized defined literal realizes a value in its datatype's space. -/
theorem recognized_literal_value (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T D ρ) (hd : D (T.literalSyntax.datatype l))
    (r : I.Resource) (hr : I.IL l = some r) :
    ∃ v, T.recognizedSpace (T.literalSyntax.datatype l) v ∧ ρ.value v = some r.val := by
  classical
  by_cases hlang : T.literalSyntax.datatype l = T.literalSyntax.langString
  · obtain ⟨tag, htag⟩ := (T.literalSyntax.tagged_iff l).mpr hlang
    obtain ⟨s, hs, hv⟩ := h.language l tag (hlang ▸ hd) htag
    have he : s = r := Option.some.inj (hs.symm.trans hr)
    refine ⟨T.languageValue (T.literalSyntax.lexical l) (asciiLower tag), ?_, he ▸ hv⟩
    simp only [DatatypeTheory.recognizedSpace, hlang, ↓reduceIte]
    exact ⟨T.literalSyntax.lexical l, tag, T.literalSyntax.tag_valid l tag htag, rfl⟩
  · have hl := (h.ordinary _ hd hlang).2 l rfl
    cases hv : T.L2V (T.identified (T.literalSyntax.datatype l)) (T.literalSyntax.lexical l) with
    | none => simp [hv, hr] at hl
    | some v =>
      rw [hv] at hl
      obtain ⟨s, hs, hvs⟩ := hl
      have he : s = r := Option.some.inj (hs.symm.trans hr)
      refine ⟨v, ?_, he ▸ hvs⟩
      simp only [DatatypeTheory.recognizedSpace, hlang, ↓reduceIte]
      exact ⟨T.literalSyntax.lexical l, hv⟩

theorem literal_object_congruence (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (s p : Term Iri Literal B) (he : I.IL l = I.IL k) :
    I.TripleTrue A ⟨s, p, .literal l⟩ ↔ I.TripleTrue A ⟨s, p, .literal k⟩ := by
  simp only [TripleTrue, denote, he]

end SimpleInterpretation

def DEntails.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) : Prop :=
  EntailsUnder.{u} (fun _ I => I.DModel T D) G E

def DSatisfiable.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) : Prop :=
  ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.DModel T D ∧ I.Satisfies G

def DUnsatisfiable.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) : Prop := ¬ DSatisfiable.{u} T D G

theorem simple_implies_d_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (h : SimplyEntails.{u} G E) : DEntails.{u} T D G E :=
  extension_preserves_simple_entailment _ h

theorem d_empty_iff_simple (T : DatatypeTheory Iri Literal Value)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    DEntails.{u} T Set.empty G E ↔ SimplyEntails.{u} G E := by
  constructor
  · exact fun h U I => h U I (I.dModel_empty T)
  · exact simple_implies_d_entailment T Set.empty

theorem d_entailment_monotone (T : DatatypeTheory Iri Literal Value)
    (hDE : Set.subset D E) (h : DEntails.{u} T D G H) : DEntails.{u} T E G H :=
  stronger_conditions_preserve_entailment (fun _ I hI => I.dModel_restrict hI hDE) h

theorem illTyped_graph_unsatisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) (t : GeneralizedTriple Iri Literal B)
    (ht : G t) (hl : t.hasLiteral l) (hi : T.IllTyped D l) : DUnsatisfiable.{u} T D G := by
  rintro ⟨U, I, ⟨ρ, hρ⟩, hG⟩
  exact I.graph_with_undefined_literal_false G l (I.illTyped_undefined hρ hi) t ht hl hG

theorem d_ex_falso (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (h : DUnsatisfiable.{u} T D G) (E : GeneralizedGraph Iri Literal B₂) : DEntails.{u} T D G E :=
  fun U I hI hG => False.elim (h ⟨U, I, hI, hG⟩)

theorem d_literal_object_substitution (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) (s p : Term Iri Literal B)
    (ht : G ⟨s, p, .literal l⟩) (ha : D a) (hb : D b)
    (hna : a ≠ T.literalSyntax.langString) (hnb : b ≠ T.literalSyntax.langString)
    (hl : T.literalSyntax.datatype l = a) (hk : T.literalSyntax.datatype k = b)
    (hv : T.L2V (T.identified a) (T.literalSyntax.lexical l) = some w)
    (hw : T.L2V (T.identified b) (T.literalSyntax.lexical k) = some w) :
    DEntails.{u} T D G (Set.singleton ⟨s, p, .literal k⟩) := by
  rintro U I ⟨ρ, hρ⟩ hG
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨A, ?_⟩
  rintro _ rfl
  exact (I.literal_object_congruence A s p
    (I.same_value_literals hρ ha hb hna hnb hl hk hv hw)).mp (hA _ ht)

end RDF11
