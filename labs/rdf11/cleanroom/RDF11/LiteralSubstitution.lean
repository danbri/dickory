/-
RDF 1.1 Semantics §7.2.1: replacement by recognized equal literal values.
One simultaneous map acts in every position, preserving blank identities.
Images remain sets even when distinct triples acquire the same image.
-/
import RDF11.Datatypes

namespace RDF11

inductive DatatypeTheory.RecognizedValue (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) : Literal → Value → Prop where
  | language (l tag) : D T.literalSyntax.langString → T.literalSyntax.language l = some tag →
      T.RecognizedValue D l (T.languageValue (T.literalSyntax.lexical l) (asciiLower tag))
  | ordinary (l a v) : D a → a ≠ T.literalSyntax.langString → T.literalSyntax.datatype l = a →
      T.L2V (T.identified a) (T.literalSyntax.lexical l) = some v → T.RecognizedValue D l v

theorem SimpleInterpretation.recognizedValue_denotes (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T D ρ) (hv : T.RecognizedValue D l v) : I.LiteralValue ρ l v := by
  cases hv with
  | language tag hd ht => exact h.language l tag hd ht
  | ordinary a v ha hn hl hv =>
    have hi := (h.ordinary a ha hn).2 l hl
    simpa only [hv] using hi

theorem SimpleInterpretation.equal_recognized_values (I : SimpleInterpretation Iri Literal U)
    (h : I.DConditions T D ρ) (hl : T.RecognizedValue D l v) (hk : T.RecognizedValue D k v) :
    I.IL l = I.IL k :=
  I.literalValue_unique (I.recognizedValue_denotes h hl) (I.recognizedValue_denotes h hk)

def Term.mapLiteral (f : Literal → Literal') : Term Iri Literal B → Term Iri Literal' B
  | .iri a => .iri a
  | .literal l => .literal (f l)
  | .blank b => .blank b

def GeneralizedTriple.mapLiteral (f : Literal → Literal') (t : GeneralizedTriple Iri Literal B) :
    GeneralizedTriple Iri Literal' B :=
  ⟨t.subject.mapLiteral f, t.predicate.mapLiteral f, t.object.mapLiteral f⟩

def GeneralizedGraph.mapLiteral (f : Literal → Literal') (G : GeneralizedGraph Iri Literal B) :
    GeneralizedGraph Iri Literal' B := Set.image (GeneralizedTriple.mapLiteral f) G

namespace SimpleInterpretation

theorem denote_mapLiteral (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (f : Literal → Literal) (t : Term Iri Literal B)
    (h : ∀ l, t.hasLiteral l → I.IL (f l) = I.IL l) :
    I.denote A (t.mapLiteral f) = I.denote A t := by
  cases t with
  | iri a => rfl
  | blank b => rfl
  | literal l => simp only [Term.mapLiteral, denote, h l rfl]

theorem tripleTrue_mapLiteral (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (f : Literal → Literal) (t : GeneralizedTriple Iri Literal B)
    (h : ∀ l, t.hasLiteral l → I.IL (f l) = I.IL l) :
    I.TripleTrue A (t.mapLiteral f) ↔ I.TripleTrue A t := by
  have hs := I.denote_mapLiteral A f t.subject (fun l hl => h l (Or.inl hl))
  have hp := I.denote_mapLiteral A f t.predicate (fun l hl => h l (Or.inr (Or.inl hl)))
  have ho := I.denote_mapLiteral A f t.object (fun l hl => h l (Or.inr (Or.inr hl)))
  simp only [TripleTrue, GeneralizedTriple.mapLiteral, hs, hp, ho]

theorem satisfies_mapLiteral_iff (I : SimpleInterpretation Iri Literal U)
    (f : Literal → Literal) (G : GeneralizedGraph Iri Literal B)
    (h : ∀ t, G t → ∀ l, t.hasLiteral l → I.IL (f l) = I.IL l) :
    I.Satisfies (G.mapLiteral f) ↔ I.Satisfies G := by
  rw [I.satisfies_iff_exists_graphTrue, I.satisfies_iff_exists_graphTrue]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, fun t ht => (I.tripleTrue_mapLiteral A f t (h t ht)).mp (hA _ ⟨t, ht, rfl⟩)⟩
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (I.tripleTrue_mapLiteral A f t (h t ht)).mpr (hA t ht)

end SimpleInterpretation

def ValuePreservingLiteralMap (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) (f : Literal → Literal) : Prop :=
  ∀ t, G t → ∀ l, t.hasLiteral l → f l = l ∨
    ∃ v, T.RecognizedValue D l v ∧ T.RecognizedValue D (f l) v

theorem value_preserving_literal_map_satisfaction (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (G : GeneralizedGraph Iri Literal B) (f : Literal → Literal)
    (hf : ValuePreservingLiteralMap T D G f) (I : SimpleInterpretation Iri Literal U)
    (hI : I.DModel T D) : I.Satisfies (G.mapLiteral f) ↔ I.Satisfies G := by
  obtain ⟨ρ, hρ⟩ := hI
  apply I.satisfies_mapLiteral_iff
  intro t ht l hl
  rcases hf t ht l hl with he | ⟨v, hv, hv'⟩
  · exact congrArg I.IL he
  · exact I.equal_recognized_values hρ hv' hv

theorem d_literal_map_equivalent (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (G : GeneralizedGraph Iri Literal B) (f : Literal → Literal)
    (hf : ValuePreservingLiteralMap T D G f) :
    DEntails.{u} T D G (G.mapLiteral f) ∧ DEntails.{u} T D (G.mapLiteral f) G := by
  exact ⟨fun _ I hI => (value_preserving_literal_map_satisfaction T D G f hf I hI).mpr,
    fun _ I hI => (value_preserving_literal_map_satisfaction T D G f hf I hI).mp⟩

end RDF11
