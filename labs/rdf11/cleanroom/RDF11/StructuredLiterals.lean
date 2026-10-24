/-
RDF 1.1 Concepts §3.3: Unicode lexical form, datatype IRI and optional
well-formed language tag. Raw tag spelling participates in term identity;
ASCII-lower tag values participate in the language datatype's denotation.
IRI syntax remains the explicit Iri parameter. Lexical datatype validity
is not a condition on the formation of an ordinary typed literal.
-/
import RDF11.LanguageTags
import RDF11.LiteralSubstitution
import RDF11.RDFSModels

namespace RDF11

inductive StructuredLiteral (Iri : Type) (langString : Iri) where
  | typed (lexical : String) (datatype : { a : Iri // a ≠ langString })
  | tagged (lexical : String) (tag : BCP47.Tag)
  deriving DecidableEq

namespace StructuredLiteral

variable {Iri : Type} {langString : Iri}

def lexical : StructuredLiteral Iri langString → String
  | .typed s _ | .tagged s _ => s

def datatype : StructuredLiteral Iri langString → Iri
  | .typed _ d => d.val
  | .tagged _ _ => langString

def language : StructuredLiteral Iri langString → Option String
  | .typed _ _ => none
  | .tagged _ tag => some tag.val

theorem typed_fields (s : String) (d : Iri) (hd : d ≠ langString) :
    ∃ l : StructuredLiteral Iri langString,
      l.lexical = s ∧ l.datatype = d ∧ l.language = none :=
  ⟨.typed s ⟨d, hd⟩, rfl, rfl, rfl⟩

theorem tagged_fields (s tag : String) (ht : BCP47.WellFormed tag) :
    ∃ l : StructuredLiteral Iri langString,
      l.lexical = s ∧ l.datatype = langString ∧ l.language = some tag :=
  ⟨.tagged s ⟨tag, ht⟩, rfl, rfl, rfl⟩

theorem eq_iff_fields (l k : StructuredLiteral Iri langString) :
    l = k ↔ l.lexical = k.lexical ∧ l.datatype = k.datatype ∧ l.language = k.language := by
  cases l <;> cases k <;> simp [lexical, datatype, language, Subtype.ext_iff]

theorem language_iff_datatype (l : StructuredLiteral Iri langString) :
    (∃ tag, l.language = some tag) ↔ l.datatype = langString := by
  cases l with
  | typed s d => simp [language, datatype, d.property]
  | tagged s tag => simp [language, datatype]

theorem language_wellFormed (l : StructuredLiteral Iri langString)
    (h : l.language = some tag) : BCP47.WellFormed tag := by
  cases l with
  | typed s d => cases h
  | tagged s t => exact Option.some.inj h ▸ t.property

theorem language_nonempty (l : StructuredLiteral Iri langString)
    (h : l.language = some tag) : tag ≠ "" :=
  BCP47.wellFormed_nonempty (l.language_wellFormed h)

def literalSyntax (langString : Iri) : LiteralSyntax Iri (StructuredLiteral Iri langString) where
  langString := langString
  lexical := lexical
  datatype := datatype
  language := language
  languageTag := BCP47.WellFormed
  tag_valid := fun l _ => language_wellFormed l
  lower_valid := fun _ => BCP47.wellFormed_lower
  tagged_iff := language_iff_datatype

/-- Optional lexical normalization, kept separate from literal identity. -/
def normalize : StructuredLiteral Iri langString → StructuredLiteral Iri langString
  | .typed s d => .typed s d
  | .tagged s t => .tagged s t.normalize

theorem normalize_lexical (l : StructuredLiteral Iri langString) :
    l.normalize.lexical = l.lexical := by cases l <;> rfl

theorem normalize_datatype (l : StructuredLiteral Iri langString) :
    l.normalize.datatype = l.datatype := by cases l <;> rfl

theorem normalize_language (l : StructuredLiteral Iri langString) :
    l.normalize.language = l.language.map asciiLower := by cases l <;> rfl

theorem normalize_idempotent (l : StructuredLiteral Iri langString) :
    l.normalize.normalize = l.normalize := by
  cases l with
  | typed s d => rfl
  | tagged s t => exact congrArg (StructuredLiteral.tagged s) t.normalize_idempotent

theorem language_coverage
    (T : DatatypeTheory Iri (StructuredLiteral Iri langString) Value)
    (hs : T.literalSyntax = literalSyntax langString) :
    RDFSModelConstruction.LanguageCoverage T := by
  rintro w ⟨s, tag, ht, rfl⟩
  have htag : BCP47.WellFormed tag := by simpa [hs, literalSyntax] using ht
  refine ⟨.tagged s ⟨tag, htag⟩, tag, ?_, ?_⟩ <;>
    simp [hs, literalSyntax, language, lexical]

theorem rdfs_base_model_exists
    (T : DatatypeTheory Iri (StructuredLiteral Iri langString) Value)
    (hs : T.literalSyntax = literalSyntax langString) (v : RDFSVocabulary Iri)
    (hlang : langString = v.iri (.rdf .rdfLangString)) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri (StructuredLiteral Iri langString) U),
      I.RDFSModel T v.toRDF.baseDatatypes v := by
  have hi : T.literalSyntax.langString = v.iri (.rdf .rdfLangString) := by
    simpa [hs, literalSyntax] using hlang
  exact (RDFSModelConstruction.base_model_exists_iff_language_coverage T v hi).mpr
    (language_coverage T hs)

theorem normalize_recognized
    (T : DatatypeTheory Iri (StructuredLiteral Iri langString) Value)
    (hs : T.literalSyntax = literalSyntax langString) (D : Set Iri) (hd : D langString)
    (l : StructuredLiteral Iri langString) :
    l.normalize = l ∨ ∃ w, T.RecognizedValue D l w ∧ T.RecognizedValue D l.normalize w := by
  cases l with
  | typed s d => exact Or.inl rfl
  | tagged s t =>
    have hlang : D T.literalSyntax.langString := by simpa [hs, literalSyntax] using hd
    have h₁ := DatatypeTheory.RecognizedValue.language (T := T) (D := D) (.tagged s t) t.val hlang
      (by simp [hs, literalSyntax, language])
    have h₂ := DatatypeTheory.RecognizedValue.language (T := T) (D := D) (.tagged s t.normalize)
      t.normalize.val hlang (by simp [hs, literalSyntax, language])
    refine Or.inr ⟨_, h₁, ?_⟩
    simpa [hs, literalSyntax, lexical, normalize, BCP47.Tag.normalize, BCP47.Tag.value,
      asciiLower_idempotent] using h₂

theorem normalize_value_preserving
    (T : DatatypeTheory Iri (StructuredLiteral Iri langString) Value)
    (hs : T.literalSyntax = literalSyntax langString) (D : Set Iri) (hd : D langString)
    (G : GeneralizedGraph Iri (StructuredLiteral Iri langString) B) :
    ValuePreservingLiteralMap T D G normalize :=
  fun _ _ l _ => normalize_recognized T hs D hd l

theorem normalize_satisfaction
    (T : DatatypeTheory Iri (StructuredLiteral Iri langString) Value)
    (hs : T.literalSyntax = literalSyntax langString) (D : Set Iri) (hd : D langString)
    (G : GeneralizedGraph Iri (StructuredLiteral Iri langString) B)
    (I : SimpleInterpretation Iri (StructuredLiteral Iri langString) U) (hI : I.DModel T D) :
    I.Satisfies (G.mapLiteral normalize) ↔ I.Satisfies G :=
  value_preserving_literal_map_satisfaction T D G normalize
    (normalize_value_preserving T hs D hd G) I hI

theorem normalize_d_equivalent
    (T : DatatypeTheory Iri (StructuredLiteral Iri langString) Value)
    (hs : T.literalSyntax = literalSyntax langString) (D : Set Iri) (hd : D langString)
    (G : GeneralizedGraph Iri (StructuredLiteral Iri langString) B) :
    DEntails.{u} T D G (G.mapLiteral normalize) ∧ DEntails.{u} T D (G.mapLiteral normalize) G :=
  d_literal_map_equivalent T D G normalize (normalize_value_preserving T hs D hd G)

end StructuredLiteral
end RDF11
