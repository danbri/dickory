/-
RDF 1.1 Semantics §9, rdfssemcond1. Its langString extension is the image
of actual tagged literals, while §8 requires all recognized values. These
two conditions impose a representation obligation on an abstract Literal
parameter. This file derives that obligation; it does not assume a model exists.
-/
import RDF11.RDFModels
import RDF11.RDFSRules

namespace RDF11
namespace SimpleInterpretation

variable {Iri Literal Value : Type} {U : Type u}
variable {T : DatatypeTheory Iri Literal Value} {D : Set Iri}
variable {v : RDFSVocabulary Iri} {ρ : ValueRealization Value U}

/-- Every permitted language value must have a literal representative in any RDFS model. -/
theorem rdfs_language_literal_coverage (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (w : Value) (hw : T.languageSpace w) :
    ∃ l tag, T.literalSyntax.language l = some tag ∧
      T.languageValue (T.literalSyntax.lexical l) (asciiLower tag) = w := by
  have hspace : T.recognizedSpace (v.iri (.rdf .rdfLangString)) w := by
    have he := h.rdf.language_iri
    change T.literalSyntax.langString = v.iri (.rdf .rdfLangString) at he
    simpa [← he, T.recognizedSpace_language] using hw
  obtain ⟨x, hx⟩ := h.rdf.values_realized _ h.rdf.recognize_language w hspace
  have ht := (h.rdf.datatype_extension _ h.rdf.recognize_language x).mpr ⟨w, hspace, hx⟩
  obtain ⟨l, tag, htag, r, hr, he⟩ := (h.language_extension x).mp ht
  have hd : D T.literalSyntax.langString := h.rdf.language_iri ▸ h.rdf.recognize_language
  obtain ⟨s, hs, hv⟩ := h.rdf.datatypes.language l tag hd htag
  have hsr : s = r := Option.some.inj (hs.symm.trans hr)
  refine ⟨l, tag, htag, ?_⟩
  apply ρ.injective _ _ x _ hx
  simpa [hsr, he] using hv

theorem rdfsModel_language_literal_coverage (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSModel T D v) (w : Value) (hw : T.languageSpace w) :
    ∃ l tag, T.literalSyntax.language l = some tag ∧
      T.languageValue (T.literalSyntax.lexical l) (asciiLower tag) = w := by
  obtain ⟨ρ, hρ⟩ := h
  exact I.rdfs_language_literal_coverage hρ w hw

end SimpleInterpretation

theorem rdfs_unsatisfiable_of_missing_language_literal (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (v : RDFSVocabulary Iri) (w : Value) (hw : T.languageSpace w)
    (hmissing : ¬ ∃ l tag, T.literalSyntax.language l = some tag ∧
      T.languageValue (T.literalSyntax.lexical l) (asciiLower tag) = w)
    (G : GeneralizedGraph Iri Literal B) : RDFSUnsatisfiable.{u} T D v G := by
  rintro ⟨U, I, hI, _⟩
  exact hmissing (I.rdfsModel_language_literal_coverage hI w hw)

theorem rdf_unsatisfiable_implies_rdfs_unsatisfiable
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B) (h : RDFUnsatisfiable.{u} T D v.toRDF G) :
    RDFSUnsatisfiable.{u} T D v G := by
  rintro ⟨U, I, hI, hG⟩
  exact h ⟨U, I, I.rdfsModel_is_rdfModel hI, hG⟩

end RDF11
