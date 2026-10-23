/-
RDF 1.1 Semantics §8.1.1. The rdfD1 conclusion uses one fresh witness
shared by both triples. A disjoint sum makes freshness structural.
-/
import RDF11.RDF

namespace RDF11

/-- Appendix A's generalized rule retains the literal as the subject. -/
theorem SimpleInterpretation.GrdfD1_triple (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (A : I.Assignment B)
    (t : GeneralizedTriple Iri Literal B) (ht : I.TripleTrue A t)
    (hl : t.hasLiteral l) (hd : D (T.literalSyntax.datatype l)) :
    I.TripleTrue A ⟨.literal l, .iri (v.iri .rdfType), .iri (T.literalSyntax.datatype l)⟩ := by
  cases hv : I.IL l with
  | none => exact False.elim (I.undefined_literal_any_position A l hv t hl ht)
  | some r =>
    apply I.tripleTrue_of_relates A _ (s := r.val) rfl (by simp [SimpleInterpretation.denote, hv]) rfl
    exact I.rdf_literal_typing h hd r hv

def literalTypingImage (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B) : GeneralizedGraph Iri Literal B :=
  fun t => ∃ s p l, G ⟨s, p, .literal l⟩ ∧ D (T.literalSyntax.datatype l) ∧
    t = ⟨.literal l, .iri (v.iri .rdfType), .iri (T.literalSyntax.datatype l)⟩

theorem GrdfD1 (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    RDFEntails.{u} T D v G (literalTypingImage T D v G) := by
  rintro U I ⟨ρ, hρ⟩ hG
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨A, ?_⟩
  rintro _ ⟨s, p, l, ht, hd, rfl⟩
  exact I.GrdfD1_triple hρ A _ (hA _ ht) (Or.inr (Or.inr rfl)) hd

def rdfD1Conclusion (v : RDFVocabulary Iri) (datatype : Iri)
    (s p : Term Iri Literal B) : GeneralizedGraph Iri Literal (Sum B Unit) :=
  Set.union
    (Set.singleton ⟨s.mapBlank Sum.inl, p.mapBlank Sum.inl, .blank (.inr ())⟩)
    (Set.singleton ⟨.blank (.inr ()), .iri (v.iri .rdfType), .iri datatype⟩)

theorem rdfD1 (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s p : Term Iri Literal B) (l : Literal)
    (ht : G ⟨s, p, .literal l⟩) (hd : D (T.literalSyntax.datatype l)) :
    RDFEntails.{u} T D v G (rdfD1Conclusion v (T.literalSyntax.datatype l) s p) := by
  rintro U I ⟨ρ, hρ⟩ hG
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  obtain ⟨q, x, r, hp, hs, hl, hrel⟩ := hA _ ht
  have hil : I.IL l = some r := by
    cases hv : I.IL l with
    | none => simp [SimpleInterpretation.denote, hv] at hl
    | some r' =>
      have he : r'.val = r.val := by simpa [SimpleInterpretation.denote, hv] using hl
      exact congrArg some (Subtype.ext he)
  let A' : I.Assignment (Sum B Unit) := Sum.elim A (fun _ => some r)
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨A', ?_⟩
  intro t ht'
  rcases ht' with rfl | rfl
  · exact ⟨q, x, r, (I.denote_mapBlank Sum.inl A' p).trans hp,
      (I.denote_mapBlank Sum.inl A' s).trans hs, rfl, hrel⟩
  · apply I.tripleTrue_of_relates A' _ rfl rfl rfl
    exact I.rdf_literal_typing hρ hd r hil

theorem rdf_illTyped_unsatisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (t : GeneralizedTriple Iri Literal B) (ht : G t) (hl : t.hasLiteral l)
    (hi : T.IllTyped D l) : RDFUnsatisfiable.{u} T D v G := by
  rintro ⟨U, I, hI, hG⟩
  exact illTyped_graph_unsatisfiable T D G t ht hl hi ⟨U, I, I.rdfModel_is_dModel hI, hG⟩

end RDF11
