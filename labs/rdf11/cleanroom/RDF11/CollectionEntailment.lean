/-
Appendix D.3 typing consequences use the existing full RDFS axioms and rules.
They impose no collection well-formedness conditions.
-/
import RDF11.RDFSRules
namespace RDF11

theorem vocabulary_domain_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (hpc : (p, c) ∈ rdfsDomainAxioms)
    (s o : Term Iri Literal B) (hg : G ⟨s, .iri (v.iri p), o⟩) :
    RDFSDerives T D v G ⟨s, .iri (v.iri (.rdf .rdfType)), .iri (v.iri c)⟩ := by
  let H := RDFSDerives T D v G
  have ha : H ⟨.iri (v.iri p), .iri (v.iri .domain), .iri (v.iri c)⟩ :=
    .rdfsAxiom ⟨p, .domain, c, Or.inl ⟨rfl, hpc⟩, rfl⟩
  exact ha.domain (.premise hg)

theorem vocabulary_range_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (hpc : (p, c) ∈ rdfsRangeAxioms)
    (s o : Term Iri Literal B) (hg : G ⟨s, .iri (v.iri p), o⟩) :
    RDFSDerives T D v G ⟨o, .iri (v.iri (.rdf .rdfType)), .iri (v.iri c)⟩ := by
  let H := RDFSDerives T D v G
  have ha : H ⟨.iri (v.iri p), .iri (v.iri .range), .iri (v.iri c)⟩ :=
    .rdfsAxiom ⟨p, .range, c, Or.inr (Or.inl ⟨rfl, hpc⟩), rfl⟩
  exact ha.range (.premise hg)

theorem collection_first_subject_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s o : Term Iri Literal B) (hg : G ⟨s, .iri (v.iri (.rdf .rdfFirst)), o⟩) :
    RDFSDerives T D v G ⟨s, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩ :=
  vocabulary_domain_derivable T D v G _ _ (by simp [rdfsDomainAxioms]) s o hg

theorem collection_rest_typing_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s o : Term Iri Literal B) (hg : G ⟨s, .iri (v.iri (.rdf .rdfRest)), o⟩) :
    RDFSDerives T D v G ⟨s, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩ ∧
    RDFSDerives T D v G ⟨o, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩ :=
  ⟨vocabulary_domain_derivable T D v G _ _ (by simp [rdfsDomainAxioms]) s o hg,
   vocabulary_range_derivable T D v G _ _ (by simp [rdfsRangeAxioms]) s o hg⟩

theorem collection_first_subject_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s o : Term Iri Literal B) (hg : G ⟨s, .iri (v.iri (.rdf .rdfFirst)), o⟩) :
    RDFSEntails.{u} T D v G
      (Set.singleton ⟨s, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩) := by
  apply rdfs_derives_entailment T D v G _
  rintro _ rfl
  exact collection_first_subject_derivable T D v G s o hg

theorem collection_rest_typing_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s o : Term Iri Literal B) (hg : G ⟨s, .iri (v.iri (.rdf .rdfRest)), o⟩) :
    RDFSEntails.{u} T D v G (Set.ofList [
      ⟨s, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩,
      ⟨o, .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩]) := by
  apply rdfs_derives_entailment T D v G _
  intro t ht
  obtain ⟨hs, ho⟩ := collection_rest_typing_derivable T D v G s o hg
  simp [Set.ofList] at ht
  rcases ht with rfl | rfl
  · exact hs
  · exact ho

theorem collection_nil_typing_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    RDFSDerives T D v G
      ⟨.iri (v.iri (.rdf .rdfNil)), .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfList))⟩ :=
  .rdfAxiom (Or.inr rfl)

end RDF11
