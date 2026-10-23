/-
An indexed membership assertion entails generic rdfs:member membership.
The derivation uses the full RDFS axiom family, then rdfs12 and rdfs7.
This also records the positive half of a closure-selection review question.
-/
import RDF11.RDFSRules

namespace RDF11

theorem container_membership_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s o : Term Iri Literal B) (n : Nat) (hg : G ⟨s, .iri (v.iri (.rdf (.container n))), o⟩) :
    RDFSDerives T D v G ⟨s, .iri (v.iri .member), o⟩ := by
  let H := RDFSDerives T D v G
  have hc : H ⟨.iri (v.iri (.rdf (.container n))), .iri (v.iri (.rdf .rdfType)),
      .iri (v.iri .containerMembershipProperty)⟩ := by
    apply RDFSDerives.rdfsAxiom
    exact ⟨.rdf (.container n), .rdf .rdfType, .containerMembershipProperty,
      Or.inr (Or.inr (Or.inr ⟨n, rfl, Or.inl ⟨rfl, rfl⟩⟩)), rfl⟩
  have hp : H ⟨.iri (v.iri (.rdf (.container n))), .iri (v.iri .subPropertyOf), .iri (v.iri .member)⟩ :=
    .rule H (fun _ h => h) (.rdfs12 _ hc)
  exact .rule H (fun _ h => h) (.rdfs7 _ _ s o hp (.premise hg))

theorem container_membership_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s o : Term Iri Literal B) (n : Nat) (hg : G ⟨s, .iri (v.iri (.rdf (.container n))), o⟩) :
    RDFSEntails.{u} T D v G (Set.singleton ⟨s, .iri (v.iri .member), o⟩) := by
  apply rdfs_derives_entailment T D v G _
  rintro _ rfl
  exact container_membership_derivable T D v G s o n hg

end RDF11
