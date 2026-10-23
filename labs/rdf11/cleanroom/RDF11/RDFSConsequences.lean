/-
RDF 1.1 Semantics §9: the additional-valid-triples table contains consequences,
not extra axioms. The twelve core class entries and all nine property entries
are derived below. XMLLiteral/HTML use the separate recognized-datatype result;
their printed unqualified validity remains an explicit source-review question.
-/
import RDF11.RDFSRules

namespace RDF11

/-- Source order, with XMLLiteral and HTML handled separately under recognition. -/
def rdfsAdditionalClassSymbols : List RDFSSymbol := [
  .resource, .class_, .literal, .datatype, .rdf .rdfSeq, .rdf .rdfBag, .rdf .rdfAlt,
  .container, .rdf .rdfList, .containerMembershipProperty, .rdf .rdfProperty, .rdf .rdfStatement]

def rdfsAdditionalPropertySymbols : List RDFSSymbol := [
  .domain, .range, .subPropertyOf, .subClassOf, .member, .seeAlso, .isDefinedBy, .comment, .label]

theorem rdfs_domain_axiom_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (h : (p, c) ∈ rdfsDomainAxioms) :
    RDFSDerives T D v G ⟨.iri (v.iri p), .iri (v.iri .domain), .iri (v.iri c)⟩ :=
  .rdfsAxiom ⟨p, .domain, c, Or.inl ⟨rfl, h⟩, rfl⟩

theorem rdfs_range_axiom_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (h : (p, c) ∈ rdfsRangeAxioms) :
    RDFSDerives T D v G ⟨.iri (v.iri p), .iri (v.iri .range), .iri (v.iri c)⟩ :=
  .rdfsAxiom ⟨p, .range, c, Or.inr (Or.inl ⟨rfl, h⟩), rfl⟩

theorem rdfs_hierarchy_axiom_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (s p o : RDFSSymbol) (h : (s, p, o) ∈ rdfsHierarchyAxioms) :
    RDFSDerives T D v G ⟨.iri (v.iri s), .iri (v.iri p), .iri (v.iri o)⟩ :=
  .rdfsAxiom ⟨s, p, o, Or.inr (Or.inr (Or.inl h)), rfl⟩

theorem rdfs_domain_target_class_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (h : (p, c) ∈ rdfsDomainAxioms) :
    RDFSDerives T D v G ⟨.iri (v.iri c), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ :=
  (rdfs_range_axiom_derivable T D v G .domain .class_ (by simp [rdfsRangeAxioms])).range
    (rdfs_domain_axiom_derivable T D v G p c h)

theorem rdfs_range_target_class_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (h : (p, c) ∈ rdfsRangeAxioms) :
    RDFSDerives T D v G ⟨.iri (v.iri c), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ :=
  (rdfs_range_axiom_derivable T D v G .range .class_ (by simp [rdfsRangeAxioms])).range
    (rdfs_range_axiom_derivable T D v G p c h)

theorem rdfs_additional_class_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (c : RDFSSymbol) (hc : c ∈ rdfsAdditionalClassSymbols) :
    RDFSDerives T D v G ⟨.iri (v.iri c), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ := by
  have sub (s o : RDFSSymbol) (h : (s, .subClassOf, o) ∈ rdfsHierarchyAxioms) :
      RDFSDerives T D v G ⟨.iri (v.iri s), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ :=
    (rdfs_domain_axiom_derivable T D v G .subClassOf .class_ (by simp [rdfsDomainAxioms])).domain
      (rdfs_hierarchy_axiom_derivable T D v G s .subClassOf o h)
  simp only [rdfsAdditionalClassSymbols, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rdfs_domain_target_class_derivable T D v G (.rdf .rdfType) .resource (by simp [rdfsDomainAxioms])
  · exact rdfs_range_target_class_derivable T D v G (.rdf .rdfType) .class_ (by simp [rdfsRangeAxioms])
  · exact rdfs_range_target_class_derivable T D v G .comment .literal (by simp [rdfsRangeAxioms])
  · exact sub .datatype .class_ (by simp [rdfsHierarchyAxioms])
  · exact sub (.rdf .rdfSeq) .container (by simp [rdfsHierarchyAxioms])
  · exact sub (.rdf .rdfBag) .container (by simp [rdfsHierarchyAxioms])
  · exact sub (.rdf .rdfAlt) .container (by simp [rdfsHierarchyAxioms])
  · exact (rdfs_range_axiom_derivable T D v G .subClassOf .class_ (by simp [rdfsRangeAxioms])).range
      (rdfs_hierarchy_axiom_derivable T D v G (.rdf .rdfAlt) .subClassOf .container (by simp [rdfsHierarchyAxioms]))
  · exact rdfs_domain_target_class_derivable T D v G (.rdf .rdfFirst) (.rdf .rdfList) (by simp [rdfsDomainAxioms])
  · apply (rdfs_range_axiom_derivable T D v G (.rdf .rdfType) .class_ (by simp [rdfsRangeAxioms])).range
    exact .rdfsAxiom ⟨.rdf (.container 0), .rdf .rdfType, .containerMembershipProperty,
      Or.inr (Or.inr (Or.inr ⟨0, rfl, Or.inl ⟨rfl, rfl⟩⟩)), rfl⟩
  · exact rdfs_domain_target_class_derivable T D v G .domain (.rdf .rdfProperty) (by simp [rdfsDomainAxioms])
  · exact rdfs_domain_target_class_derivable T D v G (.rdf .rdfSubject) (.rdf .rdfStatement) (by simp [rdfsDomainAxioms])

theorem rdfs_recognized_datatype_class_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) (a : Iri) (ha : D a) :
    RDFSDerives T D v G ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ :=
  (rdfs_hierarchy_axiom_derivable T D v G .datatype .subClassOf .class_ (by simp [rdfsHierarchyAxioms])).subclass
    (.rule (RDFSDerives T D v G) (fun _ h => h) (.rdfs1 a ha))

theorem rdfs_domain_property_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p c : RDFSSymbol) (h : (p, c) ∈ rdfsDomainAxioms) :
    RDFSDerives T D v G ⟨.iri (v.iri p), .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfProperty))⟩ :=
  (rdfs_domain_axiom_derivable T D v G .domain (.rdf .rdfProperty) (by simp [rdfsDomainAxioms])).domain
    (rdfs_domain_axiom_derivable T D v G p c h)

theorem rdfs_additional_property_derivable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (p : RDFSSymbol) (hp : p ∈ rdfsAdditionalPropertySymbols) :
    RDFSDerives T D v G ⟨.iri (v.iri p), .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfProperty))⟩ := by
  have target : ∃ c, (p, c) ∈ rdfsDomainAxioms := by
    simp only [rdfsAdditionalPropertySymbols, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [rdfsDomainAxioms]
  obtain ⟨c, hc⟩ := target
  exact rdfs_domain_property_derivable T D v G p c hc

def RDFSVocabulary.additionalClassTriples (v : RDFSVocabulary Iri) : GeneralizedGraph Iri Literal B :=
  fun t => ∃ c, c ∈ rdfsAdditionalClassSymbols ∧
    t = ⟨.iri (v.iri c), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩

def RDFSVocabulary.additionalPropertyTriples (v : RDFSVocabulary Iri) : GeneralizedGraph Iri Literal B :=
  fun t => ∃ p, p ∈ rdfsAdditionalPropertySymbols ∧
    t = ⟨.iri (v.iri p), .iri (v.iri (.rdf .rdfType)), .iri (v.iri (.rdf .rdfProperty))⟩

theorem rdfs_additional_types_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    RDFSEntails.{u} (B₂ := B) T D v G v.additionalClassTriples := by
  apply rdfs_derives_entailment
  rintro _ ⟨c, hc, rfl⟩
  exact rdfs_additional_class_derivable T D v G c hc

theorem rdfs_additional_properties_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    RDFSEntails.{u} (B₂ := B) T D v G v.additionalPropertyTriples := by
  apply rdfs_derives_entailment
  rintro _ ⟨p, hp, rfl⟩
  exact rdfs_additional_property_derivable T D v G p hp

theorem rdfs_recognized_datatype_class_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B) (a : Iri) (ha : D a) :
    RDFSEntails.{u} (B₂ := B) T D v G
      (Set.singleton ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩) := by
  apply rdfs_derives_entailment
  rintro _ rfl
  exact rdfs_recognized_datatype_class_derivable T D v G a ha

theorem SimpleInterpretation.rdfs_class_self_membership (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSModel T D v) :
    I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .class_)).val (I.IS (v.iri .class_)).val := by
  obtain ⟨ρ, hρ⟩ := h
  have ht := I.rdfs_derivation_sound hρ (fun (_ : Empty) => none)
    (G := Set.empty) (fun _ h => False.elim h)
    (rdfs_additional_class_derivable T D v Set.empty .class_ (by simp [rdfsAdditionalClassSymbols]))
  exact (I.iri_triple_true _ _ _ _).mp ht

theorem SimpleInterpretation.rdfs_resource_nonempty (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSModel T D v) :
    ∃ x, I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .resource)).val x := by
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨x, hx⟩ := I.IR_nonempty
  exact ⟨x, (hρ.resource_extension x).mpr hx⟩

end RDF11
