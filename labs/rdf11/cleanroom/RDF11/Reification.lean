/-
RDF 1.1 Semantics Appendix D.1 (informative): ordinary reification syntax.
The printed final blank-node example is retained as a source-review question;
its separately existential singleton conclusion follows in simple semantics.
-/
import RDF11.RDF
import RDF11.Instances

namespace RDF11

/-- The four ordinary RDF triples describing a triple's components. This syntax
construction does not assert that the described triple is true. -/
def Triple.reification (t : Triple Iri Literal B) (v : RDFVocabulary Iri)
    (r : Subject Iri B) : Graph Iri Literal B := Set.ofList [
  ⟨r, v.iri .rdfType, .iri (v.iri .rdfStatement)⟩,
  ⟨r, v.iri .rdfSubject, t.subject.toTerm⟩,
  ⟨r, v.iri .rdfPredicate, .iri t.predicate⟩,
  ⟨r, v.iri .rdfObject, t.object⟩]

namespace ReificationScopeReview

/-- Independent existential conclusion scope permits reuse of a premise witness. -/
theorem blank_property_consequence (G : GeneralizedGraph Iri Literal B₁)
    (x : B₁) (y : B₂) (p o : Iri)
    (hg : G ⟨.blank x, .iri p, .iri o⟩) :
    SimplyEntails.{u} G (Set.singleton
      (⟨.blank y, .iri p, .iri o⟩ : GeneralizedTriple Iri Literal B₂)) := by
  intro U I hG
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => A x, ?_⟩
  rintro _ rfl
  exact hA _ hg

/-- Transcription of Appendix D.1 paragraph 12; false/true name xxx/yyy. -/
def printedPremise (v : RDFVocabulary Iri) (s p o property value : Iri) :
    Graph Iri Literal Bool :=
  let t : Triple Iri Literal Bool := ⟨.iri s, p, .iri o⟩
  Set.union (t.reification v (.blank false)) (Set.union (t.reification v (.blank true))
    (Set.singleton ⟨.blank false, property, .iri value⟩))

/-- The literal standalone conclusion in paragraph 14 follows. This checked
result is evidence for an open source question, not a declared erratum. -/
theorem printed_conclusion_follows (v : RDFVocabulary Iri) (s p o property value : Iri) :
    SimplyEntails.{u} (printedPremise (Literal := Literal) v s p o property value).generalize
      (Set.singleton (⟨.blank true, .iri property, .iri value⟩ : GeneralizedTriple Iri Literal Bool)) := by
  apply blank_property_consequence _ false true property value
  exact ⟨⟨.blank false, property, .iri value⟩, Or.inr (Or.inr rfl), rfl⟩

end ReificationScopeReview
end RDF11
