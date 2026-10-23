/-
RDF 1.1 Semantics §4: names and vocabularies. Literal datatype IRIs contribute
names even when they are not separate triple terms. The datatype projection is
an explicit parameter until concrete RDF literals are defined.
-/
import RDF11.Syntax

namespace RDF11

abbrev Name (Iri Literal : Type) := Sum Iri Literal

def Term.names (datatype : Literal → Iri) : Term Iri Literal B → Set (Name Iri Literal)
  | .iri i => fun n => n = .inl i
  | .literal l => fun n => n = .inr l ∨ n = .inl (datatype l)
  | .blank _ => Set.empty

def GeneralizedTriple.names (datatype : Literal → Iri)
    (t : GeneralizedTriple Iri Literal B) : Set (Name Iri Literal) :=
  fun n => t.subject.names datatype n ∨ t.predicate.names datatype n ∨ t.object.names datatype n

def GeneralizedGraph.vocabulary (datatype : Literal → Iri)
    (G : GeneralizedGraph Iri Literal B) : Set (Name Iri Literal) :=
  fun n => ∃ t, G t ∧ t.names datatype n

theorem literal_contributes_two_names (datatype : Literal → Iri) (l : Literal) :
    (Term.literal l : Term Iri Literal B).names datatype (.inr l) ∧
    (Term.literal l : Term Iri Literal B).names datatype (.inl (datatype l)) :=
  ⟨Or.inl rfl, Or.inr rfl⟩

end RDF11
