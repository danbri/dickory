/-
Vocabulary restriction preserves ordinary RDF syntax. These constructions
connect the existing generalized restriction to ordinary conclusion theorems.
-/
import RDF11.Preinterpretations

namespace RDF11

def Subject.restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (s : Subject Iri B) (h : Set.subset (s.toTerm.names datatype) V) : Subject (VocabularyIRI V) B :=
  match s with
  | .iri i => .iri ⟨i, h _ rfl⟩
  | .blank b => .blank b

theorem Subject.toTerm_restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (s : Subject Iri B) (h : Set.subset (s.toTerm.names datatype) V) :
    (s.restrictNames datatype V h).toTerm = s.toTerm.restrictNames datatype V h := by
  cases s <;> rfl

def Triple.restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (t : Triple Iri Literal B) (h : Set.subset (t.generalize.names datatype) V) :
    Triple (VocabularyIRI V) (VocabularyLiteral V) B :=
  ⟨t.subject.restrictNames datatype V (fun n hn => h n (Or.inl hn)),
   ⟨t.predicate, h _ (Or.inr (Or.inl rfl))⟩,
   t.object.restrictNames datatype V (fun n hn => h n (Or.inr (Or.inr hn)))⟩

theorem Triple.generalize_restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (t : Triple Iri Literal B) (h : Set.subset (t.generalize.names datatype) V) :
    (t.restrictNames datatype V h).generalize = t.generalize.restrictNames datatype V h := by
  cases t with
  | mk s p o => cases s <;> rfl

def Graph.restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (G : Graph Iri Literal B) (h : Set.subset (G.generalize.vocabulary datatype) V) :
    Graph (VocabularyIRI V) (VocabularyLiteral V) B :=
  fun q => ∃ (t : Triple Iri Literal B) (ht : G t),
    t.restrictNames datatype V (fun n hn => h n ⟨t.generalize, ⟨t, ht, rfl⟩, hn⟩) = q

theorem Graph.generalize_restrictNames (datatype : Literal → Iri) (V : Set (Name Iri Literal))
    (G : Graph Iri Literal B) (h : Set.subset (G.generalize.vocabulary datatype) V) :
    (G.restrictNames datatype V h).generalize = G.generalize.restrictNames datatype V h := by
  apply Set.ext
  intro q
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t.generalize, ⟨t, ht, rfl⟩, (t.generalize_restrictNames datatype V _).symm⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, t.generalize_restrictNames datatype V _⟩

end RDF11
