/-
Finite non-container tables and one finite block per indexed container IRI.
Their partition proofs refer back to the full infinite axiom definitions.
-/
import RDF11.ClosureSeedEvaluation

namespace RDF11.ClosureEvaluation

def rdfProperties : List RDFSymbol :=
  [.rdfType, .rdfSubject, .rdfPredicate, .rdfObject, .rdfFirst, .rdfRest, .rdfValue]

theorem rdfProperty_iff (p : RDFSymbol) :
    p.propertyAxiom ↔ p ∈ rdfProperties ∨ ∃ n, p = .container n := by
  cases p <;> simp [RDFSymbol.propertyAxiom, rdfProperties]

def rdfFixed (v : RDFVocabulary Iri) : List (GeneralizedTriple Iri Literal B) :=
  rdfProperties.map (fun p => ⟨.iri (v.iri p), .iri (v.iri .rdfType), .iri (v.iri .rdfProperty)⟩) ++
    [⟨.iri (v.iri .rdfNil), .iri (v.iri .rdfType), .iri (v.iri .rdfList)⟩]

def rdfIndexed (v : RDFVocabulary Iri) (n : Nat) : List (GeneralizedTriple Iri Literal B) :=
  [⟨.iri (v.iri (.container n)), .iri (v.iri .rdfType), .iri (v.iri .rdfProperty)⟩]

theorem rdf_covers (v : RDFVocabulary Iri) (t : GeneralizedTriple Iri Literal B) :
    v.axioms t ↔ t ∈ rdfFixed v ∨ ∃ n, t ∈ rdfIndexed v n := by
  constructor
  · intro h
    rcases h with ⟨p, hp, rfl⟩ | rfl
    · rcases (rdfProperty_iff p).mp hp with hp | ⟨n, rfl⟩
      · exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
      · exact Or.inr ⟨n, by simp [rdfIndexed]⟩
    · exact Or.inl (List.mem_append_right _ (by simp))
  · rintro (h | ⟨n, h⟩)
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact Or.inl ⟨p, (rdfProperty_iff p).mpr (Or.inl hp), rfl⟩
      · exact Or.inr (List.mem_singleton.mp h)
    · exact Or.inl ⟨.container n, True.intro, List.mem_singleton.mp h⟩

theorem rdf_fixed_names (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (t : GeneralizedTriple Iri Literal B) (ht : t ∈ rdfFixed v) (n : Nat) :
    ¬ t.names datatype (.inl (v.iri (.container n))) := by
  rcases List.mem_append.mp ht with h | h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    cases p <;> simp_all [rdfProperties, GeneralizedTriple.names, Term.names, ClosureBound.rdf_iri_eq]
  · have he := List.mem_singleton.mp h
    subst t
    simp [GeneralizedTriple.names, Term.names, ClosureBound.rdf_iri_eq]

theorem rdf_indexed_names (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (n : Nat) (t : GeneralizedTriple Iri Literal B) (ht : t ∈ rdfIndexed v n) (k : Nat) :
    t.names datatype (.inl (v.iri (.container k))) ↔ k = n := by
  have he := List.mem_singleton.mp ht
  subst t
  simp [GeneralizedTriple.names, Term.names, ClosureBound.rdf_iri_eq]

def rdfAxiomLists (datatype : Literal → Iri) (v : RDFVocabulary Iri) :
    AxiomLists datatype (fun n => v.iri (.container n)) (v.axioms : GeneralizedGraph Iri Literal B) :=
  AxiomLists.ofPartition datatype _ _ (rdfFixed v) (rdfIndexed v) (rdf_covers v)
    (rdf_fixed_names datatype v) (rdf_indexed_names datatype v)

def rdfsFixed (v : RDFSVocabulary Iri) : List (GeneralizedTriple Iri Literal B) :=
  rdfFixed v.toRDF ++
  rdfsDomainAxioms.map (fun (s, o) => ⟨.iri (v.iri s), .iri (v.iri .domain), .iri (v.iri o)⟩) ++
  rdfsRangeAxioms.map (fun (s, o) => ⟨.iri (v.iri s), .iri (v.iri .range), .iri (v.iri o)⟩) ++
  rdfsHierarchyAxioms.map (fun (s, p, o) => ⟨.iri (v.iri s), .iri (v.iri p), .iri (v.iri o)⟩)

def rdfsIndexed (v : RDFSVocabulary Iri) (n : Nat) : List (GeneralizedTriple Iri Literal B) :=
  rdfIndexed v.toRDF n ++
  [⟨.iri (v.iri (.rdf (.container n))), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .containerMembershipProperty)⟩,
   ⟨.iri (v.iri (.rdf (.container n))), .iri (v.iri .domain), .iri (v.iri .resource)⟩,
   ⟨.iri (v.iri (.rdf (.container n))), .iri (v.iri .range), .iri (v.iri .resource)⟩]

theorem rdfs_covers (v : RDFSVocabulary Iri) (t : GeneralizedTriple Iri Literal B) :
    Set.union v.toRDF.axioms v.axioms t ↔ t ∈ rdfsFixed v ∨ ∃ n, t ∈ rdfsIndexed v n := by
  have rdf_fixed (h : t ∈ rdfFixed v.toRDF) : t ∈ rdfsFixed v := by
    simp only [rdfsFixed, List.mem_append]
    exact Or.inl (Or.inl (Or.inl h))
  constructor
  · rintro (h | h)
    · rcases (rdf_covers v.toRDF t).mp h with h | ⟨n, h⟩
      · exact Or.inl (rdf_fixed h)
      · exact Or.inr ⟨n, List.mem_append_left _ h⟩
    · obtain ⟨s, p, o, ha, rfl⟩ := h
      rcases ha with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha | ⟨n, rfl, ha⟩
      · apply Or.inl
        simp only [rdfsFixed, List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨(s, o), ha, rfl⟩)))
      · apply Or.inl
        simp only [rdfsFixed, List.mem_append]
        exact Or.inl (Or.inr (List.mem_map.mpr ⟨(s, o), ha, rfl⟩))
      · apply Or.inl
        simp only [rdfsFixed, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨(s, p, o), ha, rfl⟩)
      · refine Or.inr ⟨n, ?_⟩
        apply List.mem_append_right
        rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rintro (h | ⟨n, h⟩)
    · simp only [rdfsFixed, List.mem_append, or_assoc] at h
      rcases h with h | h | h | h
      · exact Or.inl ((rdf_covers v.toRDF t).mpr (Or.inl h))
      · obtain ⟨⟨s, o⟩, hm, rfl⟩ := List.mem_map.mp h
        exact Or.inr ⟨s, .domain, o, Or.inl ⟨rfl, hm⟩, rfl⟩
      · obtain ⟨⟨s, o⟩, hm, rfl⟩ := List.mem_map.mp h
        exact Or.inr ⟨s, .range, o, Or.inr (Or.inl ⟨rfl, hm⟩), rfl⟩
      · obtain ⟨⟨s, p, o⟩, hm, rfl⟩ := List.mem_map.mp h
        exact Or.inr ⟨s, p, o, Or.inr (Or.inr (Or.inl hm)), rfl⟩
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl ((rdf_covers v.toRDF t).mpr (Or.inr ⟨n, h⟩))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact Or.inr ⟨.rdf (.container n), .rdf .rdfType, .containerMembershipProperty,
            Or.inr (Or.inr (Or.inr ⟨n, rfl, Or.inl ⟨rfl, rfl⟩⟩)), rfl⟩
        · exact Or.inr ⟨.rdf (.container n), .domain, .resource,
            Or.inr (Or.inr (Or.inr ⟨n, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)), rfl⟩
        · exact Or.inr ⟨.rdf (.container n), .range, .resource,
            Or.inr (Or.inr (Or.inr ⟨n, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)), rfl⟩

theorem rdfs_fixed_names (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (t : GeneralizedTriple Iri Literal B) (ht : t ∈ rdfsFixed v) (n : Nat) :
    ¬ t.names datatype (.inl (v.iri (.rdf (.container n)))) := by
  simp only [rdfsFixed, List.mem_append, or_assoc] at ht
  rcases ht with h | h | h | h
  · exact rdf_fixed_names datatype v.toRDF t h n
  · obtain ⟨⟨s, o⟩, hm, rfl⟩ := List.mem_map.mp h
    have hf := ClosureBound.domain_symbols_fixed (s, o) hm
    exact ClosureBound.rdfs_fixed_triple_no_container datatype v s .domain o hf.1
      (by simp [ClosureBound.rdfsFixedSymbols]) hf.2 n
  · obtain ⟨⟨s, o⟩, hm, rfl⟩ := List.mem_map.mp h
    have hf := ClosureBound.range_symbols_fixed (s, o) hm
    exact ClosureBound.rdfs_fixed_triple_no_container datatype v s .range o hf.1
      (by simp [ClosureBound.rdfsFixedSymbols]) hf.2 n
  · obtain ⟨⟨s, p, o⟩, hm, rfl⟩ := List.mem_map.mp h
    have hf := ClosureBound.hierarchy_symbols_fixed (s, p, o) hm
    exact ClosureBound.rdfs_fixed_triple_no_container datatype v s p o hf.1 hf.2.1 hf.2.2 n

theorem rdfs_indexed_names (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (n : Nat) (t : GeneralizedTriple Iri Literal B) (ht : t ∈ rdfsIndexed v n) (k : Nat) :
    t.names datatype (.inl (v.iri (.rdf (.container k)))) ↔ k = n := by
  rcases List.mem_append.mp ht with h | h
  · exact rdf_indexed_names datatype v.toRDF n t h k
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;>
      simp [GeneralizedTriple.names, Term.names, ClosureBound.rdfs_iri_eq]

def rdfsAxiomLists (datatype : Literal → Iri) (v : RDFSVocabulary Iri) :
    AxiomLists datatype (fun n => v.iri (.rdf (.container n)))
      (Set.union v.toRDF.axioms v.axioms : GeneralizedGraph Iri Literal B) :=
  AxiomLists.ofPartition datatype _ _ (rdfsFixed v) (rdfsIndexed v) (rdfs_covers v)
    (rdfs_fixed_names datatype v) (rdfs_indexed_names datatype v)

end RDF11.ClosureEvaluation
