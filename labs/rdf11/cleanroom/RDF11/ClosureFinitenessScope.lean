/-
Appendix A source-scope checks: finite inputs are necessary, and a finite
closure cannot contain every axiom in the infinite RDF vocabulary. These
are qualified results about the formal transcription, not adopted errata.
-/
import RDF11.FiniteClosure
import RDF11.ContainerInfinitude

namespace RDF11.ClosureBound

theorem rdf_closure_contains (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    Set.subset G (RDFClosure T v G E) := fun _ h => .premise (Or.inl h)

theorem rdfs_closure_contains (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    Set.subset G (RDFSClosure T v G E) := fun _ h => .premise (Or.inl h)

theorem rdf_finite_premise_of_finite_closure (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (h : FiniteGraph (RDFClosure T v G E)) : FiniteGraph G := by
  obtain ⟨c⟩ := h
  exact ⟨c.subset G (rdf_closure_contains T v G E)⟩

theorem rdfs_finite_premise_of_finite_closure (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (h : FiniteGraph (RDFSClosure T v G E)) : FiniteGraph G := by
  obtain ⟨c⟩ := h
  exact ⟨c.subset G (rdfs_closure_contains T v G E)⟩

theorem consistent_infinite_closures (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (h : RDFSModelConstruction.Parameters T v.toRDF.baseDatatypes v) :
    let G := (ContainerInfinitude.allIndexed (Literal := Literal) v).generalize
    let E := (Set.empty : GeneralizedGraph Iri Literal Empty)
    (∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T v.toRDF.baseDatatypes v ∧ I.Satisfies G) ∧
    ¬ FiniteGraph (RDFClosure T v.toRDF G E) ∧ ¬ FiniteGraph (RDFSClosure T v G E) :=
  ⟨ContainerInfinitude.allIndexed_satisfiable T _ v h,
    fun hf => ContainerInfinitude.allIndexed_not_finite v
      (rdf_finite_premise_of_finite_closure T v.toRDF _ _ hf),
    fun hf => ContainerInfinitude.allIndexed_not_finite v
      (rdfs_finite_premise_of_finite_closure T v _ _ hf)⟩

def indexedPropertyAxiom (v : RDFVocabulary Iri) (n : Nat) : GeneralizedTriple Iri Literal B :=
  ⟨.iri (v.iri (.container n)), .iri (v.iri .rdfType), .iri (v.iri .rdfProperty)⟩

theorem indexedPropertyAxiom_injective (v : RDFVocabulary Iri) (m n : Nat)
    (h : (indexedPropertyAxiom v m : GeneralizedTriple Iri Literal B) = indexedPropertyAxiom v n) : m = n :=
  v.container_injective m n (Term.iri.inj (congrArg GeneralizedTriple.subject h))

theorem finite_selected_of_typings (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (E : GeneralizedGraph Iri Literal B₂) (C : GeneralizedGraph Iri Literal B₁)
    (hC : FiniteGraph C)
    (h : ∀ n, E.vocabulary datatype (.inl (v.iri (.container n))) → C (indexedPropertyAxiom v n)) :
    Nonempty (Enumeration (fun n => E.vocabulary datatype (.inl (v.iri (.container n))))) := by
  obtain ⟨c⟩ := hC
  obtain ⟨indices⟩ := finite_preimage_injective (indexedPropertyAxiom v)
    (indexedPropertyAxiom_injective v) C c
  exact ⟨indices.subset _ h⟩

theorem rdf_selected_typing (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (n : Nat) (hn : E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.container n)))) :
    RDFClosure T v G E (indexedPropertyAxiom v n) :=
  .premise (Or.inr (Or.inr (Or.inl ⟨n, hn, Or.inl ⟨.container n, True.intro, rfl⟩, Or.inl rfl⟩)))

theorem rdfs_selected_typing (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (n : Nat) (hn : E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.rdf (.container n))))) :
    RDFSClosure T v G E (indexedPropertyAxiom v.toRDF n) :=
  .premise (Or.inr (Or.inr (Or.inl
    ⟨n, hn, Or.inl (Or.inl ⟨.container n, True.intro, rfl⟩), Or.inl rfl⟩)))

theorem rdf_closure_finite_iff (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    FiniteGraph (RDFClosure T v G E) ↔ FiniteGraph G ∧
      Nonempty (Enumeration (fun n => E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.container n))))) := by
  constructor
  · intro h
    exact ⟨rdf_finite_premise_of_finite_closure T v G E h,
      finite_selected_of_typings _ v E _ h (rdf_selected_typing T v G E)⟩
  · rintro ⟨hG, hi⟩
    exact rdf_closure_finite_selected T v G E hG hi

theorem rdfs_closure_finite_iff (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    FiniteGraph (RDFSClosure T v G E) ↔ FiniteGraph G ∧
      Nonempty (Enumeration (fun n => E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.rdf (.container n)))))) := by
  constructor
  · intro h
    exact ⟨rdfs_finite_premise_of_finite_closure T v G E h,
      finite_selected_of_typings _ v.toRDF E _ h (rdfs_selected_typing T v G E)⟩
  · rintro ⟨hG, hi⟩
    exact rdfs_closure_finite_selected T v G E hG hi

theorem finite_omits_indexed_axiom (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (hG : FiniteGraph G) : ∃ n, ¬ G (indexedPropertyAxiom v n) := by
  apply Classical.byContradiction
  intro h
  have hall : ∀ n, G (indexedPropertyAxiom v n) := by
    intro n
    exact Classical.byContradiction (fun hn => h ⟨n, hn⟩)
  exact Enumeration.no_enumeration_of_nat_injection G (indexedPropertyAxiom v) hall
    (indexedPropertyAxiom_injective v) hG

theorem indexed_axiom_tautology (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (n : Nat) :
    RDFEntails.{u} T D v (Set.empty : GeneralizedGraph Iri Literal B₁)
      (Set.singleton (indexedPropertyAxiom v n) : GeneralizedGraph Iri Literal B₂) := by
  rintro U I ⟨ρ, hρ⟩ _
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  rintro _ rfl
  exact I.rdf_axiom_true hρ _ _ (Or.inl ⟨.container n, True.intro, rfl⟩)

def emptyEnumeration : Enumeration (Set.empty : GeneralizedGraph Iri Literal B) :=
  { triples := [], nodup := by simp, membership := by intro t; simp [Set.empty] }

theorem empty_finite : FiniteGraph (Set.empty : GeneralizedGraph Iri Literal B) :=
  ⟨emptyEnumeration⟩

theorem rdf_empty_closure_indexed_absent (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (n : Nat) (hn : n ≠ 0) :
    ¬ RDFClosure T v (Set.empty : GeneralizedGraph Iri Literal B)
      (Set.empty : GeneralizedGraph Iri Literal B) (indexedPropertyAxiom v n) := by
  intro h
  have hi : ∀ k, GeneralizedGraph.vocabulary T.literalSyntax.datatype
      (Set.empty : GeneralizedGraph Iri Literal B) (.inl (v.iri (.container k))) → k ∈ ([] : List Nat) := by
    rintro k ⟨t, ht, _⟩
    cases ht
  have hp := (rdf_closure_onTerms T v Set.empty Set.empty emptyEnumeration [] hi _ h).1
  have he : n = 0 := by
    simpa [rdfTerms, termPool, rdfNames, rdfFixedSymbols, emptyEnumeration,
      indexedPropertyAxiom, Set.ofList, rdf_iri_eq] using hp
  exact hn he

theorem rdfs_empty_closure_indexed_absent (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (n : Nat) (hn : n ≠ 0) :
    ¬ RDFSClosure T v (Set.empty : GeneralizedGraph Iri Literal B)
      (Set.empty : GeneralizedGraph Iri Literal B) (indexedPropertyAxiom v.toRDF n) := by
  intro h
  have hi : ∀ k, GeneralizedGraph.vocabulary T.literalSyntax.datatype
      (Set.empty : GeneralizedGraph Iri Literal B) (.inl (v.iri (.rdf (.container k)))) → k ∈ ([] : List Nat) := by
    rintro k ⟨t, ht, _⟩
    cases ht
  have hp := (rdfs_closure_onTerms T v Set.empty Set.empty emptyEnumeration [] hi _ h).1
  have he : n = 0 := by
    simpa [rdfsTerms, termPool, rdfsNames, rdfsFixedSymbols, rdfFixedSymbols,
      emptyEnumeration, indexedPropertyAxiom, Set.ofList, RDFSVocabulary.toRDF, rdfs_iri_eq] using hp
  exact hn he

theorem rdf_empty_closure_omits_tautology (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri) :
    let G := (Set.empty : GeneralizedGraph Iri Literal B)
    ∃ n, ¬ RDFClosure T v G G (indexedPropertyAxiom v n) ∧
      RDFEntails.{u} T v.baseDatatypes v G (Set.singleton (indexedPropertyAxiom v n) : GeneralizedGraph Iri Literal B) := by
  obtain ⟨n, hn⟩ := finite_omits_indexed_axiom v _
    (rdf_closure_finite T v (Set.empty : GeneralizedGraph Iri Literal B) Set.empty empty_finite empty_finite)
  exact ⟨n, hn, indexed_axiom_tautology T _ v n⟩

theorem rdfs_empty_closure_omits_tautology (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri) :
    let G := (Set.empty : GeneralizedGraph Iri Literal B)
    ∃ n, ¬ RDFSClosure T v G G (indexedPropertyAxiom v.toRDF n) ∧
      RDFSEntails.{u} T v.toRDF.baseDatatypes v G
        (Set.singleton (indexedPropertyAxiom v.toRDF n) : GeneralizedGraph Iri Literal B) := by
  obtain ⟨n, hn⟩ := finite_omits_indexed_axiom v.toRDF _
    (rdfs_closure_finite T v (Set.empty : GeneralizedGraph Iri Literal B) Set.empty empty_finite empty_finite)
  exact ⟨n, hn, rdf_implies_rdfs_entailment T _ v (indexed_axiom_tautology T _ v.toRDF n)⟩

end RDF11.ClosureBound
