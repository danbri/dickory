/-
Effective indexed-name selection and the exact Appendix A seed/fallback.
An injective encoding alone is insufficient: decoding has its own contract.
-/
import RDF11.ClosureVocabulary

namespace RDF11.ClosureEvaluation

variable {Iri Literal B B₁ B₂ : Type} {container : Nat → Iri}
  {datatype : Literal → Iri} {axioms : GeneralizedGraph Iri Literal B₁}

structure ContainerDecoder (container : Nat → Iri) where
  decode : Iri → Option Nat
  correct : ∀ a n, decode a = some n ↔ a = container n

def ContainerDecoder.term (d : ContainerDecoder container) : Term Iri Literal B → Option Nat
  | .iri a => d.decode a
  | _ => none

theorem ContainerDecoder.expanded_iff (d : ContainerDecoder container) (datatype : Literal → Iri)
    (t : Term Iri Literal B) (n : Nat) :
    n ∈ (ClosureBound.expanded datatype t).filterMap d.term ↔ t.names datatype (.inl (container n)) := by
  cases t <;> simp [ClosureBound.expanded, ContainerDecoder.term, Term.names, Set.empty,
    List.mem_filterMap, d.correct]
  all_goals exact eq_comm

def ContainerDecoder.indices (d : ContainerDecoder container) (datatype : Literal → Iri)
    (E : List (GeneralizedTriple Iri Literal B)) : List Nat :=
  E.flatMap (fun t => (ClosureBound.tripleTerms datatype t).filterMap d.term)

theorem ContainerDecoder.indices_iff (d : ContainerDecoder container) (datatype : Literal → Iri)
    (E : List (GeneralizedTriple Iri Literal B)) (n : Nat) :
    n ∈ d.indices datatype E ↔ GeneralizedGraph.vocabulary datatype (Set.ofList E) (.inl (container n)) := by
  simp only [ContainerDecoder.indices, List.mem_flatMap, ClosureBound.tripleTerms,
    List.filterMap_append, List.mem_append, d.expanded_iff, GeneralizedGraph.vocabulary,
    GeneralizedTriple.names, Set.ofList, or_assoc]

structure AxiomLists (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms : GeneralizedGraph Iri Literal B) where
  fixed : List (GeneralizedTriple Iri Literal B)
  indexed : Nat → List (GeneralizedTriple Iri Literal B)
  fixed_iff : ∀ t, t ∈ fixed ↔ NonContainerAxioms datatype container axioms t
  indexed_iff : ∀ n t, t ∈ indexed n ↔ ContainerAxioms datatype container axioms n t

def AxiomLists.ofPartition (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms : GeneralizedGraph Iri Literal B)
    (fixed : List (GeneralizedTriple Iri Literal B))
    (indexed : Nat → List (GeneralizedTriple Iri Literal B))
    (covers : ∀ t, axioms t ↔ t ∈ fixed ∨ ∃ n, t ∈ indexed n)
    (fixed_names : ∀ t ∈ fixed, ∀ n, ¬ t.names datatype (.inl (container n)))
    (indexed_names : ∀ n t, t ∈ indexed n → ∀ k, t.names datatype (.inl (container k)) ↔ k = n) :
    AxiomLists datatype container axioms where
  fixed := fixed
  indexed := indexed
  fixed_iff := by
    intro t
    constructor
    · intro h
      exact ⟨(covers t).mpr (Or.inl h), fun ⟨n, hn⟩ => fixed_names t h n hn⟩
    · rintro ⟨ha, hn⟩
      rcases (covers t).mp ha with h | ⟨n, h⟩
      · exact h
      · exact False.elim (hn ⟨n, (indexed_names n t h n).mpr rfl⟩)
  indexed_iff := by
    intro n t
    constructor
    · intro h
      exact ⟨(covers t).mpr (Or.inr ⟨n, h⟩), (indexed_names n t h n).mpr rfl⟩
    · rintro ⟨ha, hn⟩
      rcases (covers t).mp ha with h | ⟨k, h⟩
      · exact False.elim (fixed_names t h n hn)
      · have he := (indexed_names k t h n).mp hn
        exact he.symm ▸ h

def AxiomLists.selected (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (E : List (GeneralizedTriple Iri Literal B₂)) : List (GeneralizedTriple Iri Literal B₁) :=
  (d.indices datatype E).flatMap a.indexed

theorem AxiomLists.selected_iff (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (E : List (GeneralizedTriple Iri Literal B₂)) (t : GeneralizedTriple Iri Literal B₁) :
    t ∈ a.selected d E ↔ ConclusionAxioms datatype container axioms (Set.ofList E) t := by
  simp only [selected, List.mem_flatMap, d.indices_iff, a.indexed_iff, ConclusionAxioms]

variable [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B₁]

def AxiomLists.fallback (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) : Bool :=
  (a.selected d E).all (fun t => decide (t ∈ G ++ a.fixed))

theorem AxiomLists.fallback_iff (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    a.fallback d G E = true ↔ Set.subset (ConclusionAxioms datatype container axioms (Set.ofList E))
      (Set.union (Set.ofList G) (NonContainerAxioms datatype container axioms)) := by
  simp only [fallback, List.all_eq_true, decide_eq_true_eq, List.mem_append, a.fixed_iff]
  constructor
  · intro h t ht
    exact h t ((a.selected_iff d E t).mpr ht)
  · intro h t ht
    exact h t ((a.selected_iff d E t).mp ht)

def AxiomLists.seed (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (GeneralizedTriple Iri Literal B₁) :=
  Enumeration.unique (G ++ a.fixed ++ a.selected d E ++
    if a.fallback d G E then a.indexed 0 else [])

theorem AxiomLists.seed_iff (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (t : GeneralizedTriple Iri Literal B₁) :
    t ∈ a.seed d G E ↔ AxiomSeed datatype container axioms (Set.ofList G) (Set.ofList E) t := by
  by_cases h : a.fallback d G E = true
  · have hf := (a.fallback_iff d G E).mp h
    simp only [seed, Enumeration.mem_unique, List.mem_append, if_pos h, a.fixed_iff,
      a.selected_iff, a.indexed_iff, AxiomSeed, hf, true_and, Set.ofList, or_assoc]
  · have hf : ¬ Set.subset (ConclusionAxioms datatype container axioms (Set.ofList E))
        (Set.union (Set.ofList G) (NonContainerAxioms datatype container axioms)) :=
      fun h' => h ((a.fallback_iff d G E).mpr h')
    simp only [seed, Enumeration.mem_unique, List.mem_append, if_neg h, List.not_mem_nil,
      or_false, a.fixed_iff, a.selected_iff, AxiomSeed, hf, false_and, Set.ofList, or_assoc]

theorem AxiomLists.seed_nodup (a : AxiomLists datatype container axioms) (d : ContainerDecoder container)
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (a.seed d G E).Nodup := Enumeration.unique_nodup _

end RDF11.ClosureEvaluation
