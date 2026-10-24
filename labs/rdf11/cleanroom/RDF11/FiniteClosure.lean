/-
Appendix A finiteness, with the finite-input qualification explicit.
The original E-only axiom selection and base datatype recognition are fixed.
K counts distinct supporting terms, including embedded datatype IRIs and
axiom/rule-only names. This proves a size bound, not polynomial runtime.
-/
import RDF11.ClosureVocabulary

namespace RDF11.ClosureBound

def rdfNames (v : RDFVocabulary Iri) (indices : List Nat) : List Iri :=
  rdfFixedSymbols.map v.iri ++ (0 :: indices).map (fun n => v.iri (.container n))

def rdfsNames (v : RDFSVocabulary Iri) (indices : List Nat) : List Iri :=
  rdfsFixedSymbols.map v.iri ++ (0 :: indices).map (fun n => v.iri (.rdf (.container n)))

def rdfTerms (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (indices : List Nat) :
    List (Term Iri Literal B) := termPool T.literalSyntax.datatype (rdfNames v indices) triples

def rdfsTerms (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (indices : List Nat) :
    List (Term Iri Literal B) := termPool T.literalSyntax.datatype (rdfsNames v indices) triples

theorem rdf_fixed_in_pool (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (indices : List Nat)
    (s : RDFSymbol) (hs : s ∈ rdfFixedSymbols) : .iri (v.iri s) ∈ rdfTerms T v triples indices :=
  pool_fixed _ _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))

theorem rdfs_fixed_in_pool (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (indices : List Nat)
    (s : RDFSSymbol) (hs : s ∈ rdfsFixedSymbols) : .iri (v.iri s) ∈ rdfsTerms T v triples indices :=
  pool_fixed _ _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))

theorem rdf_container_in_pool (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (indices : List Nat)
    (n : Nat) (hn : n ∈ 0 :: indices) : .iri (v.iri (.container n)) ∈ rdfTerms T v triples indices :=
  pool_fixed _ _ _ (List.mem_append_right _ (List.mem_map.mpr ⟨n, hn, rfl⟩))

theorem rdfs_container_in_pool (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (triples : List (GeneralizedTriple Iri Literal B)) (indices : List Nat)
    (n : Nat) (hn : n ∈ 0 :: indices) : .iri (v.iri (.rdf (.container n))) ∈ rdfsTerms T v triples indices :=
  pool_fixed _ _ _ (List.mem_append_right _ (List.mem_map.mpr ⟨n, hn, rfl⟩))

theorem rdf_seed_onTerms (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (g : Enumeration G) (indices : List Nat)
    (hi : ∀ n, E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.container n))) → n ∈ indices) :
    Set.subset (AxiomSeed T.literalSyntax.datatype (fun n => v.iri (.container n)) v.axioms G E)
      (OnTerms (Set.ofList (rdfTerms T v g.triples indices))) := by
  apply seed_onTerms
  · exact fun t ht => pool_triple _ _ _ ((g.membership t).mpr ht)
  · exact rdf_axioms_onTerms _ v _ (rdf_fixed_in_pool T v g.triples indices)
  · exact rdf_axiom_container_unique _ v
  · exact fun n hn => rdf_container_in_pool T v g.triples indices n (by simp [hi n hn])
  · exact rdf_container_in_pool T v g.triples indices 0 (by simp)

theorem rdfs_seed_onTerms (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (g : Enumeration G) (indices : List Nat)
    (hi : ∀ n, E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.rdf (.container n)))) → n ∈ indices) :
    Set.subset (AxiomSeed T.literalSyntax.datatype (fun n => v.iri (.rdf (.container n)))
      (Set.union v.toRDF.axioms v.axioms) G E)
      (OnTerms (Set.ofList (rdfsTerms T v g.triples indices))) := by
  apply seed_onTerms
  · exact fun t ht => pool_triple _ _ _ ((g.membership t).mpr ht)
  · intro t ht hc
    rcases ht with h | h
    · apply rdf_axioms_onTerms _ v.toRDF _ _ t h hc
      intro s hs
      exact rdfs_fixed_in_pool T v g.triples indices (.rdf s)
        (List.mem_append_left _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
    · exact rdfs_axioms_onTerms _ v _ (rdfs_fixed_in_pool T v g.triples indices) t h hc
  · intro t ht m n hm hn
    exact ht.elim (fun h => rdf_axiom_container_unique _ v.toRDF t h m n hm hn)
      (fun h => rdfs_axiom_container_unique _ v t h m n hm hn)
  · exact fun n hn => rdfs_container_in_pool T v g.triples indices n (by simp [hi n hn])
  · exact rdfs_container_in_pool T v g.triples indices 0 (by simp)

theorem rdf_closure_onTerms (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (g : Enumeration G) (indices : List Nat)
    (hi : ∀ n, E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.container n))) → n ∈ indices) :
    Set.subset (RDFClosure T v G E) (OnTerms (Set.ofList (rdfTerms T v g.triples indices))) := by
  apply ruleDerives_least _ _ _ (rdf_seed_onTerms T v G E g indices hi)
  intro H t hH h
  exact rdf_step_onTerms T _ v _
    (rdf_fixed_in_pool T v g.triples indices .rdfType (by simp [rdfFixedSymbols]))
    (rdf_fixed_in_pool T v g.triples indices .rdfProperty (by simp [rdfFixedSymbols]))
    (fun l hl => pool_literal _ _ _ hl) H hH h

theorem rdfs_closure_onTerms (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (g : Enumeration G) (indices : List Nat)
    (hi : ∀ n, E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.rdf (.container n)))) → n ∈ indices) :
    Set.subset (RDFSClosure T v G E) (OnTerms (Set.ofList (rdfsTerms T v g.triples indices))) := by
  apply ruleDerives_least _ _ _ (rdfs_seed_onTerms T v G E g indices hi)
  intro H t hH h
  rcases h with h | h
  · exact rdf_step_onTerms T _ v.toRDF _
      (rdfs_fixed_in_pool T v g.triples indices (.rdf .rdfType) (by simp [rdfsFixedSymbols, rdfFixedSymbols]))
      (rdfs_fixed_in_pool T v g.triples indices (.rdf .rdfProperty) (by simp [rdfsFixedSymbols, rdfFixedSymbols]))
      (fun l hl => pool_literal _ _ _ hl) H hH h
  · apply rdfs_step_onTerms T _ v _ _ _ H hH h
    · intro a ha
      simp [rdfsRuleNames] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact rdfs_fixed_in_pool T v g.triples indices _ (by simp [rdfsFixedSymbols, rdfFixedSymbols])
    · intro a ha
      rcases ha with rfl | rfl <;>
        exact rdfs_fixed_in_pool T v g.triples indices _ (by simp [rdfsFixedSymbols, rdfFixedSymbols])

theorem rdf_closure_bound (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (g : Enumeration G) (indices : List Nat)
    (hi : ∀ n, E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.container n))) → n ∈ indices) :
    ∃ (terms : Enumeration (Set.ofList (rdfTerms T v g.triples indices)))
      (closure : Enumeration (RDFClosure T v G E)),
      closure.triples.length ≤ terms.triples.length ^ 3 := by
  classical
  let terms := Enumeration.fromList (rdfTerms T v g.triples indices)
  obtain ⟨c, hc⟩ := graph_bound _ terms _ (rdf_closure_onTerms T v G E g indices hi)
  exact ⟨terms, c, hc⟩

theorem rdfs_closure_bound (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (g : Enumeration G) (indices : List Nat)
    (hi : ∀ n, E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.rdf (.container n)))) → n ∈ indices) :
    ∃ (terms : Enumeration (Set.ofList (rdfsTerms T v g.triples indices)))
      (closure : Enumeration (RDFSClosure T v G E)),
      closure.triples.length ≤ terms.triples.length ^ 3 := by
  classical
  let terms := Enumeration.fromList (rdfsTerms T v g.triples indices)
  obtain ⟨c, hc⟩ := graph_bound _ terms _ (rdfs_closure_onTerms T v G E g indices hi)
  exact ⟨terms, c, hc⟩

theorem rdf_closure_finite_selected (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : FiniteGraph G)
    (hi : Nonempty (Enumeration (fun n => E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.container n)))))) :
    FiniteGraph (RDFClosure T v G E) := by
  obtain ⟨g⟩ := hG
  obtain ⟨indices⟩ := hi
  obtain ⟨_, c, _⟩ := rdf_closure_bound T v G E g indices.triples (fun n hn => (indices.membership n).mpr hn)
  exact ⟨c⟩

theorem rdfs_closure_finite_selected (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : FiniteGraph G)
    (hi : Nonempty (Enumeration (fun n => E.vocabulary T.literalSyntax.datatype (.inl (v.iri (.rdf (.container n))))))) :
    FiniteGraph (RDFSClosure T v G E) := by
  obtain ⟨g⟩ := hG
  obtain ⟨indices⟩ := hi
  obtain ⟨_, c, _⟩ := rdfs_closure_bound T v G E g indices.triples (fun n hn => (indices.membership n).mpr hn)
  exact ⟨c⟩

theorem rdf_closure_finite (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : FiniteGraph G) (hE : FiniteGraph E) : FiniteGraph (RDFClosure T v G E) :=
  rdf_closure_finite_selected T v G E hG (selected_indices_finite _ _
    (fun _ _ h => RDFSymbol.container.inj (v.distinct _ _ h)) E hE)

theorem rdfs_closure_finite (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : FiniteGraph G) (hE : FiniteGraph E) : FiniteGraph (RDFSClosure T v G E) :=
  rdfs_closure_finite_selected T v G E hG (selected_indices_finite _ _
    (fun _ _ h => RDFSymbol.container.inj (RDFSSymbol.rdf.inj (v.distinct _ _ h))) E hE)

end RDF11.ClosureBound
