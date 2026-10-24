/-
Executable Appendix A closures for finite supplied inputs. Correctness is
equality with the unchanged declarative procedure, not entailment completeness.
The caller supplies executable term equality, datatype projection and an
exact indexed-name decoder. No concrete IRI/XSD parser is claimed here.
-/
import RDF11.ClosureAxiomEvaluation
import RDF11.ClosureRuleEvaluation
import RDF11.FiniteSaturation
import RDF11.FiniteClosure

namespace RDF11.ClosureEvaluation

variable {Iri Literal B₁ B₂ Value : Type}
  [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B₁]

def rdfTermList (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (Term Iri Literal B₁) :=
  ClosureBound.termPool datatype (ClosureBound.rdfNames v (d.indices datatype E)) (Enumeration.unique G)

def rdfsTermList (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (Term Iri Literal B₁) :=
  ClosureBound.termPool datatype (ClosureBound.rdfsNames v (d.indices datatype E)) (Enumeration.unique G)

def rdfCarrier (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (GeneralizedTriple Iri Literal B₁) :=
  ClosureBound.cube (Enumeration.unique (rdfTermList datatype v d G E))

def rdfsCarrier (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (GeneralizedTriple Iri Literal B₁) :=
  ClosureBound.cube (Enumeration.unique (rdfsTermList datatype v d G E))

theorem rdfCarrier_iff (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (t : GeneralizedTriple Iri Literal B₁) :
    t ∈ rdfCarrier datatype v d G E ↔ ClosureBound.OnTerms (Set.ofList (rdfTermList datatype v d G E)) t := by
  simp only [rdfCarrier, ClosureBound.mem_cube, ClosureBound.OnTerms, Set.ofList, Enumeration.mem_unique]

theorem rdfsCarrier_iff (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (t : GeneralizedTriple Iri Literal B₁) :
    t ∈ rdfsCarrier datatype v d G E ↔ ClosureBound.OnTerms (Set.ofList (rdfsTermList datatype v d G E)) t := by
  simp only [rdfsCarrier, ClosureBound.mem_cube, ClosureBound.OnTerms, Set.ofList, Enumeration.mem_unique]

theorem rdf_seed_bounded (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (rdfAxiomLists T.literalSyntax.datatype v).seed d G E ⊆ rdfCarrier T.literalSyntax.datatype v d G E := by
  intro t ht
  apply (rdfCarrier_iff _ v d G E t).mpr
  exact ClosureBound.rdf_seed_onTerms T v (Set.ofList G) (Set.ofList E)
    (Enumeration.fromList G) (d.indices T.literalSyntax.datatype E)
    (fun n hn => (d.indices_iff _ E n).mpr hn) t
    (((rdfAxiomLists _ v).seed_iff d G E t).mp ht)

theorem rdfs_seed_bounded (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (rdfsAxiomLists T.literalSyntax.datatype v).seed d G E ⊆ rdfsCarrier T.literalSyntax.datatype v d G E := by
  intro t ht
  apply (rdfsCarrier_iff _ v d G E t).mpr
  exact ClosureBound.rdfs_seed_onTerms T v (Set.ofList G) (Set.ofList E)
    (Enumeration.fromList G) (d.indices T.literalSyntax.datatype E)
    (fun n hn => (d.indices_iff _ E n).mpr hn) t
    (((rdfsAxiomLists _ v).seed_iff d G E t).mp ht)

theorem rdf_next_bounded (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (xs : List (GeneralizedTriple Iri Literal B₁))
    (hx : xs ⊆ rdfCarrier T.literalSyntax.datatype v d G E) :
    rdfNext T.literalSyntax.datatype v xs ⊆ rdfCarrier T.literalSyntax.datatype v d G E := by
  intro t ht
  apply (rdfCarrier_iff _ v d G E t).mpr
  apply ClosureBound.rdf_step_onTerms T v.baseDatatypes v _
    (ClosureBound.rdf_fixed_in_pool T v _ _ .rdfType (by simp [ClosureBound.rdfFixedSymbols]))
    (ClosureBound.rdf_fixed_in_pool T v _ _ .rdfProperty (by simp [ClosureBound.rdfFixedSymbols]))
    (fun l hl => ClosureBound.pool_literal _ _ _ hl) (Set.ofList xs)
    (fun q hq => (rdfCarrier_iff _ v d G E q).mp (hx hq))
    ((rdfNext_iff T v xs t).mp ht)

theorem rdfs_next_bounded (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (xs : List (GeneralizedTriple Iri Literal B₁))
    (hx : xs ⊆ rdfsCarrier T.literalSyntax.datatype v d G E) :
    combinedNext T.literalSyntax.datatype v xs ⊆ rdfsCarrier T.literalSyntax.datatype v d G E := by
  intro t ht
  apply (rdfsCarrier_iff _ v d G E t).mpr
  have hH : Set.subset (Set.ofList xs) (ClosureBound.OnTerms (Set.ofList (rdfsTermList T.literalSyntax.datatype v d G E))) :=
    fun q hq => (rdfsCarrier_iff _ v d G E q).mp (hx hq)
  have fixed (s : RDFSSymbol) (hs : s ∈ ClosureBound.rdfsFixedSymbols) :
      .iri (v.iri s) ∈ rdfsTermList T.literalSyntax.datatype v d G E :=
    ClosureBound.rdfs_fixed_in_pool T v _ _ s hs
  rcases (combinedNext_iff T v xs t).mp ht with hrdf | hrdfs
  · exact ClosureBound.rdf_step_onTerms T v.toRDF.baseDatatypes v.toRDF _
      (fixed (.rdf .rdfType) (by simp [ClosureBound.rdfsFixedSymbols, ClosureBound.rdfFixedSymbols]))
      (fixed (.rdf .rdfProperty) (by simp [ClosureBound.rdfsFixedSymbols, ClosureBound.rdfFixedSymbols]))
      (fun l hl => ClosureBound.pool_literal _ _ _ hl) _ hH hrdf
  · apply ClosureBound.rdfs_step_onTerms T v.toRDF.baseDatatypes v _ ?_ ?_ _ hH hrdfs
    · intro a ha
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
      apply fixed s
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [ClosureBound.rdfsFixedSymbols, ClosureBound.rdfFixedSymbols]
    · intro a ha
      rcases ha with rfl | rfl <;> apply fixed <;>
        simp [ClosureBound.rdfsFixedSymbols, ClosureBound.rdfFixedSymbols]

def rdf (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (GeneralizedTriple Iri Literal B₁) :=
  FiniteSaturation.run (rdfNext datatype v) (rdfCarrier datatype v d G E).length
    ((rdfAxiomLists datatype v).seed d G E)

def rdfs (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    List (GeneralizedTriple Iri Literal B₁) :=
  FiniteSaturation.run (combinedNext datatype v) (rdfsCarrier datatype v d G E).length
    ((rdfsAxiomLists datatype v).seed d G E)

theorem rdf_nodup (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (rdf datatype v d G E).Nodup :=
  FiniteSaturation.run_nodup _ _ _ ((rdfAxiomLists datatype v).seed_nodup d G E)

theorem rdfs_nodup (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (rdfs datatype v d G E).Nodup :=
  FiniteSaturation.run_nodup _ _ _ ((rdfsAxiomLists datatype v).seed_nodup d G E)

theorem rdf_exact (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    Set.ofList (rdf T.literalSyntax.datatype v d G E) = RDFClosure T v (Set.ofList G) (Set.ofList E) := by
  have h := FiniteSaturation.run_exact (RDFStep T v.baseDatatypes v) (rdfNext T.literalSyntax.datatype v)
    (rdfNext_iff T v) (rdfStep_mono T v.baseDatatypes v) _ (rdf_next_bounded T v d G E)
    (rdfCarrier T.literalSyntax.datatype v d G E).length _
    ((rdfAxiomLists _ v).seed_nodup d G E) (rdf_seed_bounded T v d G E) (by omega)
  have seed_eq := Set.ext ((rdfAxiomLists T.literalSyntax.datatype v).seed_iff d G E)
  change Set.ofList ((rdfAxiomLists T.literalSyntax.datatype v).seed d G E) = _ at seed_eq
  rw [seed_eq] at h
  exact h

theorem rdfs_exact (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    Set.ofList (rdfs T.literalSyntax.datatype v d G E) = RDFSClosure T v (Set.ofList G) (Set.ofList E) := by
  have h := FiniteSaturation.run_exact (RDFSGeneralizedStep T v.toRDF.baseDatatypes v)
    (combinedNext T.literalSyntax.datatype v) (combinedNext_iff T v)
    (combinedStep_mono T v.toRDF.baseDatatypes v) _ (rdfs_next_bounded T v d G E)
    (rdfsCarrier T.literalSyntax.datatype v d G E).length _
    ((rdfsAxiomLists _ v).seed_nodup d G E) (rdfs_seed_bounded T v d G E) (by omega)
  have seed_eq := Set.ext ((rdfsAxiomLists T.literalSyntax.datatype v).seed_iff d G E)
  change Set.ofList ((rdfsAxiomLists T.literalSyntax.datatype v).seed d G E) = _ at seed_eq
  rw [seed_eq] at h
  exact h

def rdfEnumeration (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    Enumeration (RDFClosure T v (Set.ofList G) (Set.ofList E)) where
  triples := rdf T.literalSyntax.datatype v d G E
  nodup := rdf_nodup _ v d G E
  membership := by intro t; change Set.ofList _ t ↔ _; rw [rdf_exact T v d G E]

def rdfsEnumeration (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    Enumeration (RDFSClosure T v (Set.ofList G) (Set.ofList E)) where
  triples := rdfs T.literalSyntax.datatype v d G E
  nodup := rdfs_nodup _ v d G E
  membership := by intro t; change Set.ofList _ t ↔ _; rw [rdfs_exact T v d G E]

def rdfDecision (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (t : GeneralizedTriple Iri Literal B₁) : Decidable (RDFClosure T v (Set.ofList G) (Set.ofList E) t) :=
  FiniteSaturation.decision _ (rdfEnumeration T v d G E) t

def rdfsDecision (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (t : GeneralizedTriple Iri Literal B₁) : Decidable (RDFSClosure T v (Set.ofList G) (Set.ofList E) t) :=
  FiniteSaturation.decision _ (rdfsEnumeration T v d G E) t

theorem rdf_fuel_bound (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (rdfCarrier datatype v d G E).length = (Enumeration.unique (rdfTermList datatype v d G E)).length ^ 3 :=
  ClosureBound.cube_length _

theorem rdfs_fuel_bound (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) :
    (rdfsCarrier datatype v d G E).length = (Enumeration.unique (rdfsTermList datatype v d G E)).length ^ 3 :=
  ClosureBound.cube_length _

theorem rdf_count_respects_graphs (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G H : List (GeneralizedTriple Iri Literal B₁)) (E F : List (GeneralizedTriple Iri Literal B₂))
    (hG : Set.ofList G = Set.ofList H) (hE : Set.ofList E = Set.ofList F) :
    (rdf T.literalSyntax.datatype v d G E).length = (rdf T.literalSyntax.datatype v d H F).length := by
  have same (t) : t ∈ rdf T.literalSyntax.datatype v d G E ↔ t ∈ rdf T.literalSyntax.datatype v d H F := by
    change Set.ofList _ t ↔ Set.ofList _ t
    rw [rdf_exact T v d G E, rdf_exact T v d H F, hG, hE]
  have hg := rdf_nodup T.literalSyntax.datatype v d G E
  have hh := rdf_nodup T.literalSyntax.datatype v d H F
  apply Nat.le_antisymm
  · apply hg.length_le_of_subset
    exact fun t ht => (same t).mp ht
  · apply hh.length_le_of_subset
    exact fun t ht => (same t).mpr ht

theorem rdfs_count_respects_graphs (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G H : List (GeneralizedTriple Iri Literal B₁)) (E F : List (GeneralizedTriple Iri Literal B₂))
    (hG : Set.ofList G = Set.ofList H) (hE : Set.ofList E = Set.ofList F) :
    (rdfs T.literalSyntax.datatype v d G E).length = (rdfs T.literalSyntax.datatype v d H F).length := by
  have same (t) : t ∈ rdfs T.literalSyntax.datatype v d G E ↔ t ∈ rdfs T.literalSyntax.datatype v d H F := by
    change Set.ofList _ t ↔ Set.ofList _ t
    rw [rdfs_exact T v d G E, rdfs_exact T v d H F, hG, hE]
  have hg := rdfs_nodup T.literalSyntax.datatype v d G E
  have hh := rdfs_nodup T.literalSyntax.datatype v d H F
  apply Nat.le_antisymm
  · apply hg.length_le_of_subset
    exact fun t ht => (same t).mp ht
  · apply hh.length_le_of_subset
    exact fun t ht => (same t).mpr ht

theorem rdf_result_satisfaction (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (I : SimpleInterpretation Iri Literal U) (hI : I.RDFModel T v.baseDatatypes v) :
    I.Satisfies (Set.ofList (rdf T.literalSyntax.datatype v d G E)) ↔ I.Satisfies (Set.ofList G) := by
  rw [rdf_exact T v d G E]
  exact I.rdf_closure_satisfaction hI _ _

theorem rdfs_result_satisfaction (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (I : SimpleInterpretation Iri Literal U) (hI : I.RDFSModel T v.toRDF.baseDatatypes v) :
    I.Satisfies (Set.ofList (rdfs T.literalSyntax.datatype v d G E)) ↔ I.Satisfies (Set.ofList G) := by
  rw [rdfs_exact T v d G E]
  exact I.rdfs_closure_satisfaction hI _ _

end RDF11.ClosureEvaluation
