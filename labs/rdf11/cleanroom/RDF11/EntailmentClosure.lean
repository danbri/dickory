/-
RDF 1.1 Semantics Appendix A: generalized closure towards a conclusion.
The seed selects container axioms from E, with the stated rdf:_1 fallback.
Recognition is the base set {rdf:langString, xsd:string}. These definitions
and soundness proofs do not establish finite computation or completeness.
-/
import RDF11.RDFSRules

namespace RDF11

def NonContainerAxioms (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms : GeneralizedGraph Iri Literal B) : GeneralizedGraph Iri Literal B :=
  fun t => axioms t ∧ ¬ ∃ n, t.names datatype (.inl (container n))

def ContainerAxioms (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms : GeneralizedGraph Iri Literal B) (n : Nat) : GeneralizedGraph Iri Literal B :=
  fun t => axioms t ∧ t.names datatype (.inl (container n))

def ConclusionAxioms (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    GeneralizedGraph Iri Literal B₁ :=
  fun t => ∃ n, E.vocabulary datatype (.inl (container n)) ∧ ContainerAxioms datatype container axioms n t

/-- The fallback reads "no triples were added" as set inclusion in the seed after step 1. -/
def AxiomSeed (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    GeneralizedGraph Iri Literal B₁ :=
  fun t => G t ∨ NonContainerAxioms datatype container axioms t ∨
    ConclusionAxioms datatype container axioms E t ∨
    (Set.subset (ConclusionAxioms datatype container axioms E)
      (Set.union G (NonContainerAxioms datatype container axioms)) ∧
      ContainerAxioms datatype container axioms 0 t)

theorem axiomSeed_contains (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    Set.subset G (AxiomSeed datatype container axioms G E) := fun _ ht => Or.inl ht

theorem axiomSeed_subset (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    Set.subset (AxiomSeed datatype container axioms G E) (Set.union G axioms) := by
  intro t ht
  rcases ht with hg | ha | ⟨_, _, ha⟩ | ⟨_, ha⟩
  · exact Or.inl hg
  · exact Or.inr ha.1
  · exact Or.inr ha.1
  · exact Or.inr ha.1

inductive RDFStep (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    GeneralizedTriple Iri Literal B → Prop where
  | rdfD2 (t) : G t → RDFStep T D v G
      ⟨t.predicate, .iri (v.iri .rdfType), .iri (v.iri .rdfProperty)⟩
  | GrdfD1 (s p l) : G ⟨s, p, .literal l⟩ → D (T.literalSyntax.datatype l) →
      RDFStep T D v G ⟨.literal l, .iri (v.iri .rdfType), .iri (T.literalSyntax.datatype l)⟩

def RDFSGeneralizedStep (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : GeneralizedGraph Iri Literal B)
    (t : GeneralizedTriple Iri Literal B) : Prop :=
  RDFStep T D v.toRDF G t ∨ RDFSStep T D v G t

inductive RuleDerives
    (step : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop)
    (seed : GeneralizedGraph Iri Literal B) : GeneralizedTriple Iri Literal B → Prop where
  | premise : seed t → RuleDerives step seed t
  | rule (H : GeneralizedGraph Iri Literal B) :
      (∀ t, H t → RuleDerives step seed t) → step H t → RuleDerives step seed t

theorem ruleDerives_least
    (step : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop)
    (seed closed : GeneralizedGraph Iri Literal B) (hs : Set.subset seed closed)
    (hc : ∀ H t, Set.subset H closed → step H t → closed t) :
    Set.subset (RuleDerives step seed) closed := by
  intro t ht
  induction ht with
  | premise ht => exact hs _ ht
  | rule H _ hstep ih => exact hc H _ ih hstep

def RDFClosure (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    GeneralizedGraph Iri Literal B₁ :=
  RuleDerives (RDFStep T v.baseDatatypes v)
    (AxiomSeed T.literalSyntax.datatype (fun n => v.iri (.container n)) v.axioms G E)

def RDFSClosure (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    GeneralizedGraph Iri Literal B₁ :=
  RuleDerives (RDFSGeneralizedStep T v.toRDF.baseDatatypes v)
    (AxiomSeed T.literalSyntax.datatype (fun n => v.iri (.rdf (.container n)))
      (Set.union v.toRDF.axioms v.axioms) G E)

namespace SimpleInterpretation

theorem rdf_step_sound (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (A : I.Assignment B) (hG : I.GraphTrue A G)
    (step : RDFStep T D v G t) : I.TripleTrue A t := by
  cases step with
  | rdfD2 t ht => exact I.rdfD2_triple h.property A t (hG t ht)
  | GrdfD1 s p l ht hd => exact I.GrdfD1_triple h A _ (hG _ ht) (Or.inr (Or.inr rfl)) hd

theorem rdfs_generalized_step_sound (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (A : I.Assignment B) (hG : I.GraphTrue A G)
    (step : RDFSGeneralizedStep T D v G t) : I.TripleTrue A t := by
  rcases step with rdf | rdfs
  · exact I.rdf_step_sound h.rdf A hG rdf
  · exact I.rdfs_step_sound h A hG rdfs

theorem axiomSeed_true (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B₁) (datatype : Literal → Iri) (container : Nat → Iri)
    (axioms G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (ha : I.GraphTrue A axioms) (hG : I.GraphTrue A G) :
    I.GraphTrue A (AxiomSeed datatype container axioms G E) := by
  intro t ht
  rcases axiomSeed_subset datatype container axioms G E t ht with hg | hx
  · exact hG t hg
  · exact ha t hx

theorem ruleDerives_true (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (step : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop)
    (seed : GeneralizedGraph Iri Literal B) (hs : I.GraphTrue A seed)
    (hstep : ∀ H t, I.GraphTrue A H → step H t → I.TripleTrue A t) :
    I.GraphTrue A (RuleDerives step seed) :=
  ruleDerives_least step seed (I.TripleTrue A) hs hstep

theorem rdf_closure_satisfaction (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFModel T v.baseDatatypes v)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    I.Satisfies (RDFClosure T v G E) ↔ I.Satisfies G := by
  constructor
  · exact I.satisfies_subgraph (fun _ ht => RuleDerives.premise (Or.inl ht))
  · intro hG
    obtain ⟨ρ, hρ⟩ := h
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, I.ruleDerives_true A _ _ ?_ ?_⟩
    · exact I.axiomSeed_true A _ _ _ G E (fun t ht => I.rdf_axiom_true hρ A t ht) hA
    · exact fun _ _ hH hs => I.rdf_step_sound hρ A hH hs

theorem rdfs_closure_satisfaction (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSModel T v.toRDF.baseDatatypes v)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) :
    I.Satisfies (RDFSClosure T v G E) ↔ I.Satisfies G := by
  constructor
  · exact I.satisfies_subgraph (fun _ ht => RuleDerives.premise (Or.inl ht))
  · intro hG
    obtain ⟨ρ, hρ⟩ := h
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue G).mp hG
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, I.ruleDerives_true A _ _ ?_ ?_⟩
    · apply I.axiomSeed_true A _ _ _ G E ?_ hA
      intro t ht
      rcases ht with hrdf | hrdfs
      · exact I.rdf_axiom_true hρ.rdf A t hrdf
      · exact I.rdfs_axiom_true hρ A t hrdfs
    · exact fun _ _ hH hs => I.rdfs_generalized_step_sound hρ A hH hs

end SimpleInterpretation

theorem rdf_closure_simple_check_sound (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (h : SimplyEntails.{u} (RDFClosure T v G E) E) : RDFEntails.{u} T v.baseDatatypes v G E :=
  fun _ I hI hG => h _ I ((I.rdf_closure_satisfaction hI G E).mpr hG)

theorem rdfs_closure_simple_check_sound (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (h : SimplyEntails.{u} (RDFSClosure T v G E) E) : RDFSEntails.{u} T v.toRDF.baseDatatypes v G E :=
  fun _ I hI hG => h _ I ((I.rdfs_closure_satisfaction hI G E).mpr hG)

theorem rdf_closure_instance_check_sound (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (G E : GeneralizedGraph Iri Literal B) (μ : Substitution Iri Literal B)
    (h : Set.subset (E.substitute μ) (RDFClosure T v G E)) : RDFEntails.{u} T v.baseDatatypes v G E := by
  intro U I hI hG
  have hc := (I.rdf_closure_satisfaction hI G E).mpr hG
  obtain ⟨ρ, hρ⟩ := hI
  exact rdf_condition_substitution_entails _ _ E μ U I hρ.property (I.satisfies_subgraph h hc)

theorem rdfs_closure_instance_check_sound (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (G E : GeneralizedGraph Iri Literal B) (μ : Substitution Iri Literal B)
    (h : Set.subset (E.substitute μ) (RDFSClosure T v G E)) : RDFSEntails.{u} T v.toRDF.baseDatatypes v G E := by
  intro U I hI hG
  have hc := (I.rdfs_closure_satisfaction hI G E).mpr hG
  obtain ⟨ρ, hρ⟩ := hI
  exact rdf_condition_substitution_entails _ _ E μ U I hρ.rdf.property (I.satisfies_subgraph h hc)

end RDF11
