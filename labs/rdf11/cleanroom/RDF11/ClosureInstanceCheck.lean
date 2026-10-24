/-
The final instance search in the finite printed Appendix A procedure.
Exact instance existence is decidable. Positive checks imply RDF/RDFS
entailment; negative checks do not establish semantic non-entailment.
-/
import RDF11.ExecutableClosure
import RDF11.InstanceDecision

namespace RDF11.ClosureEvaluation

variable {Iri Literal Value B B₁ B₂ : Type}
variable [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B]

def rdfCheck (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G E : List (GeneralizedTriple Iri Literal B)) : Bool :=
  InstanceSearch.check (rdf datatype v d G E) E

def rdfsCheck (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G E : List (GeneralizedTriple Iri Literal B)) : Bool :=
  InstanceSearch.check (rdfs datatype v d G E) E

theorem rdfCheck_iff (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G E : List (GeneralizedTriple Iri Literal B)) :
    rdfCheck T.literalSyntax.datatype v d G E = true ↔
      ∃ μ, Set.subset (GeneralizedGraph.substitute μ (Set.ofList E))
        (RDFClosure T v (Set.ofList G) (Set.ofList E)) := by
  rw [rdfCheck, InstanceSearch.check_iff, rdf_exact]

theorem rdfsCheck_iff (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G E : List (GeneralizedTriple Iri Literal B)) :
    rdfsCheck T.literalSyntax.datatype v d G E = true ↔
      ∃ μ, Set.subset (GeneralizedGraph.substitute μ (Set.ofList E))
        (RDFSClosure T v (Set.ofList G) (Set.ofList E)) := by
  rw [rdfsCheck, InstanceSearch.check_iff, rdfs_exact]

theorem rdfCheck_sound (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G E : List (GeneralizedTriple Iri Literal B))
    (h : rdfCheck T.literalSyntax.datatype v d G E = true) :
    RDFEntails.{u} T v.baseDatatypes v (Set.ofList G) (Set.ofList E) := by
  obtain ⟨μ, hm⟩ := (rdfCheck_iff T v d G E).mp h
  exact rdf_closure_instance_check_sound T v _ _ μ hm

theorem rdfsCheck_sound (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G E : List (GeneralizedTriple Iri Literal B))
    (h : rdfsCheck T.literalSyntax.datatype v d G E = true) :
    RDFSEntails.{u} T v.toRDF.baseDatatypes v (Set.ofList G) (Set.ofList E) := by
  obtain ⟨μ, hm⟩ := (rdfsCheck_iff T v d G E).mp h
  exact rdfs_closure_instance_check_sound T v _ _ μ hm

def rdfInstanceDecision (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G E : List (GeneralizedTriple Iri Literal B)) :
    Decidable (∃ μ, Set.subset (GeneralizedGraph.substitute μ (Set.ofList E))
      (RDFClosure T v (Set.ofList G) (Set.ofList E))) :=
  decidable_of_iff (rdfCheck T.literalSyntax.datatype v d G E = true) (rdfCheck_iff T v d G E)

def rdfsInstanceDecision (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G E : List (GeneralizedTriple Iri Literal B)) :
    Decidable (∃ μ, Set.subset (GeneralizedGraph.substitute μ (Set.ofList E))
      (RDFSClosure T v (Set.ofList G) (Set.ofList E))) :=
  decidable_of_iff (rdfsCheck T.literalSyntax.datatype v d G E = true) (rdfsCheck_iff T v d G E)

theorem rdfCheck_ordinary_iff (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B)) (E : List (Triple Iri Literal B)) :
    rdfCheck T.literalSyntax.datatype v d G (E.map Triple.generalize) = true ↔
      SimplyEntails.{u} (RDFClosure T v (Set.ofList G) (Graph.generalize (Set.ofList E)))
        (Graph.generalize (Set.ofList E)) := by
  rw [rdfCheck_iff, InstanceSearch.generalize_list, ordinary_interpolation]

theorem rdfsCheck_ordinary_iff (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B)) (E : List (Triple Iri Literal B)) :
    rdfsCheck T.literalSyntax.datatype v d G (E.map Triple.generalize) = true ↔
      SimplyEntails.{u} (RDFSClosure T v (Set.ofList G) (Graph.generalize (Set.ofList E)))
        (Graph.generalize (Set.ofList E)) := by
  rw [rdfsCheck_iff, InstanceSearch.generalize_list, ordinary_interpolation]

theorem rdfCheck_respects_graphs (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G H E F : List (GeneralizedTriple Iri Literal B))
    (hG : Set.ofList G = Set.ofList H) (hE : Set.ofList E = Set.ofList F) :
    rdfCheck T.literalSyntax.datatype v d G E = rdfCheck T.literalSyntax.datatype v d H F := by
  apply Bool.eq_iff_iff.mpr
  rw [rdfCheck_iff, rdfCheck_iff, hG, hE]

theorem rdfsCheck_respects_graphs (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G H E F : List (GeneralizedTriple Iri Literal B))
    (hG : Set.ofList G = Set.ofList H) (hE : Set.ofList E = Set.ofList F) :
    rdfsCheck T.literalSyntax.datatype v d G E = rdfsCheck T.literalSyntax.datatype v d H F := by
  apply Bool.eq_iff_iff.mpr
  rw [rdfsCheck_iff, rdfsCheck_iff, hG, hE]

omit [DecidableEq B] in
def rdfApartCheck [DecidableEq B₁] [DecidableEq B₂]
    (datatype : Literal → Iri) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) : Bool :=
  rdfCheck datatype v d (G.map (GeneralizedTriple.mapBlank Sum.inl))
    (E.map (GeneralizedTriple.mapBlank Sum.inr))

omit [DecidableEq B] in
def rdfsApartCheck [DecidableEq B₁] [DecidableEq B₂]
    (datatype : Literal → Iri) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂)) : Bool :=
  rdfsCheck datatype v d (G.map (GeneralizedTriple.mapBlank Sum.inl))
    (E.map (GeneralizedTriple.mapBlank Sum.inr))

omit [DecidableEq B] in
theorem rdfApartCheck_sound [DecidableEq B₁] [DecidableEq B₂]
    (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.container n)))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (h : rdfApartCheck T.literalSyntax.datatype v d G E = true) :
    RDFEntails.{u} T v.baseDatatypes v (Set.ofList G) (Set.ofList E) := by
  have hs := rdfCheck_sound.{u} T v d _ _ h
  rw [InstanceSearch.mapBlank_list, InstanceSearch.mapBlank_list] at hs
  intro U I hI hG
  exact (InstanceSearch.satisfies_right I _).mp
    (hs U I hI ((InstanceSearch.satisfies_left I _).mpr hG))

omit [DecidableEq B] in
theorem rdfsApartCheck_sound [DecidableEq B₁] [DecidableEq B₂]
    (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (d : ContainerDecoder (fun n => v.iri (.rdf (.container n))))
    (G : List (GeneralizedTriple Iri Literal B₁)) (E : List (GeneralizedTriple Iri Literal B₂))
    (h : rdfsApartCheck T.literalSyntax.datatype v d G E = true) :
    RDFSEntails.{u} T v.toRDF.baseDatatypes v (Set.ofList G) (Set.ofList E) := by
  have hs := rdfsCheck_sound.{u} T v d _ _ h
  rw [InstanceSearch.mapBlank_list, InstanceSearch.mapBlank_list] at hs
  intro U I hI hG
  exact (InstanceSearch.satisfies_right I _).mp
    (hs U I hI ((InstanceSearch.satisfies_left I _).mpr hG))

end RDF11.ClosureEvaluation
