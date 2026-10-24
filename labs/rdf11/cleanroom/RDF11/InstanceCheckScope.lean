/-
Connect executable answers to the existing source-scope witnesses.
A generalized instance success need not be simple entailment. Conversely,
a selected-closure failure need not be RDF/RDFS non-entailment. These are
checked boundaries of the current transcription, not adopted W3C errata.
-/
import RDF11.ClosureInstanceCheck
import RDF11.GeneralizedScope
import RDF11.ClosureSelectionScope

namespace RDF11.InstanceCheckScope

theorem generalized_success [DecidableEq Iri] [DecidableEq Literal] (s p : Iri) :
    InstanceSearch.check [(GeneralizedScope.substitutedTriple s p : GeneralizedTriple Iri Literal Unit)]
      [GeneralizedScope.originalTriple s] = true := by
  apply (InstanceSearch.check_iff _ _).mpr
  refine ⟨fun _ => some (.iri p), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have ht' : t = GeneralizedScope.originalTriple s := by simpa [Set.ofList] using ht
  subst t
  simp [Set.ofList, GeneralizedScope.originalTriple, GeneralizedScope.substitutedTriple,
    GeneralizedTriple.substitute, Term.substitute, Substitution.resolve]

theorem generalized_success_not_entails [DecidableEq Iri] [DecidableEq Literal]
    (s p : Iri) (h : s ≠ p) :
    InstanceSearch.check [(GeneralizedScope.substitutedTriple s p : GeneralizedTriple Iri Literal Unit)]
      [GeneralizedScope.originalTriple s] = true ∧
    ¬ SimplyEntails.{0} (Set.ofList [(GeneralizedScope.substitutedTriple s p : GeneralizedTriple Iri Literal Unit)])
      (Set.ofList [GeneralizedScope.originalTriple s]) := by
  refine ⟨generalized_success s p, ?_⟩
  rw [InstanceSearch.singleton_list, InstanceSearch.singleton_list]
  exact GeneralizedScope.unrestricted_generalized_instance_consequence_fails s p h

open ClosureSelection ClosureEvaluation

def decode : ClosureSelection.Iri → Option Nat
  | .inl (.rdf (.container n)) => some n
  | _ => none

def decoder : ContainerDecoder (fun n => vocabulary.iri (.rdf (.container n))) where
  decode := decode
  correct := by
    intro a n
    cases a with
    | inr b => simp [decode, vocabulary]
    | inl s =>
      cases s with
      | rdf r => cases r <;> simp [decode, vocabulary]
      | _ => simp [decode, vocabulary]

theorem premise_list :
    Set.ofList [(premiseTriple : Triple ClosureSelection.Iri Literal B).generalize] =
      (premise : Graph ClosureSelection.Iri Literal B).generalize := by
  apply Set.ext
  intro t
  simp [premise, Graph.generalize, Set.ofList, Set.singleton, Set.image, eq_comm]

theorem conclusion_list :
    Set.ofList [(conclusionTriple : Triple ClosureSelection.Iri Literal B).generalize] =
      (conclusion : Graph ClosureSelection.Iri Literal B).generalize := by
  apply Set.ext
  intro t
  simp [conclusion, Graph.generalize, Set.ofList, Set.singleton, Set.image, eq_comm]

theorem selection_failure [DecidableEq Literal] [DecidableEq B]
    (T : DatatypeTheory ClosureSelection.Iri Literal Value) :
    rdfsCheck T.literalSyntax.datatype vocabulary decoder
      [(premiseTriple : Triple ClosureSelection.Iri Literal B).generalize]
      [conclusionTriple.generalize] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨μ, hm⟩ := (rdfsCheck_iff T vocabulary decoder _ _).mp h
  rw [premise_list, conclusion_list] at hm
  exact closure_has_no_conclusion_instance T μ hm

theorem selection_failure_consistent [DecidableEq Literal] [DecidableEq B]
    (T : DatatypeTheory ClosureSelection.Iri Literal Value)
    (h : RDFSModelConstruction.Parameters T vocabulary.toRDF.baseDatatypes vocabulary) :
    rdfsCheck T.literalSyntax.datatype vocabulary decoder
      [(premiseTriple : Triple ClosureSelection.Iri Literal B).generalize]
      [conclusionTriple.generalize] = false ∧
    RDFSEntails.{u} T vocabulary.toRDF.baseDatatypes vocabulary
      (premise : Graph ClosureSelection.Iri Literal B).generalize (conclusion : Graph ClosureSelection.Iri Literal B).generalize ∧
    ∃ (U : Type u) (I : SimpleInterpretation ClosureSelection.Iri Literal U),
      I.RDFSModel T vocabulary.toRDF.baseDatatypes vocabulary ∧
      I.Satisfies (premise : Graph ClosureSelection.Iri Literal B).generalize :=
  ⟨selection_failure T, full_entailment T, premise_consistent T h⟩

end RDF11.InstanceCheckScope
