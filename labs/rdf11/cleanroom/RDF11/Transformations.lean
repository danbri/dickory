/-
RDF 1.1 Semantics §5.2 and §3: satisfaction, validity and semantic extensions.
A process is represented by its possible input/output pairs, without imposing
an algorithm or a requirement to execute any inference.
-/
import RDF11.Entailment

namespace RDF11

def SimplySatisfiable.{u} (G : GeneralizedGraph Iri Literal B) : Prop :=
  ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.Satisfies G

def SimplyUnsatisfiable.{u} (G : GeneralizedGraph Iri Literal B) : Prop :=
  ¬ SimplySatisfiable.{u} G

theorem simply_satisfiable (G : GeneralizedGraph Iri Literal B) : SimplySatisfiable.{u} G :=
  all_graphs_simply_satisfiable G

theorem never_simply_unsatisfiable (G : GeneralizedGraph Iri Literal B) :
    ¬ SimplyUnsatisfiable.{u} G := fun h => h (simply_satisfiable G)

def SimplyValid.{u}
    (process : GeneralizedGraph Iri Literal B₁ → GeneralizedGraph Iri Literal B₂ → Prop) : Prop :=
  ∀ G E, process G E → SimplyEntails.{u} G E

def SimplyInvalid.{u}
    (process : GeneralizedGraph Iri Literal B₁ → GeneralizedGraph Iri Literal B₂ → Prop) : Prop :=
  ¬ SimplyValid.{u} process

theorem valid_composition
    (first : GeneralizedGraph Iri Literal B₁ → GeneralizedGraph Iri Literal B₂ → Prop)
    (second : GeneralizedGraph Iri Literal B₂ → GeneralizedGraph Iri Literal B₃ → Prop)
    (hf : SimplyValid.{u} first) (hs : SimplyValid.{u} second) :
    SimplyValid.{u} (fun G E => ∃ H, first G H ∧ second H E) := by
  rintro G E ⟨H, hGH, hHE⟩
  exact simplyEntails_trans (hf G H hGH) (hs H E hHE)

theorem subgraph_process_valid :
    SimplyValid.{u} (fun (G E : GeneralizedGraph Iri Literal B) => Set.subset E G) :=
  fun _ _ h => subgraph_entailment h

theorem valid_under_extension
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    (process : GeneralizedGraph Iri Literal B₁ → GeneralizedGraph Iri Literal B₂ → Prop)
    (h : SimplyValid.{u} process) : ∀ G E, process G E → EntailsUnder C G E :=
  fun G E hGE => extension_preserves_simple_entailment C (h G E hGE)

end RDF11
