/-
Semantics §10 gives matching-name graph entailments, with missing graphs filled
by the empty graph, as a possible requirement of an illustrative extension.
This is a parameterized comparison condition, not complete dataset semantics.
-/
import RDF11.DatasetExamples

namespace RDF11

def Dataset.namedGraphOrEmpty (D : Dataset Iri Literal B) (n : GraphName Iri B) :
    Graph Iri Literal B := (D.namedGraphs n).getD Set.empty

theorem Dataset.namedGraphOrEmpty_of_present (D : Dataset Iri Literal B)
    (n : GraphName Iri B) (G : Graph Iri Literal B) (h : D.HasNamedGraph n G) :
    D.namedGraphOrEmpty n = G := by
  change D.namedGraphs n = some G at h
  simp [namedGraphOrEmpty, h]

theorem Dataset.namedGraphOrEmpty_of_absent (D : Dataset Iri Literal B)
    (n : GraphName Iri B) (h : D.namedGraphs n = none) :
    D.namedGraphOrEmpty n = Set.empty := by
  simp [namedGraphOrEmpty, h]

theorem Dataset.emptyNamed_graphAt (n m : GraphName Iri B) :
    (Dataset.emptyNamed n : Dataset Iri Literal B).namedGraphOrEmpty m = Set.empty := by
  classical
  by_cases h : m = n <;> simp [namedGraphOrEmpty, emptyNamed, h]

def NamedGraphComparison
    (graphEntails : Graph Iri Literal B → Graph Iri Literal B → Prop)
    (D E : Dataset Iri Literal B) : Prop :=
  ∀ n, graphEntails (D.namedGraphOrEmpty n) (E.namedGraphOrEmpty n)

theorem namedGraphComparison_refl
    (graphEntails : Graph Iri Literal B → Graph Iri Literal B → Prop)
    (h : ∀ G, graphEntails G G) (D : Dataset Iri Literal B) :
    NamedGraphComparison graphEntails D D := fun _ => h _

theorem namedGraphComparison_trans
    (graphEntails : Graph Iri Literal B → Graph Iri Literal B → Prop)
    (h : ∀ G H K, graphEntails G H → graphEntails H K → graphEntails G K)
    {D E F : Dataset Iri Literal B} (hDE : NamedGraphComparison graphEntails D E)
    (hEF : NamedGraphComparison graphEntails E F) : NamedGraphComparison graphEntails D F :=
  fun n => h _ _ _ (hDE n) (hEF n)

def SimpleNamedGraphComparison.{u} (D E : Dataset Iri Literal B) : Prop :=
  NamedGraphComparison (fun G H => SimplyEntails.{u} G.generalize H.generalize) D E

theorem empty_named_matches_absent (n : GraphName Iri B) :
    SimpleNamedGraphComparison.{u} (Dataset.emptyNamed n : Dataset Iri Literal B) Dataset.empty ∧
      SimpleNamedGraphComparison.{u} Dataset.empty (Dataset.emptyNamed n : Dataset Iri Literal B) := by
  constructor <;> intro m
  all_goals
    change SimplyEntails _ _
    rw [Dataset.emptyNamed_graphAt]
    exact simplyEntails_refl _

theorem matching_graphs_need_not_be_isomorphic (n : GraphName Iri B) :
    SimpleNamedGraphComparison.{u} (Dataset.emptyNamed n : Dataset Iri Literal B) Dataset.empty ∧
      SimpleNamedGraphComparison.{u} Dataset.empty (Dataset.emptyNamed n : Dataset Iri Literal B) ∧
      ¬ Nonempty (DatasetIsomorphism (Dataset.emptyNamed n : Dataset Iri Literal B) Dataset.empty) :=
  ⟨(empty_named_matches_absent n).1, (empty_named_matches_absent n).2,
    DatasetSharingExample.empty_named_not_isomorphic_to_empty n⟩

end RDF11
