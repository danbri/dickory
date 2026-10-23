/-
Semantics §10's IRI graph-name denotation caution, with §5's global name scope.
The witness is generic over the full IRI/literal types and any blank domain.
IS is total on all IRIs; IL is a permitted everywhere-undefined partial map.
Graph objects are explicitly embedded in the resource carrier. No universal
embedding or dataset truth relation is imposed. RDF/RDFS models are separate.
-/
import RDF11.Datasets

namespace RDF11.DatasetNameExample

variable {Iri Literal B : Type}

def graph (name : Iri) : Graph Iri Literal B := Set.singleton ⟨.iri name, name, .iri name⟩

noncomputable def dataset (name : Iri) : Dataset Iri Literal B := by
  classical
  exact ⟨graph name, fun n => match n with
    | .iri i => if i = name then some (graph name) else none
    | .blank _ => none⟩

abbrev Carrier (Iri Literal B : Type) := Sum (Graph Iri Literal B) Unit

def graphObject (G : Graph Iri Literal B) : Carrier Iri Literal B := .inl G

theorem graphObject_injective {G H : Graph Iri Literal B}
    (h : graphObject G = graphObject H) : G = H := Sum.inl.inj h

def nameValue (name : Iri) (refersToGraph : Bool) : Carrier Iri Literal B :=
  if refersToGraph then graphObject (graph name) else .inr ()

def interpretation (name : Iri) (refersToGraph : Bool) :
    SimpleInterpretation Iri Literal (Carrier Iri Literal B) where
  IR := fun _ => True
  IR_nonempty := ⟨.inr (), True.intro⟩
  IP := fun _ => True
  IEXT := fun _ _ => True
  IS := fun _ => ⟨nameValue name refersToGraph, Or.inl True.intro⟩
  IL := fun _ => none

theorem named_pair (name : Iri) :
    (dataset name : Dataset Iri Literal B).HasNamedGraph (.iri name) (graph name) := by
  simp [dataset, Dataset.HasNamedGraph]

theorem graph_satisfied (name : Iri) (refersToGraph : Bool) :
    (interpretation (Literal := Literal) (B := B) name refersToGraph).Satisfies
      (graph name : Graph Iri Literal B).generalize := by
  apply ((interpretation name refersToGraph).satisfies_iff_exists_graphTrue _).mpr
  refine ⟨(fun _ => some ⟨nameValue name refersToGraph, True.intro⟩), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  change t = ⟨.iri name, name, .iri name⟩ at ht
  subst t
  exact ⟨⟨nameValue name refersToGraph, True.intro⟩, ⟨nameValue name refersToGraph, True.intro⟩,
    ⟨nameValue name refersToGraph, True.intro⟩, rfl, rfl, rfl, True.intro⟩

theorem all_components_satisfied (name : Iri) (refersToGraph : Bool) :
    (interpretation (Literal := Literal) (B := B) name refersToGraph).Satisfies
        (dataset name : Dataset Iri Literal B).defaultGraph.generalize ∧
      ∀ n G, (dataset name : Dataset Iri Literal B).HasNamedGraph n G →
        (interpretation (Literal := Literal) (B := B) name refersToGraph).Satisfies G.generalize := by
  classical
  refine ⟨graph_satisfied name refersToGraph, ?_⟩
  intro n G hn
  cases n with
  | blank b => simp [Dataset.HasNamedGraph, dataset] at hn
  | iri i =>
    by_cases hi : i = name
    · have hG : graph name = G := by simpa [Dataset.HasNamedGraph, dataset, hi] using hn
      exact hG ▸ graph_satisfied name refersToGraph
    · simp [Dataset.HasNamedGraph, dataset, hi] at hn

theorem name_can_denote_graph (name : Iri) :
    ((interpretation (Literal := Literal) (B := B) name true).IS name).val =
      graphObject (graph name) := rfl

theorem name_can_denote_something_else (name : Iri) :
    ((interpretation (Literal := Literal) (B := B) name false).IS name).val ≠
      graphObject (graph name) := by
  intro h
  cases h

theorem pairing_and_component_truth_allow_both (name : Iri) :
    (dataset name : Dataset Iri Literal B).HasNamedGraph (.iri name) (graph name) ∧
      (interpretation (Literal := Literal) (B := B) name true).Satisfies
        (graph name : Graph Iri Literal B).generalize ∧
      (interpretation (Literal := Literal) (B := B) name false).Satisfies
        (graph name : Graph Iri Literal B).generalize ∧
      ((interpretation (Literal := Literal) (B := B) name true).IS name).val = graphObject (graph name) ∧
      ((interpretation (Literal := Literal) (B := B) name false).IS name).val ≠ graphObject (graph name) :=
  ⟨named_pair name, graph_satisfied name true, graph_satisfied name false,
    name_can_denote_graph name, name_can_denote_something_else name⟩

end RDF11.DatasetNameExample
