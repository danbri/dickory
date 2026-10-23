/-
Semantics §10's IRI graph-name denotation caution, in a declared simple-model
example. Graph objects are explicitly embedded in the resource carrier.
The same named pair and true RDF triples permit either name/graph equality or
inequality. No universal dataset truth relation or mandatory graph embedding
is inferred from the specification. RDF/RDFS model existence is separate.
-/
import RDF11.Datasets

namespace RDF11.DatasetNameExample

def graph : Graph Unit Empty Empty := Set.singleton ⟨.iri (), (), .iri ()⟩

def dataset : Dataset Unit Empty Empty :=
  ⟨graph, fun n => match n with
    | .iri _ => some graph
    | .blank b => nomatch b⟩

abbrev Carrier := Sum (Graph Unit Empty Empty) Unit

def graphObject (G : Graph Unit Empty Empty) : Carrier := .inl G

theorem graphObject_injective {G H : Graph Unit Empty Empty}
    (h : graphObject G = graphObject H) : G = H := Sum.inl.inj h

def nameValue (refersToGraph : Bool) : Carrier :=
  if refersToGraph then graphObject graph else .inr ()

def interpretation (refersToGraph : Bool) : SimpleInterpretation Unit Empty Carrier where
  IR := fun _ => True
  IR_nonempty := ⟨.inr (), True.intro⟩
  IP := fun _ => True
  IEXT := fun _ _ => True
  IS := fun _ => ⟨nameValue refersToGraph, Or.inl True.intro⟩
  IL := fun l => nomatch l

theorem named_pair : dataset.HasNamedGraph (.iri ()) graph := rfl

theorem graph_satisfied (refersToGraph : Bool) :
    (interpretation refersToGraph).Satisfies graph.generalize := by
  apply ((interpretation refersToGraph).satisfies_iff_exists_graphTrue _).mpr
  refine ⟨(fun b => nomatch b), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  change t = ⟨.iri (), (), .iri ()⟩ at ht
  subst t
  exact ⟨⟨nameValue refersToGraph, True.intro⟩, ⟨nameValue refersToGraph, True.intro⟩,
    ⟨nameValue refersToGraph, True.intro⟩, rfl, rfl, rfl, True.intro⟩

theorem all_components_satisfied (refersToGraph : Bool) :
    (interpretation refersToGraph).Satisfies dataset.defaultGraph.generalize ∧
      ∀ n G, dataset.HasNamedGraph n G → (interpretation refersToGraph).Satisfies G.generalize := by
  refine ⟨graph_satisfied refersToGraph, ?_⟩
  intro n G hn
  cases n with
  | blank b => exact nomatch b
  | iri i =>
    have hG : graph = G := Option.some.inj hn
    exact hG ▸ graph_satisfied refersToGraph

theorem name_can_denote_graph :
    ((interpretation true).IS ()).val = graphObject graph := rfl

theorem name_can_denote_something_else :
    ((interpretation false).IS ()).val ≠ graphObject graph := by
  intro h
  cases h

theorem pairing_and_component_truth_allow_both :
    dataset.HasNamedGraph (.iri ()) graph ∧
      (interpretation true).Satisfies graph.generalize ∧
      (interpretation false).Satisfies graph.generalize ∧
      ((interpretation true).IS ()).val = graphObject graph ∧
      ((interpretation false).IS ()).val ≠ graphObject graph :=
  ⟨named_pair, graph_satisfied true, graph_satisfied false,
    name_can_denote_graph, name_can_denote_something_else⟩

end RDF11.DatasetNameExample
