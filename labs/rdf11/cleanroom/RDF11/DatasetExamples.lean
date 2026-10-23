/-
Semantics §10: replacing an equivalent default graph can disrupt shared blanks.
This finite structural example uses one abstract IRI, no literals, and two
blank identities. It proves non-isomorphism, not a dataset entailment claim.
-/
import RDF11.DatasetIsomorphism

namespace RDF11.DatasetSharingExample

def defaultFor (b : Bool) : Graph Unit Empty Bool :=
  Set.singleton ⟨.iri (), (), .blank b⟩

def namedFor (b : Bool) : Graph Unit Empty Bool :=
  Set.singleton ⟨.blank b, (), .iri ()⟩

def dataset (b : Bool) : Dataset Unit Empty Bool :=
  ⟨defaultFor b, fun n => match n with
    | .iri _ => some (namedFor false)
    | .blank _ => none⟩

theorem default_map (f : Bool → Bool) (b : Bool) :
    (defaultFor b).mapBlank f = defaultFor (f b) := by
  apply Set.ext
  intro t
  simp [Graph.mapBlank, defaultFor, Set.image, Set.singleton, Triple.mapBlank,
    Subject.mapBlank, Term.mapBlank, eq_comm]

theorem named_map (f : Bool → Bool) (b : Bool) :
    (namedFor b).mapBlank f = namedFor (f b) := by
  apply Set.ext
  intro t
  simp [Graph.mapBlank, namedFor, Set.image, Set.singleton, Triple.mapBlank,
    Subject.mapBlank, Term.mapBlank, eq_comm]

theorem default_injective {b c : Bool} (h : defaultFor b = defaultFor c) : b = c := by
  have ht : defaultFor c ⟨.iri (), (), .blank b⟩ := h ▸ rfl
  simpa [defaultFor, Set.singleton] using ht

theorem named_injective {b c : Bool} (h : namedFor b = namedFor c) : b = c := by
  have ht : namedFor c ⟨.blank b, (), .iri ()⟩ := h ▸ rfl
  simpa [namedFor, Set.singleton] using ht

def default_isomorphism :
    GraphIsomorphism (dataset false).defaultGraph.generalize
      (dataset true).defaultGraph.generalize where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by intro b _; cases b <;> rfl
  right_inv := by intro b _; cases b <;> rfl
  image_eq := by
    change (defaultFor false).generalize.mapBlank Bool.not = (defaultFor true).generalize
    rw [← Graph.generalize_mapBlank, default_map]
    rfl

theorem defaults_equivalent : LogicallyEquivalent.{u}
    (dataset false).defaultGraph.generalize (dataset true).defaultGraph.generalize :=
  default_isomorphism.equivalent

theorem named_graphs_unchanged : (dataset false).namedGraphs = (dataset true).namedGraphs := rfl

theorem no_dataset_isomorphism : ¬ Nonempty (DatasetIsomorphism (dataset false) (dataset true)) := by
  rintro ⟨e⟩
  have hd : e.toFun false = true :=
    default_injective ((default_map e.toFun false).symm.trans e.default_eq)
  have hn := e.named_forward (.iri ()) (namedFor false) rfl
  change some (namedFor false) = some ((namedFor false).mapBlank e.toFun) at hn
  have hn' : e.toFun false = false :=
    named_injective ((named_map e.toFun false).symm.trans (Option.some.inj hn).symm)
  exact Bool.noConfusion (hd.symm.trans hn')

/-- The empty named graph itself carries its blank graph-name identity. -/
theorem empty_blank_name_occurs (b : B) :
    (Dataset.emptyNamed (.blank b) : Dataset Iri Literal B).hasBlank b :=
  Or.inr ⟨.blank b, Set.empty, Dataset.emptyNamed_present (.blank b), Or.inl rfl⟩

theorem empty_named_not_isomorphic_to_empty (n : GraphName Iri B) :
    ¬ Nonempty (DatasetIsomorphism (Dataset.emptyNamed n : Dataset Iri Literal B)
      Dataset.empty) := by
  rintro ⟨e⟩
  have hn := e.named_forward n Set.empty (Dataset.emptyNamed_present n)
  cases hn

end RDF11.DatasetSharingExample
