/-
RDF 1.1 Semantics §4.1 and §5.1–5.2: arbitrary families of graphs.
Union retains shared identities. Merge uses one disjoint copy per input.
No finiteness or inhabited-index hypothesis is imposed. The satisfaction
equivalences are derived from the specified truth conditions.
-/
import RDF11.Datasets

namespace RDF11

def Set.iUnion (S : K → Set α) : Set α := fun a => ∃ i, S i a

theorem Set.image_iUnion (f : α → β) (S : K → Set α) :
    image f (iUnion S) = iUnion (fun i => image f (S i)) := by
  apply ext
  intro b
  exact ⟨fun ⟨a, ⟨i, ha⟩, hab⟩ => ⟨i, a, ha, hab⟩,
    fun ⟨i, a, ha, hab⟩ => ⟨a, ⟨i, ha⟩, hab⟩⟩

namespace GraphFamily

variable {K Iri Literal B : Type} {Bs : K → Type}

def merge (G : (i : K) → GeneralizedGraph Iri Literal (Bs i)) :
    GeneralizedGraph Iri Literal (Sigma Bs) :=
  Set.iUnion fun i => (G i).mapBlank (Sigma.mk i)

def ordinaryMerge (G : (i : K) → Graph Iri Literal (Bs i)) :
    Graph Iri Literal (Sigma Bs) :=
  Set.iUnion fun i => (G i).mapBlank (Sigma.mk i)

/-- Literal set-of-graphs indexing: each graph is included once. -/
def unionSet (S : Set (GeneralizedGraph Iri Literal B)) :
    GeneralizedGraph Iri Literal B := Set.iUnion (fun G : {G // S G} => G.val)

def mergeSet (S : Set (GeneralizedGraph Iri Literal B)) :
    GeneralizedGraph Iri Literal (Sigma (fun _ : {G // S G} => B)) :=
  merge (fun G : {G // S G} => G.val)

theorem generalize_union (G : K → Graph Iri Literal B) :
    Graph.generalize (Set.iUnion G) = Set.iUnion (fun i => (G i).generalize) :=
  Set.image_iUnion Triple.generalize G

theorem ordinaryMerge_generalize (G : (i : K) → Graph Iri Literal (Bs i)) :
    (ordinaryMerge G).generalize = merge (fun i => (G i).generalize) := by
  rw [ordinaryMerge, generalize_union]
  simp only [Graph.generalize_mapBlank, merge]

theorem union_hasBlank (G : K → GeneralizedGraph Iri Literal B) (b : B) :
    GeneralizedGraph.hasBlank (Set.iUnion G) b ↔ ∃ i, (G i).hasBlank b := by
  exact ⟨fun ⟨t, ⟨i, ht⟩, hb⟩ => ⟨i, t, ht, hb⟩,
    fun ⟨i, t, ht, hb⟩ => ⟨t, ⟨i, ht⟩, hb⟩⟩

theorem merge_hasBlank (G : (i : K) → GeneralizedGraph Iri Literal (Bs i))
    (b : Sigma Bs) : (merge G).hasBlank b ↔ (G b.1).hasBlank b.2 := by
  rw [merge, union_hasBlank]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨a, ha, he⟩ := ((G i).hasBlank_mapBlank (Sigma.mk i) b).mp hi
    cases he
    exact ha
  · intro h
    exact ⟨b.1, ((G b.1).hasBlank_mapBlank (Sigma.mk b.1) b).mpr ⟨b.2, h, rfl⟩⟩

/-- Disjointness concerns occurring blanks, not the ambient identity type. -/
def Apart (G : K → GeneralizedGraph Iri Literal B) : Prop :=
  ∀ i j b, (G i).hasBlank b → (G j).hasBlank b → i = j

end GraphFamily

namespace SimpleInterpretation

variable {K Iri Literal B : Type} {U : Type u}

theorem graphTrue_iUnion (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (G : K → GeneralizedGraph Iri Literal B) :
    I.GraphTrue A (Set.iUnion G) ↔ ∀ i, I.GraphTrue A (G i) := by
  exact ⟨fun h i t ht => h t ⟨i, ht⟩, fun h t ⟨i, ht⟩ => h i t ht⟩

theorem satisfies_iUnion (I : SimpleInterpretation Iri Literal U)
    (G : K → GeneralizedGraph Iri Literal B) :
    I.Satisfies (Set.iUnion G) ↔ ∃ A, ∀ i, I.GraphTrue A (G i) := by
  rw [I.satisfies_iff_exists_graphTrue]
  exact exists_congr fun A => I.graphTrue_iUnion A G

/-- These are separate graph witnesses which agree wherever identity is shared. -/
def Coherent (I : SimpleInterpretation Iri Literal U)
    (G : K → GeneralizedGraph Iri Literal B) (A : K → I.Assignment B) : Prop :=
  ∀ i j b, (G i).hasBlank b → (G j).hasBlank b → A i b = A j b

noncomputable def amalgamate (I : SimpleInterpretation Iri Literal U)
    (G : K → GeneralizedGraph Iri Literal B) (A : K → I.Assignment B) :
    I.Assignment B := by
  classical
  exact fun b => if h : ∃ i, (G i).hasBlank b then A (Classical.choose h) b else none

theorem amalgamate_agrees (I : SimpleInterpretation Iri Literal U)
    (G : K → GeneralizedGraph Iri Literal B) (A : K → I.Assignment B)
    (h : I.Coherent G A) (i : K) (b : B) (hb : (G i).hasBlank b) :
    I.amalgamate G A b = A i b := by
  have hex : ∃ j, (G j).hasBlank b := ⟨i, hb⟩
  simp only [amalgamate, dif_pos hex]
  exact h _ i b (Classical.choose_spec hex) hb

theorem satisfies_iUnion_iff_coherent (I : SimpleInterpretation Iri Literal U)
    (G : K → GeneralizedGraph Iri Literal B) :
    I.Satisfies (Set.iUnion G) ↔
      ∃ A : K → I.Assignment B, (∀ i, I.GraphTrue (A i) (G i)) ∧ I.Coherent G A := by
  constructor
  · rintro h
    obtain ⟨A, hA⟩ := (I.satisfies_iUnion G).mp h
    exact ⟨fun _ => A, hA, fun _ _ _ _ _ => rfl⟩
  · rintro ⟨A, hA, hc⟩
    apply (I.satisfies_iUnion G).mpr
    refine ⟨I.amalgamate G A, fun i t ht => ?_⟩
    apply (I.tripleTrue_agrees t ?_).mpr (hA i t ht)
    exact fun b hb => I.amalgamate_agrees G A hc i b ⟨t, ht, hb⟩

theorem satisfies_iUnion_of_apart (I : SimpleInterpretation Iri Literal U)
    (G : K → GeneralizedGraph Iri Literal B) (hG : GraphFamily.Apart G) :
    I.Satisfies (Set.iUnion G) ↔ ∀ i, I.Satisfies (G i) := by
  constructor
  · intro h i
    exact I.satisfies_subgraph (fun t ht => ⟨i, ht⟩) h
  · intro h
    let A i := Classical.choose ((I.satisfies_iff_exists_graphTrue (G i)).mp (h i))
    have hA i : I.GraphTrue (A i) (G i) :=
      Classical.choose_spec ((I.satisfies_iff_exists_graphTrue (G i)).mp (h i))
    apply (I.satisfies_iUnion_iff_coherent G).mpr
    exact ⟨A, hA, fun i j b hi hj => congrArg (fun k => A k b) (hG i j b hi hj)⟩

end SimpleInterpretation

namespace GraphFamily

variable {K Iri Literal B : Type} {Bs : K → Type}

theorem graphTrue_merge (I : SimpleInterpretation Iri Literal U)
    (G : (i : K) → GeneralizedGraph Iri Literal (Bs i))
    (A : (i : K) → I.Assignment (Bs i)) :
    I.GraphTrue (fun b => A b.1 b.2) (merge G) ↔
      ∀ i, I.GraphTrue (A i) (G i) := by
  rw [merge, I.graphTrue_iUnion]
  constructor
  · exact fun h i => (I.graphTrue_mapBlank (Sigma.mk i) _ (G i)).mp (h i)
  · exact fun h i => (I.graphTrue_mapBlank (Sigma.mk i) _ (G i)).mpr (h i)

theorem satisfies_merge (I : SimpleInterpretation Iri Literal U)
    (G : (i : K) → GeneralizedGraph Iri Literal (Bs i)) :
    I.Satisfies (merge G) ↔ ∀ i, I.Satisfies (G i) := by
  constructor
  · intro h i
    exact I.satisfies_mapBlank_implies (Sigma.mk i) (G i)
      (I.satisfies_subgraph (fun t ht => ⟨i, ht⟩) h)
  · intro h
    let A i := Classical.choose ((I.satisfies_iff_exists_graphTrue (G i)).mp (h i))
    have hA i : I.GraphTrue (A i) (G i) :=
      Classical.choose_spec ((I.satisfies_iff_exists_graphTrue (G i)).mp (h i))
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    exact ⟨fun b => A b.1 b.2, (graphTrue_merge I G A).mpr hA⟩

theorem union_entails_merge (G : K → GeneralizedGraph Iri Literal B) :
    SimplyEntails.{u} (Set.iUnion G) (merge G) := by
  intro U I h
  exact (satisfies_merge I G).mpr fun i =>
    I.satisfies_subgraph (fun t ht => ⟨i, ht⟩) h

theorem apart_union_equivalent_merge (G : K → GeneralizedGraph Iri Literal B)
    (hG : Apart G) : LogicallyEquivalent.{u} (Set.iUnion G) (merge G) := by
  refine ⟨union_entails_merge G, fun U I h => ?_⟩
  exact (I.satisfies_iUnion_of_apart G hG).mpr ((satisfies_merge I G).mp h)

theorem merge_entails_iff (G : (i : K) → GeneralizedGraph Iri Literal (Bs i))
    (E : GeneralizedGraph Iri Literal B) :
    SimplyEntails.{u} (merge G) E ↔
      ∀ (U : Type u) (I : SimpleInterpretation Iri Literal U),
        (∀ i, I.Satisfies (G i)) → I.Satisfies E := by
  exact ⟨fun h U I hG => h U I ((satisfies_merge I G).mpr hG),
    fun h U I hG => h U I ((satisfies_merge I G).mp hG)⟩

theorem union_entails_iff (G : K → GeneralizedGraph Iri Literal B)
    (E : GeneralizedGraph Iri Literal B') :
    SimplyEntails.{u} (Set.iUnion G) E ↔
      ∀ (U : Type u) (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B),
        (∀ i, I.GraphTrue A (G i)) → I.Satisfies E := by
  constructor
  · exact fun h U I A hA => h U I ((I.satisfies_iUnion G).mpr ⟨A, hA⟩)
  · intro h U I hG
    obtain ⟨A, hA⟩ := (I.satisfies_iUnion G).mp hG
    exact h U I A hA

theorem merge_entailsUnder_iff
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    (G : (i : K) → GeneralizedGraph Iri Literal (Bs i))
    (E : GeneralizedGraph Iri Literal B) :
    EntailsUnder C (merge G) E ↔
      ∀ U I, C U I → (∀ i, I.Satisfies (G i)) → I.Satisfies E := by
  exact ⟨fun h U I hc hG => h U I hc ((satisfies_merge I G).mpr hG),
    fun h U I hc hG => h U I hc ((satisfies_merge I G).mp hG)⟩

theorem satisfies_mergeSet (I : SimpleInterpretation Iri Literal U)
    (S : Set (GeneralizedGraph Iri Literal B)) :
    I.Satisfies (mergeSet S) ↔ ∀ G, S G → I.Satisfies G := by
  rw [mergeSet, satisfies_merge]
  exact ⟨fun h G hG => h ⟨G, hG⟩, fun h G => h G.val G.property⟩

theorem satisfies_unionSet (I : SimpleInterpretation Iri Literal U)
    (S : Set (GeneralizedGraph Iri Literal B)) :
    I.Satisfies (unionSet S) ↔ ∃ A, ∀ G, S G → I.GraphTrue A G := by
  rw [unionSet, I.satisfies_iUnion]
  exact exists_congr fun A => ⟨fun h G hG => h ⟨G, hG⟩, fun h G => h G.val G.property⟩

/-- Repeating input occurrences changes copies but not the merged truth condition. -/
theorem reindex_merge_satisfaction (I : SimpleInterpretation Iri Literal U)
    (G : (i : K) → GeneralizedGraph Iri Literal (Bs i))
    (f : J → K) (hf : ∀ i, ∃ j, f j = i) :
    I.Satisfies (merge (fun j => G (f j))) ↔ I.Satisfies (merge G) := by
  rw [satisfies_merge, satisfies_merge]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := hf i
    exact h j
  · exact fun h j => h (f j)

theorem merge_empty {Bs' : Empty → Type}
    (G : (i : Empty) → GeneralizedGraph Iri Literal (Bs' i)) :
    merge G = Set.empty := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨i, _⟩
    exact nomatch i
  · exact False.elim

theorem merge_constant_satisfaction (I : SimpleInterpretation Iri Literal U)
    (G : GeneralizedGraph Iri Literal B) (i : K) :
    I.Satisfies (merge (fun _ : K => G)) ↔ I.Satisfies G := by
  rw [satisfies_merge]
  exact ⟨fun h => h i, fun h _ => h⟩

theorem entails_merge_iff (G : (i : K) → GeneralizedGraph Iri Literal (Bs i))
    (H : GeneralizedGraph Iri Literal B) :
    SimplyEntails.{u} H (merge G) ↔ ∀ i, SimplyEntails.{u} H (G i) := by
  exact ⟨fun h i U I hH => (satisfies_merge I G).mp (h U I hH) i,
    fun h U I hH => (satisfies_merge I G).mpr fun i => h i U I hH⟩

end GraphFamily
end RDF11
