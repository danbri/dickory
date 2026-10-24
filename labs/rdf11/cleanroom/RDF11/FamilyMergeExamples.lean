/-
Checked scope witnesses for arbitrary-family union and merge.
The existing shared-blank countermodel is reused. The infinite example has
distinct syntactic blanks but permits every one to denote the same resource.
-/
import RDF11.MergeInstances
import RDF11.ScopeExample
import RDF11.Enumeration

namespace RDF11.FamilyMergeExamples

open ScopeExample

theorem shared_union_eq :
    Set.iUnion graph = Set.union (graph false) (graph true) := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

theorem shared_union_false : ¬ I.Satisfies (Set.iUnion graph) := by
  rw [shared_union_eq]
  exact union_not_satisfied

theorem shared_merge_true : I.Satisfies (GraphFamily.merge graph) :=
  (GraphFamily.satisfies_merge I graph).mpr each_satisfiable

theorem shared_merge_not_entails_union :
    ¬ SimplyEntails.{0} (GraphFamily.merge graph) (Set.iUnion graph) :=
  fun h => shared_union_false (h Bool I shared_merge_true)

def graphSet : Set (GeneralizedGraph Bool Empty Unit) :=
  fun G => G = graph false ∨ G = graph true

theorem set_merge_true : I.Satisfies (GraphFamily.mergeSet graphSet) := by
  apply (GraphFamily.satisfies_mergeSet I graphSet).mpr
  intro G hG
  rcases hG with rfl | rfl
  · exact each_satisfiable false
  · exact each_satisfiable true

theorem set_union_eq : GraphFamily.unionSet graphSet = Set.iUnion graph := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨⟨G, hG⟩, ht⟩
    rcases hG with rfl | rfl
    · exact ⟨false, ht⟩
    · exact ⟨true, ht⟩
  · rintro ⟨i, hi⟩
    cases i with
    | false => exact ⟨⟨graph false, Or.inl rfl⟩, hi⟩
    | true => exact ⟨⟨graph true, Or.inr rfl⟩, hi⟩

theorem set_union_false : ¬ I.Satisfies (GraphFamily.unionSet graphSet) := by
  rw [set_union_eq]
  exact shared_union_false

def independent (n : Nat) : GeneralizedGraph Bool Empty Nat :=
  Set.singleton ⟨.blank n, .iri true, .iri false⟩

theorem independent_apart : GraphFamily.Apart independent := by
  intro i j b hi hj
  obtain ⟨ti, hti, hbi⟩ := hi
  obtain ⟨tj, htj, hbj⟩ := hj
  have hei : ti = ⟨.blank i, .iri true, .iri false⟩ := hti
  have hej : tj = ⟨.blank j, .iri true, .iri false⟩ := htj
  subst ti
  subst tj
  have hi : i = b := by simpa [GeneralizedTriple.hasBlank, Term.hasBlank] using hbi
  have hj : j = b := by simpa [GeneralizedTriple.hasBlank, Term.hasBlank] using hbj
  exact hi.trans hj.symm

/-- Infinitely many different identities may all receive one resource value. -/
theorem independent_common_witness :
    I.GraphTrue (fun _ => some ⟨true, True.intro⟩) (Set.iUnion independent) := by
  rintro t ⟨n, ht⟩
  have he : t = ⟨.blank n, .iri true, .iri false⟩ := ht
  subst t
  exact ⟨⟨true, True.intro⟩, ⟨true, True.intro⟩, ⟨false, True.intro⟩,
    rfl, rfl, rfl, rfl⟩

theorem infinite_union_true : I.Satisfies (Set.iUnion independent) :=
  (I.satisfies_iff_exists_graphTrue _).mpr ⟨_, independent_common_witness⟩

theorem infinite_merge_true : I.Satisfies (GraphFamily.merge independent) :=
  GraphFamily.union_entails_merge independent Bool I infinite_union_true

noncomputable def infinite_isomorphism :
    GraphIsomorphism (GraphFamily.scopedMerge independent) (GraphFamily.scopedUnion independent) :=
  GraphFamily.apart_isomorphism independent independent_apart

/-- Two distinct subgraphs: the smaller shares its triple and blank with the larger. -/
def nested : Bool → GeneralizedGraph Bool Empty Unit
  | false => Set.ofList [triple false]
  | true => Set.ofList [triple false, triple true]

def nested_union_enumeration : Enumeration (Set.iUnion nested) where
  triples := [triple false, triple true]
  nodup := by decide
  membership := by
    intro t
    simp [Set.iUnion, nested, Set.ofList]

def nested_merge_enumeration : Enumeration (GraphFamily.merge nested) where
  triples := [(triple false).mapBlank (Sigma.mk false),
    (triple false).mapBlank (Sigma.mk true), (triple true).mapBlank (Sigma.mk true)]
  nodup := by decide
  membership := by
    intro t
    constructor
    · intro ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨false, triple false, by simp [nested, Set.ofList], rfl⟩
      · exact ⟨true, triple false, by simp [nested, Set.ofList], rfl⟩
      · exact ⟨true, triple true, by simp [nested, Set.ofList], rfl⟩
    · rintro ⟨i, s, hs, rfl⟩
      cases i <;> simp [nested, Set.ofList] at hs
      · subst s
        simp
      · rcases hs with rfl | rfl <;> simp

/-- Counts are independent of the chosen duplicate-free enumerations. -/
theorem merging_subgraphs_can_increase_size
    (u : Enumeration (Set.iUnion nested)) (m : Enumeration (GraphFamily.merge nested)) :
    u.triples.length = 2 ∧ m.triples.length = 3 :=
  ⟨Enumeration.length_independent u nested_union_enumeration,
    Enumeration.length_independent m nested_merge_enumeration⟩

end RDF11.FamilyMergeExamples
