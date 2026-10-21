/-
A formal counterexample illustrating Semantics §5.1.1 (informative).
Each singleton graph has a witness; their union has no common witness.
This is proof evidence for a phenomenon, not a complete entailment procedure.
-/
import RDF11.Merge

namespace RDF11.ScopeExample

def I : SimpleInterpretation Bool Empty Bool where
  IR := fun _ => True
  IR_nonempty := ⟨false, True.intro⟩
  IP := fun _ => True
  IEXT := fun p pair => pair.1.val = p.val
  IS := fun i => ⟨i, Or.inl True.intro⟩
  IL := fun l => nomatch l

def triple (v : Bool) : GeneralizedTriple Bool Empty Unit :=
  ⟨.blank (), .iri v, .iri false⟩

def graph (v : Bool) : GeneralizedGraph Bool Empty Unit := Set.singleton (triple v)

theorem each_satisfiable (v : Bool) : I.Satisfies (graph v) := by
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => some ⟨v, True.intro⟩, ?_⟩
  intro t ht
  have he : t = triple v := ht
  subst t
  exact ⟨⟨v, True.intro⟩, ⟨v, True.intro⟩, ⟨false, True.intro⟩,
    rfl, rfl, rfl, rfl⟩

theorem witness_forced (A : I.Assignment Unit) (v : Bool)
    (h : I.TripleTrue A (triple v)) : (A ()).map Subtype.val = some v := by
  obtain ⟨p, s, o, hp, hs, ho, he⟩ := h
  have hpv : v = p.val := Option.some.inj hp
  have hsv : s.val = p.val := he
  exact hs.trans (congrArg some (hsv.trans hpv.symm))

theorem union_not_satisfied : ¬ I.Satisfies (Set.union (graph false) (graph true)) := by
  intro h
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp h
  have hf := witness_forced A false (hA _ (Or.inl rfl))
  have ht := witness_forced A true (hA _ (Or.inr rfl))
  have he : (some false : Option Bool) = some true := hf.symm.trans ht
  cases he

theorem merge_satisfied : I.Satisfies (merge (graph false) (graph true)) :=
  (satisfies_merge I _ _).mpr ⟨each_satisfiable false, each_satisfiable true⟩

theorem merge_does_not_entail_union :
    ¬ SimplyEntails.{0} (merge (graph false) (graph true))
      (Set.union (graph false) (graph true)) :=
  fun h => union_not_satisfied (h Bool I merge_satisfied)

end RDF11.ScopeExample

