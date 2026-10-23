/-
Engineering refinement, not a replacement for W3C's set-valued graph.
A finite enumeration carries proofs of membership fidelity AND uniqueness.
-/
import RDF11.Syntax

namespace RDF11

structure Enumeration (G : Set α) where
  triples : List α
  nodup : triples.Nodup
  membership : ∀ t, t ∈ triples ↔ G t

namespace Enumeration

def unique [DecidableEq α] : List α → List α
  | [] => []
  | t :: ts =>
    let rest := unique ts
    if t ∈ rest then rest else t :: rest

@[simp] theorem mem_unique [DecidableEq α] (xs : List α) (t : α) :
    t ∈ unique xs ↔ t ∈ xs := by
  induction xs generalizing t with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique]
    split
    · rename_i h
      have hx : x ∈ xs := (ih x).mp h
      simp only [ih t, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun he => he ▸ hx) id⟩
    · simp [List.mem_cons, ih]

theorem unique_nodup [DecidableEq α] (xs : List α) : (unique xs).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    simp only [unique]
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.mpr ⟨h, ih⟩

def fromList [DecidableEq α] (xs : List α) : Enumeration (Set.ofList xs) where
  triples := unique xs
  nodup := unique_nodup xs
  membership := mem_unique xs

theorem count_le_one [BEq α] [LawfulBEq α] (e : Enumeration G) (t : α) :
    e.triples.count t ≤ 1 :=
  List.nodup_iff_count.mp e.nodup t

theorem length_independent (e f : Enumeration G) : e.triples.length = f.triples.length := by
  apply Nat.le_antisymm
  · apply e.nodup.length_le_of_subset
    intro t ht
    exact (f.membership t).mpr ((e.membership t).mp ht)
  · apply f.nodup.length_le_of_subset
    intro t ht
    exact (e.membership t).mpr ((f.membership t).mp ht)

theorem repeated_input_same_set (t : α) : Set.ofList [t, t] = Set.ofList [t] :=
  Set.ofList_repeat t

/-- A set containing an injective natural-number family has no finite enumeration. -/
theorem no_enumeration_of_nat_injection (G : Set α) (f : Nat → α)
    (hmem : ∀ n, G (f n)) (hinj : ∀ m n, f m = f n → m = n) :
    ¬ Nonempty (Enumeration G) := by
  rintro ⟨e⟩
  have hn : ((List.range (e.triples.length + 1)).map f).Nodup :=
    List.Pairwise.map f (fun m n hne he => hne (hinj m n he)) List.nodup_range
  have hs : ((List.range (e.triples.length + 1)).map f) ⊆ e.triples := by
    intro a ha
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp ha
    exact (e.membership _).mpr (hmem n)
  have hl := hn.length_le_of_subset hs
  simp only [List.length_map, List.length_range] at hl
  exact (Nat.not_succ_le_self _) hl

end Enumeration
end RDF11

