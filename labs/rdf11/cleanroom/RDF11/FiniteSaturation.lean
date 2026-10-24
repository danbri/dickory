/-
Executable finite saturation support for Appendix A. Each nonterminal round
adds a fact; a fixed finite carrier therefore bounds the number of rounds.
The bound counts rounds, not machine time or term-comparison cost.
-/
import RDF11.Enumeration
import RDF11.EntailmentClosure

namespace RDF11.FiniteSaturation

variable {α : Type u} [DecidableEq α]

def decision (S : Set α) (e : Enumeration S) (a : α) : Decidable (S a) :=
  if h : a ∈ e.triples then isTrue ((e.membership a).mp h)
  else isFalse (fun ha => h ((e.membership a).mpr ha))

def stable (next : List α → List α) (xs : List α) : Bool :=
  (next xs).all (fun a => decide (a ∈ xs))

theorem stable_iff (next : List α → List α) (xs : List α) :
    stable next xs = true ↔ next xs ⊆ xs := by
  simp [stable, List.subset_def]

def advance (next : List α → List α) (xs : List α) : List α :=
  Enumeration.unique (xs ++ next xs)

theorem mem_advance (next : List α → List α) (xs : List α) (a : α) :
    a ∈ advance next xs ↔ a ∈ xs ∨ a ∈ next xs := by
  simp [advance]

theorem advance_nodup (next : List α → List α) (xs : List α) :
    (advance next xs).Nodup := Enumeration.unique_nodup _

theorem subset_advance (next : List α → List α) (xs : List α) : xs ⊆ advance next xs :=
  fun a ha => (mem_advance next xs a).mpr (Or.inl ha)

theorem advance_subset (next : List α → List α) (xs carrier : List α)
    (hx : xs ⊆ carrier) (hn : next xs ⊆ carrier) : advance next xs ⊆ carrier := by
  intro a ha
  exact ((mem_advance next xs a).mp ha).elim (hx ·) (hn ·)

theorem advance_grows (next : List α → List α) (xs : List α) (hx : xs.Nodup)
    (hn : stable next xs ≠ true) : xs.length < (advance next xs).length := by
  classical
  have witness : ∃ a, a ∈ next xs ∧ a ∉ xs := by
    apply Classical.byContradiction
    intro h
    apply hn
    apply (stable_iff next xs).mpr
    intro a ha
    exact Classical.byContradiction (fun hna => h ⟨a, ha, hna⟩)
  obtain ⟨a, ha, hna⟩ := witness
  have hd : (a :: xs).Nodup := List.nodup_cons.mpr ⟨hna, hx⟩
  have hs : a :: xs ⊆ advance next xs := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (mem_advance next xs _).mpr (Or.inr ha)
    · exact subset_advance next xs hb
  exact hd.length_le_of_subset hs

def run (next : List α → List α) (fuel : Nat) : List α → List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun xs => xs)
    (fun _ previous xs => if stable next xs then xs else previous (advance next xs)) fuel

theorem run_nodup (next : List α → List α) (fuel : Nat) (xs : List α) (hx : xs.Nodup) :
    (run next fuel xs).Nodup := by
  induction fuel generalizing xs with
  | zero => exact hx
  | succ fuel ih =>
    simp only [run]
    split
    · exact hx
    · exact ih _ (advance_nodup next xs)

theorem subset_run (next : List α → List α) (fuel : Nat) (xs : List α) :
    xs ⊆ run next fuel xs := by
  induction fuel generalizing xs with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
    simp only [run]
    split
    · exact List.Subset.refl _
    · exact List.Subset.trans (subset_advance next xs) (ih _)

theorem run_preserves (next : List α → List α) (P : Set α)
    (hn : ∀ xs, (∀ a ∈ xs, P a) → ∀ a ∈ next xs, P a)
    (fuel : Nat) (xs : List α) (hx : ∀ a ∈ xs, P a) :
    ∀ a ∈ run next fuel xs, P a := by
  induction fuel generalizing xs with
  | zero => exact hx
  | succ fuel ih =>
    simp only [run]
    split
    · exact hx
    · apply ih
      intro a ha
      exact ((mem_advance next xs a).mp ha).elim (hx a) (hn xs hx a)

theorem run_subset (next : List α → List α) (carrier : List α)
    (hn : ∀ xs, xs ⊆ carrier → next xs ⊆ carrier)
    (fuel : Nat) (xs : List α) (hx : xs ⊆ carrier) :
    run next fuel xs ⊆ carrier :=
  run_preserves next (Set.ofList carrier) hn fuel xs hx

theorem run_stable (next : List α → List α) (carrier : List α)
    (hn : ∀ xs, xs ⊆ carrier → next xs ⊆ carrier)
    (fuel : Nat) (xs : List α) (hx : xs.Nodup) (hu : xs ⊆ carrier)
    (enough : carrier.length ≤ xs.length + fuel) : stable next (run next fuel xs) = true := by
  induction fuel generalizing xs with
  | zero =>
    change stable next xs = true
    apply Classical.byContradiction
    intro h
    have grows := advance_grows next xs hx h
    have bound := (advance_nodup next xs).length_le_of_subset (advance_subset next xs carrier hu (hn xs hu))
    omega
  | succ fuel ih =>
    simp only [run]
    split
    · assumption
    · rename_i h
      apply ih _ (advance_nodup next xs) (advance_subset next xs carrier hu (hn xs hu))
      have grows := advance_grows next xs hx h
      omega

theorem run_length (next : List α → List α) (carrier : List α)
    (hn : ∀ xs, xs ⊆ carrier → next xs ⊆ carrier)
    (fuel : Nat) (xs : List α) (hx : xs.Nodup) (hu : xs ⊆ carrier) :
    (run next fuel xs).length ≤ carrier.length :=
  (run_nodup next fuel xs hx).length_le_of_subset (run_subset next carrier hn fuel xs hu)

section Rules
variable [DecidableEq Iri] [DecidableEq Literal] [DecidableEq B]

theorem run_exact
    (step : GeneralizedGraph Iri Literal B → GeneralizedTriple Iri Literal B → Prop)
    (next : List (GeneralizedTriple Iri Literal B) → List (GeneralizedTriple Iri Literal B))
    (hnext : ∀ xs t, t ∈ next xs ↔ step (Set.ofList xs) t)
    (hmono : ∀ G H, Set.subset G H → ∀ t, step G t → step H t)
    (carrier : List (GeneralizedTriple Iri Literal B))
    (hbound : ∀ xs, xs ⊆ carrier → next xs ⊆ carrier)
    (fuel : Nat) (seed : List (GeneralizedTriple Iri Literal B))
    (hs : seed.Nodup) (hc : seed ⊆ carrier) (enough : carrier.length ≤ seed.length + fuel) :
    Set.ofList (run next fuel seed) = RuleDerives step (Set.ofList seed) := by
  apply Set.ext
  intro t
  constructor
  · exact run_preserves next (RuleDerives step (Set.ofList seed))
      (fun xs hx t ht => .rule (Set.ofList xs) hx ((hnext xs t).mp ht)) fuel seed
      (fun _ h => .premise h) t
  · apply ruleDerives_least step (Set.ofList seed) (Set.ofList (run next fuel seed))
    · exact subset_run next fuel seed
    · intro H q hH hq
      have hq' := hmono H _ hH q hq
      exact (stable_iff next _).mp (run_stable next carrier hbound fuel seed hs hc enough)
        ((hnext _ q).mpr hq')

end Rules

end RDF11.FiniteSaturation
