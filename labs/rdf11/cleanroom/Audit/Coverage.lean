/-
Spec2Lean structural accountability only, not a proof of extraction fidelity.
Scalar offsets refer to separately hashed, strictly decoded source snapshots.
-/
import Std

namespace Spec2Lean

structure Atom where
  start : Nat
  stop : Nat
  refs : List String
  deriving DecidableEq, Repr

def Contains (a : Atom) (i : Nat) : Prop := a.start ≤ i ∧ i < a.stop

def ValidPartition (ids : List String) (limit start : Nat) (atoms : List Atom) : Prop :=
  match atoms with
  | [] => start = limit
  | a :: rest =>
    a.start = start ∧ a.start < a.stop ∧ a.refs ≠ [] ∧
    (∀ r ∈ a.refs, r ∈ ids) ∧ ValidPartition ids limit a.stop rest
termination_by structural atoms

def partitionDecidable (ids : List String) (limit start : Nat) (atoms : List Atom) :
    Decidable (ValidPartition ids limit start atoms) :=
  match atoms with
  | [] => inferInstanceAs (Decidable (start = limit))
  | a :: rest =>
    letI := partitionDecidable ids limit a.stop rest
    inferInstanceAs (Decidable
      (a.start = start ∧ a.start < a.stop ∧ a.refs ≠ [] ∧
        (∀ r ∈ a.refs, r ∈ ids) ∧ ValidPartition ids limit a.stop rest))
termination_by structural atoms

instance (ids : List String) (limit start : Nat) (atoms : List Atom) :
    Decidable (ValidPartition ids limit start atoms) := partitionDecidable ids limit start atoms

theorem member_starts_after {ids : List String} {limit start : Nat} {atoms : List Atom}
    (h : ValidPartition ids limit start atoms) {a : Atom} (ha : a ∈ atoms) :
    start ≤ a.start := by
  induction atoms generalizing start with
  | nil => simp at ha
  | cons b rest ih =>
    obtain ⟨hb, hlt, _, _, ht⟩ := h
    rcases List.mem_cons.mp ha with he | he
    · subst a
      omega
    · have hr := ih ht he
      omega

theorem partition_sound {ids : List String} {limit start : Nat} {atoms : List Atom}
    (h : ValidPartition ids limit start atoms) (i : Nat) (hi : start ≤ i ∧ i < limit) :
    ∃ a, a ∈ atoms ∧ Contains a i ∧
      ∀ b, b ∈ atoms → Contains b i → b = a := by
  induction atoms generalizing start with
  | nil =>
    simp only [ValidPartition] at h
    omega
  | cons a rest ih =>
    obtain ⟨ha, hlt, _, _, ht⟩ := h
    by_cases hia : i < a.stop
    · refine ⟨a, List.mem_cons_self, ⟨?_, hia⟩, ?_⟩
      · omega
      · intro b hb hbi
        rcases List.mem_cons.mp hb with he | he
        · exact he
        · have hstart := member_starts_after ht he
          have := hbi.1
          omega
    · have hit : a.stop ≤ i ∧ i < limit := by omega
      obtain ⟨b, hb, hbi, huniq⟩ := ih ht hit
      refine ⟨b, List.mem_cons_of_mem a hb, hbi, ?_⟩
      intro c hc hci
      rcases List.mem_cons.mp hc with he | he
      · subst c
        exact False.elim (hia hci.2)
      · exact huniq c he hci

theorem references_grounded {ids : List String} {limit start : Nat} {atoms : List Atom}
    (h : ValidPartition ids limit start atoms) {a : Atom} (ha : a ∈ atoms) :
    a.refs ≠ [] ∧ ∀ r ∈ a.refs, r ∈ ids := by
  induction atoms generalizing start with
  | nil => simp at ha
  | cons b rest ih =>
    obtain ⟨_, _, href, hvalid, ht⟩ := h
    rcases List.mem_cons.mp ha with he | he
    · subst a
      exact ⟨href, hvalid⟩
    · exact ih ht he

end Spec2Lean

