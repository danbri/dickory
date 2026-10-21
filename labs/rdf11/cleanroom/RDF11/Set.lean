/-
FOUNDATION-SET: extensional sets, possibly infinite.
This project uses only Lean's standard distribution. No Factoidal imports.
-/
import Std

namespace RDF11

abbrev Set (α : Type u) := α → Prop

namespace Set

def empty : Set α := fun _ => False
def singleton (a : α) : Set α := fun b => b = a
def union (s t : Set α) : Set α := fun a => s a ∨ t a
def subset (s t : Set α) : Prop := ∀ a, s a → t a
def image (f : α → β) (s : Set α) : Set β := fun b => ∃ a, s a ∧ f a = b
def ofList (xs : List α) : Set α := fun a => a ∈ xs

@[ext] theorem ext {s t : Set α} (h : ∀ a, s a ↔ t a) : s = t := by
  funext a
  exact propext (h a)

theorem union_idempotent (s : Set α) : union s s = s := by
  apply ext
  intro a
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem union_comm (s t : Set α) : union s t = union t s := by
  apply ext
  intro a
  exact or_comm

theorem union_assoc (s t u : Set α) : union (union s t) u = union s (union t u) := by
  apply ext
  intro a
  exact or_assoc

theorem subset_refl (s : Set α) : subset s s := fun _ h => h

theorem subset_trans {s t u : Set α} (hst : subset s t) (htu : subset t u) :
    subset s u := fun a h => htu a (hst a h)

theorem ofList_repeat (a : α) : ofList [a, a] = ofList [a] := by
  apply ext
  intro b
  simp [ofList]

end Set
end RDF11
