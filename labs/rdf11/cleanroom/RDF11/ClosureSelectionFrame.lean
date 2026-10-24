/-
Proof-support abstraction for the Appendix A container-selection question.
This relation is closed under the listed rules and excludes generic membership.
It is NOT an RDFS interpretation: it deliberately need not satisfy omitted
container axioms or the datatype truth conditions. Full-model consistency is
proved separately. No computation here replaces a kernel-checked proof.
-/
import RDF11.EntailmentClosure

namespace RDF11.ClosureSelection

inductive Tag where
  | top | cmp | typing | subclass | subproperty | member | domainRange
  | free | selected | user | invalid
  deriving DecidableEq

def holds (s p o : Tag) : Prop :=
  match p with
  | .typing => s ≠ .invalid ∧ (o = .top ∨ (s = .selected ∧ o = .cmp))
  | .subclass => s ≠ .invalid ∧ o ≠ .invalid ∧ (o = .top ∨ s = o)
  | .subproperty => s ≠ .invalid ∧ o ≠ .invalid ∧ (s = o ∨ (s = .selected ∧ o = .member))
  | .domainRange => s ≠ .invalid ∧ o = .top
  | .free => s = .user ∧ o = .user
  | _ => False

theorem subject_valid {s p o : Tag} (h : holds s p o) : s ≠ .invalid := by
  cases p <;> cases s <;> simp_all [holds]

theorem object_valid {s p o : Tag} (h : holds s p o) : o ≠ .invalid := by
  cases p <;> cases o <;> simp_all [holds]

theorem predicate_valid {s p o : Tag} (h : holds s p o) : p ≠ .invalid := by
  cases p <;> simp_all [holds]

theorem type_top {s : Tag} (h : s ≠ .invalid) : holds s .typing .top :=
  ⟨h, Or.inl rfl⟩

theorem domain_closed {p c s o : Tag} (hd : holds p .domainRange c) (ht : holds s p o) :
    holds s .typing c := by
  have hc : c = .top := hd.2
  subst c
  exact type_top (subject_valid ht)

theorem range_closed {p c s o : Tag} (hd : holds p .domainRange c) (ht : holds s p o) :
    holds o .typing c := by
  have hc : c = .top := hd.2
  subst c
  exact type_top (object_valid ht)

theorem subproperty_trans {p q r : Tag} (hpq : holds p .subproperty q)
    (hqr : holds q .subproperty r) : holds p .subproperty r := by
  refine ⟨hpq.1, hqr.2.1, ?_⟩
  rcases hpq.2.2 with rfl | ⟨rfl, rfl⟩
  · exact hqr.2.2
  · rcases hqr.2.2 with rfl | ⟨h, _⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · cases h

theorem subproperty_refl {p : Tag} (hp : p ≠ .invalid) : holds p .subproperty p :=
  ⟨hp, hp, Or.inl rfl⟩

theorem subproperty_use {p q s o : Tag} (hpq : holds p .subproperty q)
    (ht : holds s p o) : holds s q o := by
  rcases hpq.2.2 with rfl | ⟨rfl, rfl⟩
  · exact ht
  · exact False.elim ht

theorem subclass_top {c : Tag} (hc : c ≠ .invalid) : holds c .subclass .top :=
  ⟨hc, by decide, Or.inl rfl⟩

theorem subclass_refl {c : Tag} (hc : c ≠ .invalid) : holds c .subclass c :=
  ⟨hc, hc, Or.inr rfl⟩

theorem subclass_use {c d x : Tag} (hcd : holds c .subclass d)
    (hx : holds x .typing c) : holds x .typing d := by
  rcases hcd.2.2 with rfl | rfl
  · exact type_top (subject_valid hx)
  · exact hx

theorem subclass_trans {c d e : Tag} (hcd : holds c .subclass d)
    (hde : holds d .subclass e) : holds c .subclass e := by
  refine ⟨hcd.1, hde.2.1, ?_⟩
  rcases hde.2.2 with rfl | rfl
  · exact Or.inl rfl
  · exact hcd.2.2

theorem container_subproperty {p : Tag} (hp : holds p .typing .cmp) :
    holds p .subproperty .member := by
  rcases hp.2 with h | ⟨rfl, _⟩
  · cases h
  · exact ⟨by decide, by decide, Or.inr ⟨rfl, rfl⟩⟩

end RDF11.ClosureSelection
