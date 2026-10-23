/-
Derived source-review witness, not an example printed in the specification.
An infinite ordinary graph can be a proper instance of itself. This graph
is NOT lean, so it is not a counterexample to the §5.3 consequence.
-/
import RDF11.FiniteInstances

namespace RDF11.InfiniteProperInstance

def triple (p o : Iri) (n : Nat) : Triple Iri Literal Nat :=
  ⟨.blank n, p, .iri o⟩

def graph (p o : Iri) : Graph Iri Literal Nat :=
  fun t => ∃ n, t = triple p o n

theorem hasBlank (p o : Iri) (n : Nat) :
    (graph (Literal := Literal) p o).generalize.hasBlank n :=
  ⟨(triple p o n).generalize, ⟨triple p o n, ⟨n, rfl⟩, rfl⟩, Or.inl rfl⟩

/-- Pair adjacent blank identities: 0 and 1 collide, but every index is hit. -/
def fold : Substitution Iri Literal Nat := fun n => some (.blank (n / 2))

theorem fold_triple (p o : Iri) (n : Nat) :
    ((triple (Literal := Literal) p o n).generalize).substitute fold =
      (triple p o (n / 2)).generalize := rfl

theorem fold_image (p o : Iri) :
    (graph (Literal := Literal) p o).generalize.substitute fold = (graph p o).generalize := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
    exact ⟨triple p o (n / 2), ⟨n / 2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨(triple p o (2 * n)).generalize, ⟨triple p o (2 * n), ⟨2 * n, rfl⟩, rfl⟩, ?_⟩
    rw [fold_triple]
    have hn : 2 * n / 2 = n := by omega
    rw [hn]

theorem fold_proper (p o : Iri) :
    ProperSubstitution (graph (Literal := Literal) p o).generalize fold :=
  Or.inr ⟨0, 1, hasBlank p o 0, hasBlank p o 1, Nat.zero_ne_one, rfl⟩

theorem proper_self_instance (p o : Iri) :
    ProperInstance (graph (Literal := Literal) p o).generalize (graph p o).generalize :=
  ⟨fold, (fold_image p o).symm, fold_proper p o⟩

theorem infinite_blank_support (p o : Iri) :
    ¬ FiniteBlankSupport (graph (Literal := Literal) p o).generalize :=
  Enumeration.no_enumeration_of_nat_injection _ id (hasBlank p o) (fun _ _ h => h)

theorem infinite_graph (p o : Iri) :
    ¬ FiniteGraph (graph (Literal := Literal) p o).generalize :=
  fun h => infinite_blank_support p o (finite_blank_support_of_finite_graph _ h)

/-- Collapsing all blanks to 0 exhibits a proper subgraph instance. -/
theorem not_lean (p o : Iri) : ¬ LeanGraph (graph (Literal := Literal) p o).generalize := by
  intro hl
  let μ : Substitution Iri Literal Nat := fun _ => some (.blank 0)
  have hs : Set.subset ((graph p o).generalize.substitute μ) (graph p o).generalize := by
    rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
    exact ⟨triple p o 0, ⟨0, rfl⟩, rfl⟩
  have he := hl _ ⟨μ, rfl⟩ hs
  have h1 : (graph (Literal := Literal) p o).generalize ((triple p o 1).generalize) :=
    ⟨triple p o 1, ⟨1, rfl⟩, rfl⟩
  rw [← he] at h1
  obtain ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, ht⟩ := h1
  have hx : (Term.blank 0 : Term Iri Literal Nat) = .blank 1 :=
    congrArg GeneralizedTriple.subject ht
  exact Nat.zero_ne_one (Term.blank.inj hx)

end RDF11.InfiniteProperInstance
