/-
The §5 technical note concerns the full name-mapping structure, not IR's
cardinality. Infinite abstract vocabulary and collapsed denotations coexist.
Concrete legal IRI spellings remain a separate correspondence obligation.
-/
import RDF11.RDF
import RDF11.Enumeration

namespace RDF11

/-- The infinite indexed vocabulary supplies distinct abstract IRI names. -/
theorem RDFVocabulary.container_injective (v : RDFVocabulary Iri) (m n : Nat)
    (h : v.iri (.container m) = v.iri (.container n)) : m = n :=
  RDFSymbol.container.inj (v.distinct _ _ h)

namespace SimpleInterpretation

/-- The set-theoretic graph of IS, distinct from an RDF graph. -/
def ISGraph (I : SimpleInterpretation Iri Literal U) : Set (Iri × U) :=
  fun pair => pair.2 = (I.IS pair.1).val

theorem ISGraph_not_finite (I : SimpleInterpretation Iri Literal U)
    (ι : Nat → Iri) (hinj : ∀ m n, ι m = ι n → m = n) :
    ¬ Nonempty (Enumeration I.ISGraph) := by
  apply Enumeration.no_enumeration_of_nat_injection I.ISGraph (fun n => (ι n, (I.IS (ι n)).val))
  · intro n; rfl
  · intro m n he
    exact hinj m n (congrArg Prod.fst he)

theorem vocabulary_ISGraph_not_finite (I : SimpleInterpretation Iri Literal U)
    (v : RDFVocabulary Iri) : ¬ Nonempty (Enumeration I.ISGraph) :=
  I.ISGraph_not_finite (fun n => v.iri (.container n)) v.container_injective

end SimpleInterpretation

/-- A full-domain simple interpretation can have one resource and an infinite
IS graph. This is not a finite-vocabulary pre-interpretation. -/
theorem one_resource_infinite_name_mapping (v : RDFVocabulary Iri) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      Nonempty (Enumeration I.IR) ∧ ¬ Nonempty (Enumeration I.ISGraph) ∧
      ∃ r, ∀ x, I.IR x → x = r := by
  let I : SimpleInterpretation Iri Literal (ULift.{u} Unit) := indiscriminate
  have e : Enumeration I.IR := {
    triples := [⟨()⟩]
    nodup := by simp
    membership := by
      intro x
      have hx : x = (⟨()⟩ : ULift.{u} Unit) := Subsingleton.elim _ _
      simp [hx, I, indiscriminate]
  }
  exact ⟨ULift.{u} Unit, I, ⟨e⟩, I.vocabulary_ISGraph_not_finite v,
    ⟨⟨()⟩, fun _ _ => Subsingleton.elim _ _⟩⟩

end RDF11
