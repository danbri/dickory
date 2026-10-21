/-
Review question: the generalized-syntax extension of the instance consequence.
This is NOT asserted as a W3C erratum. It checks a scope issue against the
literal §5 domains, without silently adding IP ⊆ IR.

For any two distinct IRIs s and p, s denotes the sole resource false and
p denotes the separate property true. The ground triple s p s is true.
Replacing p by an existential blank node requires a resource denotation,
so the generalized graph is false. All other IRIs/literals are interpreted.
-/
import RDF11.Entailment

namespace RDF11.GeneralizedScope

def I [DecidableEq Iri] (p : Iri) : SimpleInterpretation Iri Literal Bool where
  IR := fun x => x = false
  IR_nonempty := ⟨false, rfl⟩
  IP := fun x => x = true
  IEXT := fun _ _ => True
  IS := fun i => if i = p then ⟨true, Or.inr rfl⟩ else ⟨false, Or.inl rfl⟩
  IL := fun _ => none

def originalTriple (s : Iri) : GeneralizedTriple Iri Literal Unit :=
  ⟨.iri s, .blank (), .iri s⟩

/-- The result of substituting the IRI p for the sole blank node. -/
def substitutedTriple (s p : Iri) : GeneralizedTriple Iri Literal Unit :=
  ⟨.iri s, .iri p, .iri s⟩

def original (s : Iri) : GeneralizedGraph Iri Literal Unit := Set.singleton (originalTriple s)
def substituted (s p : Iri) : GeneralizedGraph Iri Literal Unit :=
  Set.singleton (substitutedTriple s p)

theorem substituted_true [DecidableEq Iri] (s p : Iri) (hsp : s ≠ p) :
    (I (Literal := Literal) p).Satisfies (substituted s p) := by
  apply ((I p).satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  intro t ht
  have he : t = substitutedTriple s p := ht
  subst t
  refine ⟨⟨true, rfl⟩, ⟨false, rfl⟩, ⟨false, rfl⟩, ?_, ?_, ?_, True.intro⟩
  all_goals simp [SimpleInterpretation.denote, substitutedTriple, I, hsp]

theorem original_false [DecidableEq Iri] (s p : Iri) :
    ¬ (I (Literal := Literal) p).Satisfies (original s) := by
  rintro ⟨A, _, h⟩
  obtain ⟨q, _, _, hp, _, _, _⟩ := h (originalTriple s) rfl
  cases hA : A () with
  | none => simp [SimpleInterpretation.denote, originalTriple, hA] at hp
  | some r =>
    have he : r.val = q.val := by
      simpa [SimpleInterpretation.denote, originalTriple, hA] using hp
    have hr : r.val = false := r.property
    have hpv : q.val = true := q.property
    have hf : false = true := hr.symm.trans (he.trans hpv)
    cases hf

theorem unrestricted_generalized_instance_consequence_fails
    [DecidableEq Iri] (s p : Iri) (hsp : s ≠ p) :
    ¬ SimplyEntails.{0} (Literal := Literal) (substituted s p) (original s) :=
  fun h => original_false s p (h Bool (I p) (substituted_true s p hsp))

end RDF11.GeneralizedScope

