/-
RDF 1.1 Semantics §5.2–5.3.
Entailment quantifies over all simple interpretations, not an inference engine.
The universe parameter u is explicit; it is not an assumed finite universe.
-/
import RDF11.Simple

namespace RDF11

def SimplyEntails.{u} (G : GeneralizedGraph Iri Literal B₁)
    (E : GeneralizedGraph Iri Literal B₂) : Prop :=
  ∀ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.Satisfies G → I.Satisfies E

def LogicallyEquivalent.{u} (G : GeneralizedGraph Iri Literal B₁)
    (E : GeneralizedGraph Iri Literal B₂) : Prop :=
  SimplyEntails.{u} G E ∧ SimplyEntails.{u} E G

theorem simplyEntails_refl (G : GeneralizedGraph Iri Literal B) :
    SimplyEntails.{u} G G := fun _ _ h => h

theorem simplyEntails_trans {G : GeneralizedGraph Iri Literal B₁}
    {H : GeneralizedGraph Iri Literal B₂} {E : GeneralizedGraph Iri Literal B₃}
    (hGH : SimplyEntails.{u} G H) (hHE : SimplyEntails.{u} H E) :
    SimplyEntails.{u} G E := fun U I h => hHE U I (hGH U I h)

theorem subgraph_entailment {G E : GeneralizedGraph Iri Literal B}
    (hEG : Set.subset E G) : SimplyEntails.{u} G E :=
  fun _ I h => I.satisfies_subgraph hEG h

theorem premise_monotonicity {G H : GeneralizedGraph Iri Literal B₁}
    {E : GeneralizedGraph Iri Literal B₂} (hGH : Set.subset G H)
    (hGE : SimplyEntails.{u} G E) : SimplyEntails.{u} H E :=
  simplyEntails_trans (subgraph_entailment hGH) hGE

theorem entails_empty (G : GeneralizedGraph Iri Literal B₁) :
    SimplyEntails.{u} G (Set.empty : GeneralizedGraph Iri Literal B₂) :=
  fun _ I _ => I.satisfies_empty

/-- A one-element interpretation suffices; no finiteness of G is assumed. -/
def indiscriminate : SimpleInterpretation Iri Literal (ULift.{u} Unit) where
  IR := fun _ => True
  IR_nonempty := ⟨⟨()⟩, True.intro⟩
  IP := fun _ => True
  IEXT := fun _ _ => True
  IS := fun _ => ⟨⟨()⟩, Or.inl True.intro⟩
  IL := fun _ => some ⟨⟨()⟩, True.intro⟩

theorem all_graphs_simply_satisfiable (G : GeneralizedGraph Iri Literal B) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.Satisfies G := by
  refine ⟨ULift.{u} Unit, indiscriminate, ?_⟩
  apply (indiscriminate.satisfies_iff_exists_graphTrue G).mpr
  let I : SimpleInterpretation Iri Literal (ULift.{u} Unit) := indiscriminate
  let r : I.Resource := ⟨⟨()⟩, True.intro⟩
  let A : I.Assignment B := fun _ => some r
  refine ⟨A, ?_⟩
  intro t _
  refine ⟨⟨⟨()⟩, True.intro⟩, r, r, ?_, ?_, ?_, True.intro⟩
  all_goals first
    | cases t.predicate <;> rfl
    | cases t.subject <;> rfl
    | cases t.object <;> rfl

/-- Model with no true triples, used to separate the empty graph. -/
def noPairs : SimpleInterpretation Iri Literal (ULift.{u} Unit) where
  IR := fun _ => True
  IR_nonempty := ⟨⟨()⟩, True.intro⟩
  IP := fun _ => True
  IEXT := fun _ _ => False
  IS := fun _ => ⟨⟨()⟩, Or.inl True.intro⟩
  IL := fun _ => some ⟨⟨()⟩, True.intro⟩

theorem empty_entails_only_empty (E : GeneralizedGraph Iri Literal B₂)
    (h : SimplyEntails.{u} (Set.empty : GeneralizedGraph Iri Literal B₁) E) :
    E = Set.empty := by
  have hE := h (ULift.{u} Unit) noPairs noPairs.satisfies_empty
  obtain ⟨A, hA⟩ := (noPairs.satisfies_iff_exists_graphTrue E).mp hE
  apply Set.ext
  intro t
  constructor
  · intro ht
    obtain ⟨_, _, _, _, _, _, hp⟩ := hA t ht
    exact hp
  · exact False.elim

/-- A semantic extension adds conditions on I, retaining its truth conditions. -/
def EntailsUnder.{u} (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) : Prop :=
  ∀ U I, C U I → I.Satisfies G → I.Satisfies E

theorem extension_preserves_simple_entailment
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    {G : GeneralizedGraph Iri Literal B₁} {E : GeneralizedGraph Iri Literal B₂}
    (h : SimplyEntails.{u} G E) : EntailsUnder C G E := fun U I _ => h U I

theorem stronger_conditions_preserve_entailment
    {C D : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop}
    (hDC : ∀ U I, D U I → C U I)
    {G : GeneralizedGraph Iri Literal B₁} {E : GeneralizedGraph Iri Literal B₂}
    (h : EntailsUnder C G E) : EntailsUnder D G E :=
  fun U I hD => h U I (hDC U I hD)

end RDF11

