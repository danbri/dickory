/-
RDF 1.1 Semantics §6: exact lifting with separate original/conclusion blanks.
Names are inverted only on occurring source blanks; conclusion blanks survive.
-/
import RDF11.Skolemization
namespace RDF11.Skolemization
variable {Iri Literal B C : Type} {datatype : Literal → Iri}
    {G : GeneralizedGraph Iri Literal B}

theorem unname_sound (sk : Skolemization datatype G) (i : Iri) (b : B)
    (hb : sk.unname i = some b) : G.hasBlank b ∧ sk.name b = i := by
  classical
  unfold unname at hb
  split at hb
  next h =>
    have he : Classical.choose h = b := Option.some.inj hb
    exact he ▸ Classical.choose_spec h
  next h => contradiction

noncomputable def liftTerm (sk : Skolemization datatype G) :
    Term Iri Literal C → Term Iri Literal (Sum B C)
  | .iri i => match sk.unname i with
    | some b => .blank (.inl b)
    | none => .iri i
  | .literal l => .literal l
  | .blank c => .blank (.inr c)

def applyLiftedTerm (sk : Skolemization datatype G) :
    Term Iri Literal (Sum B C) → Term Iri Literal C
  | .iri i => .iri i
  | .literal l => .literal l
  | .blank (.inl b) => .iri (sk.name b)
  | .blank (.inr c) => .blank c

theorem apply_liftTerm (sk : Skolemization datatype G) (q : Term Iri Literal C) :
    sk.applyLiftedTerm (sk.liftTerm q) = q := by
  cases q with
  | iri i =>
    cases hi : sk.unname i with
    | none => simp [liftTerm, applyLiftedTerm, hi]
    | some b => simp [liftTerm, applyLiftedTerm, hi, (sk.unname_sound i b hi).2]
  | literal l => rfl
  | blank c => rfl

noncomputable def liftTriple (sk : Skolemization datatype G)
    (t : GeneralizedTriple Iri Literal C) : GeneralizedTriple Iri Literal (Sum B C) :=
  ⟨sk.liftTerm t.subject, sk.liftTerm t.predicate, sk.liftTerm t.object⟩

def applyLiftedTriple (sk : Skolemization datatype G)
    (t : GeneralizedTriple Iri Literal (Sum B C)) : GeneralizedTriple Iri Literal C :=
  ⟨sk.applyLiftedTerm t.subject, sk.applyLiftedTerm t.predicate, sk.applyLiftedTerm t.object⟩

theorem apply_liftTriple (sk : Skolemization datatype G) (t : GeneralizedTriple Iri Literal C) :
    sk.applyLiftedTriple (sk.liftTriple t) = t := by
  cases t
  simp [applyLiftedTriple, liftTriple, apply_liftTerm]

theorem apply_liftGraph (sk : Skolemization datatype G) (H : GeneralizedGraph Iri Literal C) :
    Set.image sk.applyLiftedTriple (Set.image sk.liftTriple H) = H := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, he⟩
    rw [apply_liftTriple] at he
    exact he ▸ hs
  · intro ht
    exact ⟨sk.liftTriple t, ⟨t, ht, rfl⟩, sk.apply_liftTriple t⟩

/-- An unused blank may take an arbitrary resource; truth fixes used blanks. -/
noncomputable def totalAssignment (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (b : B) : I.Resource :=
  (A b).getD ⟨Classical.choose I.IR_nonempty, Classical.choose_spec I.IR_nonempty⟩

/-- Change only denotations of the chosen Skolem IRIs, retaining all domains,
property extensions and literal denotations of the original interpretation. -/
noncomputable def namedInterpretation (sk : Skolemization datatype G)
    (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B) :
    SimpleInterpretation Iri Literal U where
  IR := I.IR
  IR_nonempty := I.IR_nonempty
  IP := I.IP
  IEXT := I.IEXT
  IS := fun i => match sk.unname i with
    | none => I.IS i
    | some b => ⟨(totalAssignment I A b).val, Or.inl (totalAssignment I A b).property⟩
  IL := I.IL

noncomputable def liftAssignment (I : SimpleInterpretation Iri Literal U)
    (A : I.Assignment B) (E : I.Assignment C) : I.Assignment (Sum B C) :=
  Sum.elim (fun b => some (totalAssignment I A b)) E

theorem denote_liftTerm (sk : Skolemization datatype G)
    (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (E : I.Assignment C) (q : Term Iri Literal C) :
    I.denote (liftAssignment I A E) (sk.liftTerm q) =
      (sk.namedInterpretation I A).denote E q := by
  cases q with
  | iri i =>
    cases hi : sk.unname i <;>
      simp [liftTerm, SimpleInterpretation.denote, liftAssignment, namedInterpretation, hi]
  | literal l => rfl
  | blank c => rfl

theorem tripleTrue_lift (sk : Skolemization datatype G)
    (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (E : I.Assignment C) (t : GeneralizedTriple Iri Literal C) :
    I.TripleTrue (liftAssignment I A E) (sk.liftTriple t) ↔
      (sk.namedInterpretation I A).TripleTrue E t := by
  simp only [SimpleInterpretation.TripleTrue, liftTriple, denote_liftTerm]
  rfl

theorem unname_of_fresh (sk : Skolemization datatype G) (i : Iri)
    (hf : ∀ b, G.hasBlank b → sk.name b ≠ i) : sk.unname i = none := by
  cases hi : sk.unname i with
  | none => rfl
  | some b => exact False.elim (hf b (sk.unname_sound i b hi).1 (sk.unname_sound i b hi).2)

theorem named_denote_substituted (sk : Skolemization datatype G)
    (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (q : Term Iri Literal B) (x : U) (hx : I.denote A q = some x)
    (hn : ∀ b, G.hasBlank b → ¬ q.names datatype (.inl (sk.name b)))
    (hb : ∀ b, q.hasBlank b → G.hasBlank b) :
    (sk.namedInterpretation I A).denote (fun (_ : B) => none)
      (q.substitute sk.substitution) = some x := by
  cases q with
  | iri i =>
    have hi : sk.unname i = none := sk.unname_of_fresh i (fun b hbg he => hn b hbg (congrArg Sum.inl he))
    simpa [Term.substitute, SimpleInterpretation.denote, namedInterpretation, hi] using hx
  | literal l => exact hx
  | blank b =>
    have hbg := hb b rfl
    cases ha : A b with
    | none => simp [SimpleInterpretation.denote, ha] at hx
    | some r =>
      have he : r.val = x := Option.some.inj (by simpa [SimpleInterpretation.denote, ha] using hx)
      simp [Term.substitute, substitution, Substitution.resolve, SimpleInterpretation.denote,
        namedInterpretation, sk.unname_name b hbg, totalAssignment, ha, he]

theorem named_satisfies_skolem (sk : Skolemization datatype G)
    (I : SimpleInterpretation Iri Literal U) (A : I.Assignment B)
    (hG : I.GraphTrue A G) : (sk.namedInterpretation I A).Satisfies sk.graph := by
  apply ((sk.namedInterpretation I A).satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨p, s, o, hp, hs, ho, hr⟩ := hG t ht
  have term (q : Term Iri Literal B) (x : U) (hx : I.denote A q = some x)
      (hn : ∀ n, q.names datatype n → t.names datatype n)
      (hb : ∀ b, q.hasBlank b → t.hasBlank b) :
      (sk.namedInterpretation I A).denote (fun (_ : B) => none)
        (q.substitute sk.substitution) = some x :=
    sk.named_denote_substituted I A q x hx
      (fun b hbg hqn => sk.fresh b hbg ⟨t, ht, hn _ hqn⟩)
      (fun b hqb => ⟨t, ht, hb b hqb⟩)
  exact ⟨p, s, o,
    term t.predicate p.val hp (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inl h)),
    term t.subject s.val hs (fun _ h => Or.inl h) (fun _ h => Or.inl h),
    term t.object o.val ho (fun _ h => Or.inr (Or.inr h)) (fun _ h => Or.inr (Or.inr h)), hr⟩

/-- Semantic lifting needs no finiteness or fresh-vocabulary restriction on H. -/
theorem entails_lift (sk : Skolemization datatype G) (H : GeneralizedGraph Iri Literal C)
    (h : SimplyEntails.{u} sk.graph H) :
    SimplyEntails.{u} G (Set.image sk.liftTriple H) := by
  intro U I hg
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp hg
  let J := sk.namedInterpretation I A
  have hj := h U J (sk.named_satisfies_skolem I A hA)
  obtain ⟨E, hE⟩ := (J.satisfies_iff_exists_graphTrue _).mp hj
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨liftAssignment I A E, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (sk.tripleTrue_lift I A E t).mpr (hE t ht)

end RDF11.Skolemization

namespace RDF11

/-- An entailed fixed IRI predicate occurs as a predicate in the premise.
The conclusion may have a different blank-node domain. -/
theorem entailed_iri_predicate_occurs {G : GeneralizedGraph Iri Literal B}
    {H : GeneralizedGraph Iri Literal C} (h : SimplyEntails.{u} G H)
    (t : GeneralizedTriple Iri Literal C) (ht : H t) (i : Iri) (hi : t.predicate = .iri i) :
    ∃ s, G s ∧ s.predicate = .iri i := by
  have hh := h (Herbrand.Carrier.{u} Iri Literal B) (Herbrand.interpretation G) (Herbrand.satisfies G)
  obtain ⟨A, hA⟩ := ((Herbrand.interpretation G).satisfies_iff_exists_graphTrue _).mp hh
  obtain ⟨p, _, _, hp, _, _, s, hs, ep, _, _⟩ := hA t ht
  have he : Herbrand.encode (.iri i : Term Iri Literal B) = Herbrand.encode s.predicate := by
    exact (Option.some.inj (by simpa [hi, SimpleInterpretation.denote, Herbrand.interpretation] using hp)).trans ep
  exact ⟨s, hs, (Option.some.inj (congrArg ULift.down he)).symm⟩

namespace Skolemization
variable {Iri Literal B C : Type} {datatype : Literal → Iri}
    {G : GeneralizedGraph Iri Literal B}

theorem liftTerm_left_blank (sk : Skolemization datatype G) (q : Term Iri Literal C) (b : B)
    (hb : (sk.liftTerm q).hasBlank (.inl b)) : G.hasBlank b := by
  cases q with
  | iri i =>
    cases hi : sk.unname i with
    | none => simp [liftTerm, hi, Term.hasBlank] at hb
    | some c =>
      have he : c = b := by simpa [liftTerm, hi, Term.hasBlank] using hb
      subst c
      exact (sk.unname_sound i b hi).1
  | literal l => simp [liftTerm, Term.hasBlank] at hb
  | blank c => simp [liftTerm, Term.hasBlank] at hb

theorem liftGraph_left_blank (sk : Skolemization datatype G) (H : GeneralizedGraph Iri Literal C)
    (b : B) (hb : GeneralizedGraph.hasBlank (Set.image sk.liftTriple H) (.inl b)) : G.hasBlank b := by
  obtain ⟨_, ⟨t, _, rfl⟩, hb⟩ := hb
  rcases hb with hb | hb | hb
  · exact sk.liftTerm_left_blank t.subject b hb
  · exact sk.liftTerm_left_blank t.predicate b hb
  · exact sk.liftTerm_left_blank t.object b hb

theorem unname_predicate_of_entails (G : Graph Iri Literal B)
    (sk : Skolemization datatype G.generalize) (H : Graph Iri Literal C)
    (h : SimplyEntails.{u} sk.graph H.generalize) (t : Triple Iri Literal C) (ht : H t) :
    sk.unname t.predicate = none := by
  apply sk.unname_of_fresh
  intro b hb he
  obtain ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, hp⟩ :=
    entailed_iri_predicate_occurs h t.generalize ⟨t, ht, rfl⟩ t.predicate rfl
  have hpred : s.predicate = t.predicate := Term.iri.inj hp
  exact sk.fresh b hb ⟨s.generalize, ⟨s, hs, rfl⟩,
    Or.inr (Or.inl (congrArg Sum.inl (he.trans hpred.symm)))⟩

noncomputable def liftSubject (sk : Skolemization datatype G) :
    Subject Iri C → Subject Iri (Sum B C)
  | .iri i => match sk.unname i with
    | some b => .blank (.inl b)
    | none => .iri i
  | .blank c => .blank (.inr c)

theorem liftSubject_toTerm (sk : Skolemization datatype G) (s : Subject Iri C) :
    (sk.liftSubject s).toTerm = sk.liftTerm s.toTerm := by
  cases s with
  | iri i => cases hi : sk.unname i <;> simp [liftSubject, liftTerm, Subject.toTerm, hi]
  | blank c => rfl

/-- Ordinary construction retains the IRI predicate; entailment proves that
it cannot be one of the generated names which inverse lifting replaces. -/
noncomputable def liftOrdinaryTriple (sk : Skolemization datatype G)
    (t : Triple Iri Literal C) : Triple Iri Literal (Sum B C) :=
  ⟨sk.liftSubject t.subject, t.predicate, sk.liftTerm t.object⟩

noncomputable def liftOrdinaryGraph (sk : Skolemization datatype G)
    (H : Graph Iri Literal C) : Graph Iri Literal (Sum B C) :=
  Set.image sk.liftOrdinaryTriple H

theorem generalize_liftOrdinaryTriple (sk : Skolemization datatype G)
    (t : Triple Iri Literal C) (hp : sk.unname t.predicate = none) :
    (sk.liftOrdinaryTriple t).generalize = sk.liftTriple t.generalize := by
  simp [liftOrdinaryTriple, Triple.generalize, liftTriple, liftSubject_toTerm, liftTerm, hp]

theorem ordinary_lift_generalize (G : Graph Iri Literal B)
    (sk : Skolemization datatype G.generalize) (H : Graph Iri Literal C)
    (h : SimplyEntails.{u} sk.graph H.generalize) :
    (sk.liftOrdinaryGraph H).generalize = Set.image sk.liftTriple H.generalize := by
  apply Set.ext
  intro t
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s.generalize, ⟨s, hs, rfl⟩,
      (sk.generalize_liftOrdinaryTriple s (sk.unname_predicate_of_entails G H h s hs)).symm⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨sk.liftOrdinaryTriple s, ⟨s, hs, rfl⟩,
      sk.generalize_liftOrdinaryTriple s (sk.unname_predicate_of_entails G H h s hs)⟩

/-- Exact ordinary lifting using separate copies of original/conclusion blanks.
H may contain generated IRIs; neither graph is required to be finite. -/
theorem ordinary_exact_lifting (G : Graph Iri Literal B)
    (sk : Skolemization datatype G.generalize) (H : Graph Iri Literal C)
    (h : SimplyEntails.{u} sk.graph H.generalize) :
    ∃ H' : Graph Iri Literal (Sum B C), SimplyEntails.{u} G.generalize H'.generalize ∧
      (∀ b, H'.generalize.hasBlank (.inl b) → G.generalize.hasBlank b) ∧
      Set.image sk.applyLiftedTriple H'.generalize = H.generalize := by
  refine ⟨sk.liftOrdinaryGraph H, ?_, ?_, ?_⟩
  · rw [sk.ordinary_lift_generalize G H h]
    exact sk.entails_lift H.generalize h
  · rw [sk.ordinary_lift_generalize G H h]
    exact sk.liftGraph_left_blank H.generalize
  · rw [sk.ordinary_lift_generalize G H h]
    exact sk.apply_liftGraph H.generalize

/-- The older ambient-total naming substitution grounds any input graph;
it is therefore not the extension used to recover a conclusion with blanks. -/
theorem total_substitution_ground (sk : Skolemization datatype G)
    (K : GeneralizedGraph Iri Literal B) : (K.substitute sk.substitution).ground := by
  rintro b ⟨_, ⟨t, _, rfl⟩, hb⟩
  have term (q : Term Iri Literal B) : ¬ (q.substitute sk.substitution).hasBlank b := by
    cases q <;> simp [Term.substitute, substitution, Substitution.resolve, Term.hasBlank]
  rcases hb with hb | hb | hb
  · exact term t.subject hb
  · exact term t.predicate hb
  · exact term t.object hb

theorem total_substitution_cannot_recover_blank_conclusion (sk : Skolemization datatype G)
    (H : GeneralizedGraph Iri Literal B) (b : B) (hb : H.hasBlank b)
    (K : GeneralizedGraph Iri Literal B) : H ≠ K.substitute sk.substitution := by
  intro he
  exact sk.total_substitution_ground K b (he ▸ hb)

end Skolemization
end RDF11
