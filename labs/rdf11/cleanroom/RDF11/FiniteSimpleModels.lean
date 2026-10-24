/-
RDF 1.1 Semantics, informative Appendix B: the N+B+1 simple-model bound.
Keep one resource, the interpreted comparison names, and one premise's blank
witnesses. Restrict both IR and IP, including property-only name denotations.
An ambient U may contain unused objects; the bound covers every active object.
-/
import RDF11.DomainRestriction
import RDF11.Preinterpretations
import RDF11.FiniteInstances

namespace RDF11

section Enumeration
variable {α : Type u} {S : Set α}

noncomputable def Enumeration.subset (e : Enumeration S) (T : Set α)
    (h : Set.subset T S) : Enumeration T := by
  classical
  exact {
    triples := e.triples.filter (fun x => decide (T x))
    nodup := List.Pairwise.filter _ e.nodup
    membership := by
      intro x
      simp only [List.mem_filter, decide_eq_true_eq, e.membership]
      exact ⟨And.right, fun hx => ⟨h x hx, hx⟩⟩
  }

theorem Enumeration.subset_length (e : Enumeration S) (T : Set α) (h : Set.subset T S) :
    (e.subset T h).triples.length ≤ e.triples.length :=
  List.length_filter_le _ _

theorem Enumeration.fromList_length [DecidableEq α] (xs : List α) :
    (Enumeration.fromList xs).triples.length ≤ xs.length :=
  (Enumeration.unique_nodup xs).length_le_of_subset (fun x hx => (Enumeration.mem_unique xs x).mp hx)

end Enumeration

/-- Count resources and properties together, counting overlap only once. -/
def SimpleInterpretation.BoundedDomain (I : SimpleInterpretation Iri Literal U) (n : Nat) : Prop :=
  ∃ e : Enumeration (fun x => I.IR x ∨ I.IP x), e.triples.length ≤ n

theorem SimpleInterpretation.BoundedDomain.resources
    {I : SimpleInterpretation Iri Literal U} {n : Nat} (h : I.BoundedDomain n) :
    ∃ e : Enumeration I.IR, e.triples.length ≤ n := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.subset I.IR (fun _ => Or.inl), Nat.le_trans (e.subset_length _ _) he⟩

namespace FiniteSimpleModel

variable {Iri Literal B : Type} {U : Type u} {V : Set (Name Iri Literal)} {S : Set B}

def nameValue (I : SimpleInterpretation Iri Literal U) : Name Iri Literal → Option U
  | .inl i => some (I.IS i).val
  | .inr l => (I.IL l).map Subtype.val

theorem nameValue_active (I : SimpleInterpretation Iri Literal U)
    (n : Name Iri Literal) {x : U} (h : nameValue I n = some x) : I.IR x ∨ I.IP x := by
  cases n with
  | inl i => exact (Option.some.inj h) ▸ (I.IS i).property
  | inr l =>
    obtain ⟨r, _, he⟩ := Option.map_eq_some_iff.mp h
    exact Or.inl (he ▸ r.property)

noncomputable def values (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B) : List U :=
  v.triples.filterMap (nameValue I) ++
  b.triples.filterMap (fun c => (A c).map Subtype.val) ++ [Classical.choose I.IR_nonempty]

theorem values_length (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B) :
    (values I v b A).length ≤ v.triples.length + b.triples.length + 1 := by
  have hn := List.length_filterMap_le (nameValue I) v.triples
  have hb := List.length_filterMap_le (fun c => (A c).map Subtype.val) b.triples
  simpa only [values, List.length_append, List.length_cons, List.length_nil, Nat.add_assoc] using
    Nat.add_le_add_right (Nat.add_le_add hn hb) 1

theorem name_kept (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B)
    (n : Name Iri Literal) (hn : V n) {x : U} (hx : nameValue I n = some x) :
    x ∈ values I v b A := by
  simp only [values, List.mem_append]
  exact Or.inl (Or.inl (List.mem_filterMap.mpr ⟨n, (v.membership n).mpr hn, hx⟩))

theorem assignment_kept (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B)
    (c : B) (hc : S c) (r : I.Resource) (hr : A c = some r) :
    r.val ∈ values I v b A := by
  simp only [values, List.mem_append]
  exact Or.inl (Or.inr (List.mem_filterMap.mpr ⟨c, (b.membership c).mpr hc, by simp [hr]⟩))

theorem values_active (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B)
    {x : U} (hx : x ∈ values I v b A) : I.IR x ∨ I.IP x := by
  simp only [values, List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | he
  · obtain ⟨n, _, he⟩ := List.mem_filterMap.mp hx
    exact nameValue_active I n he
  · obtain ⟨c, _, he⟩ := List.mem_filterMap.mp hx
    obtain ⟨r, _, hr⟩ := Option.map_eq_some_iff.mp he
    exact Or.inl (hr ▸ r.property)
  · exact Or.inl (he.symm ▸ Classical.choose_spec I.IR_nonempty)

/-- Restrict the comparison-vocabulary interpretation to the selected values. -/
noncomputable def restriction (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B) :
    (I.comapNames (fun i : VocabularyIRI V => i.val)
      (fun l : VocabularyLiteral V => l.val)).DomainRestriction where
  keep := Set.ofList (values I v b A)
  resource := ⟨⟨Classical.choose I.IR_nonempty, Classical.choose_spec I.IR_nonempty⟩,
    by simp [Set.ofList, values]⟩
  names := fun i => name_kept I v b A (.inl i.val) i.property rfl
  literals := fun l r h => name_kept I v b A (.inr l.val) l.property (by
    change (I.IL l.val).map Subtype.val = some r.val
    change I.IL l.val = some r at h
    rw [h]
    rfl)

theorem restriction_bounded (I : SimpleInterpretation Iri Literal U)
    (v : Enumeration V) (b : Enumeration S) (A : I.Assignment B) :
    (restriction I v b A).interpretation.BoundedDomain
      (v.triples.length + b.triples.length + 1) := by
  classical
  let e := Enumeration.fromList (values I v b A)
  refine ⟨⟨e.triples, e.nodup, ?_⟩, Nat.le_trans (Enumeration.fromList_length _) (values_length I v b A)⟩
  intro x
  rw [e.membership]
  change x ∈ values I v b A ↔
    (I.IR x ∧ x ∈ values I v b A) ∨ (I.IP x ∧ x ∈ values I v b A)
  constructor
  · intro hx
    exact (values_active I v b A hx).elim (fun h => Or.inl ⟨h, hx⟩) (fun h => Or.inr ⟨h, hx⟩)
  · exact fun h => h.elim And.right And.right

/-- Keep a premise model and reflect every conclusion over the selected names. -/
theorem compress (I : SimpleInterpretation Iri Literal U)
    (datatype : Literal → Iri) (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B) (hV : Set.subset (G.vocabulary datatype) V)
    (hB : Set.subset G.hasBlank S) (hG : I.Satisfies G) :
    ∃ J : SimpleInterpretation Iri Literal U,
      J.BoundedDomain (v.triples.length + b.triples.length + 1) ∧ J.Satisfies G ∧
      ∀ (C : Type) (E : GeneralizedGraph Iri Literal C),
        Set.subset (E.vocabulary datatype) V → J.Satisfies E → I.Satisfies E := by
  obtain ⟨A, hOn, hTrue⟩ := hG
  let P := I.comapNames (fun i : VocabularyIRI V => i.val) (fun l : VocabularyLiteral V => l.val)
  let R := restriction I v b A
  let G₀ := G.restrictNames datatype V hV
  have hinc := G.include_restrictNames datatype V hV
  have hp : P.GraphTrue A G₀ := (I.graphTrue_mapNames _ _ A G₀).mp (hinc.symm ▸ hTrue)
  have hkeep : ∀ c r, A c = some r → R.keep r.val := by
    intro c r hr
    exact assignment_kept I v b A c (hB c ((hOn c).mp ⟨r, hr⟩)) r hr
  have hg₀ := R.satisfies_lower G₀ A hkeep hp
  let J := PreInterpretation.extend R.interpretation
  refine ⟨J, restriction_bounded I v b A, ?_, ?_⟩
  · exact hinc ▸ (PreInterpretation.satisfies_extend R.interpretation G₀).mpr hg₀
  · intro C E hE hJE
    let E₀ := E.restrictNames datatype V hE
    have heinc := E.include_restrictNames datatype V hE
    have hr := (PreInterpretation.satisfies_extend R.interpretation E₀).mp (heinc.symm ▸ hJE)
    exact heinc ▸ (I.satisfies_mapNames _ _ E₀).mpr (R.satisfies_lift E₀ hr)

end FiniteSimpleModel

section Comparison
variable {Iri Literal B₁ B₂ : Type} {V : Set (Name Iri Literal)} {S : Set B₁}

/-- A countermodel needs only N names, B allowed premise blanks, and one resource. -/
theorem bounded_simple_countermodel (datatype : Literal → Iri)
    (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : Set.subset (G.vocabulary datatype) V) (hE : Set.subset (E.vocabulary datatype) V)
    (hB : Set.subset G.hasBlank S) (h : ¬ SimplyEntails.{u} G E) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.BoundedDomain (v.triples.length + b.triples.length + 1) ∧ I.Satisfies G ∧ ¬ I.Satisfies E := by
  classical
  obtain ⟨U, hu⟩ := Classical.not_forall.mp h
  obtain ⟨I, hi⟩ := Classical.not_forall.mp hu
  obtain ⟨hIG, hIE⟩ := Classical.not_imp.mp hi
  obtain ⟨J, hj, hjG, hreflect⟩ := FiniteSimpleModel.compress I datatype v b G hG hB hIG
  exact ⟨U, J, hj, hjG, fun hJE => hIE (hreflect B₂ E hE hJE)⟩

/-- Quantification over bounded domains gives exactly the existing entailment. -/
theorem simple_entailment_iff_bounded (datatype : Literal → Iri)
    (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : Set.subset (G.vocabulary datatype) V) (hE : Set.subset (E.vocabulary datatype) V)
    (hB : Set.subset G.hasBlank S) :
    SimplyEntails.{u} G E ↔ ∀ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.BoundedDomain (v.triples.length + b.triples.length + 1) → I.Satisfies G → I.Satisfies E := by
  constructor
  · intro h U I _
    exact h U I
  · intro h
    apply Classical.byContradiction
    intro hn
    obtain ⟨U, I, hb, hg, he⟩ := bounded_simple_countermodel datatype v b G E hG hE hB hn
    exact he (h U I hb hg)

theorem simple_satisfiable_iff_bounded (datatype : Literal → Iri)
    (v : Enumeration V) (b : Enumeration S) (G : GeneralizedGraph Iri Literal B₁)
    (hG : Set.subset (G.vocabulary datatype) V) (hB : Set.subset G.hasBlank S) :
    SimplySatisfiable.{u} G ↔ ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.BoundedDomain (v.triples.length + b.triples.length + 1) ∧ I.Satisfies G := by
  constructor
  · rintro ⟨U, I, hi⟩
    obtain ⟨J, hj, hg, _⟩ := FiniteSimpleModel.compress I datatype v b G hG hB hi
    exact ⟨U, J, hj, hg⟩
  · rintro ⟨U, I, _, hg⟩
    exact ⟨U, I, hg⟩

end Comparison

/-- Appendix B's exact comparison vocabulary and shared blank-identity count. -/
theorem simple_entailment_iff_bounded_preinterpretations (datatype : Literal → Iri)
    (G E : GeneralizedGraph Iri Literal B)
    (v : Enumeration (Set.union (G.vocabulary datatype) (E.vocabulary datatype)))
    (b : Enumeration (Set.union G.hasBlank E.hasBlank)) :
    let V := Set.union (G.vocabulary datatype) (E.vocabulary datatype)
    SimplyEntails.{u} G E ↔ ∀ (U : Type u) (I : PreInterpretation V U),
      I.BoundedDomain (v.triples.length + b.triples.length + 1) →
      I.Satisfies (G.restrictNames datatype V (fun _ => Or.inl)) →
      I.Satisfies (E.restrictNames datatype V (fun _ => Or.inr)) := by
  let V := Set.union (G.vocabulary datatype) (E.vocabulary datatype)
  let G₀ := G.restrictNames datatype V (fun _ => Or.inl)
  let E₀ := E.restrictNames datatype V (fun _ => Or.inr)
  have hginc := G.include_restrictNames datatype V (fun _ => Or.inl)
  have heinc := E.include_restrictNames datatype V (fun _ => Or.inr)
  constructor
  · intro h U I _ hi
    let J := PreInterpretation.extend I
    have hjG : J.Satisfies G := (congrArg (fun X => J.Satisfies X) hginc).mp
      ((PreInterpretation.satisfies_extend I G₀).mpr hi)
    exact (PreInterpretation.satisfies_extend I E₀).mp
      ((congrArg (fun X => J.Satisfies X) heinc).mpr (h U J hjG))
  · intro h
    apply (simple_entailment_iff_bounded datatype v b G E
      (fun _ => Or.inl) (fun _ => Or.inr) (fun _ => Or.inl)).mpr
    intro U I hb hg
    let P := I.comapNames (fun i : VocabularyIRI V => i.val) (fun l : VocabularyLiteral V => l.val)
    have hp := (I.satisfies_mapNames _ _ G₀).mp (hginc.symm ▸ hg)
    exact heinc ▸ (I.satisfies_mapNames _ _ E₀).mpr (h U P hb hp)

theorem simple_satisfiable_iff_bounded_preinterpretations (datatype : Literal → Iri)
    (G E : GeneralizedGraph Iri Literal B)
    (v : Enumeration (Set.union (G.vocabulary datatype) (E.vocabulary datatype)))
    (b : Enumeration (Set.union G.hasBlank E.hasBlank)) :
    let V := Set.union (G.vocabulary datatype) (E.vocabulary datatype)
    SimplySatisfiable.{u} G ↔ ∃ (U : Type u) (I : PreInterpretation V U),
      I.BoundedDomain (v.triples.length + b.triples.length + 1) ∧
      I.Satisfies (G.restrictNames datatype V (fun _ => Or.inl)) := by
  let V := Set.union (G.vocabulary datatype) (E.vocabulary datatype)
  let G₀ := G.restrictNames datatype V (fun _ => Or.inl)
  have hginc := G.include_restrictNames datatype V (fun _ => Or.inl)
  constructor
  · intro h
    obtain ⟨U, I, hb, hg⟩ := (simple_satisfiable_iff_bounded datatype v b G
      (fun _ => Or.inl) (fun _ => Or.inl)).mp h
    exact ⟨U, I.comapNames Subtype.val Subtype.val, hb,
      (I.satisfies_mapNames _ _ G₀).mp (hginc.symm ▸ hg)⟩
  · rintro ⟨U, I, _, hg⟩
    let J := PreInterpretation.extend I
    exact ⟨U, J, (congrArg (fun X => J.Satisfies X) hginc).mp
      ((PreInterpretation.satisfies_extend I G₀).mpr hg)⟩

/-- Finite inputs supply the exact shared-identity blank enumeration used above. -/
theorem finite_shared_blank_support (G E : GeneralizedGraph Iri Literal B)
    (hG : FiniteGraph G) (hE : FiniteGraph E) :
    Nonempty (Enumeration (Set.union G.hasBlank E.hasBlank)) := by
  classical
  obtain ⟨g⟩ := finite_blank_support_of_finite_graph G hG
  obtain ⟨e⟩ := finite_blank_support_of_finite_graph E hE
  let b := Enumeration.fromList (g.triples ++ e.triples)
  refine ⟨⟨b.triples, b.nodup, ?_⟩⟩
  intro x
  rw [b.membership]
  exact List.mem_append.trans (or_congr (g.membership x) (e.membership x))

/-- Finite input graphs have an N+B+1 countermodel whenever entailment fails. -/
theorem finite_simple_countermodel (datatype : Literal → Iri)
    (G E : GeneralizedGraph Iri Literal B) (hG : FiniteGraph G) (hE : FiniteGraph E)
    (h : ¬ SimplyEntails.{u} G E) :
    ∃ (v : Enumeration (Set.union (G.vocabulary datatype) (E.vocabulary datatype)))
      (b : Enumeration (Set.union G.hasBlank E.hasBlank))
      (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.BoundedDomain (v.triples.length + b.triples.length + 1) ∧ I.Satisfies G ∧ ¬ I.Satisfies E := by
  obtain ⟨v⟩ := finite_shared_vocabulary datatype G E hG hE
  obtain ⟨b⟩ := finite_shared_blank_support G E hG hE
  exact ⟨v, b, bounded_simple_countermodel datatype v b G E
    (fun _ => Or.inl) (fun _ => Or.inr) (fun _ => Or.inl) h⟩

end RDF11
