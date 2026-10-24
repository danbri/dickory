/-
Appendix B's datatype weakening: every full D-countermodel restricts to a
finite weakened pre-countermodel. The converse requires completion and is
not asserted here. N+B+1 is a proved bound, distinct from the printed formula
(N+B)*(D+1), whose empty-vocabulary case is recorded for source review.
-/
import RDF11.DatatypePreinterpretations
import RDF11.FiniteSimpleModels
import RDF11.DatatypeModels

namespace RDF11

theorem Term.literal_in_names (datatype : Literal → Iri) (t : Term Iri Literal B)
    (l : Literal) (h : t.hasLiteral l) : t.names datatype (.inr l) := by
  cases t <;> simp_all [Term.hasLiteral, Term.names]

theorem GeneralizedTriple.literal_in_names (datatype : Literal → Iri)
    (t : GeneralizedTriple Iri Literal B) (l : Literal) (h : t.hasLiteral l) :
    t.names datatype (.inr l) := by
  rcases h with h | h | h
  · exact Or.inl (t.subject.literal_in_names datatype l h)
  · exact Or.inr (Or.inl (t.predicate.literal_in_names datatype l h))
  · exact Or.inr (Or.inr (t.object.literal_in_names datatype l h))

/-- A local model rules out ill-typed occurring literals, hence gives satisfiability.
The full witness comes from the existing D-model construction; this is not a
completion preserving the local interpretation's relation or other graph truths. -/
theorem d_satisfiable_of_preinterpretation (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : GeneralizedGraph Iri Literal B) (V : Set (Name Iri Literal))
    (hV : Set.subset (G.vocabulary T.literalSyntax.datatype) V)
    (P : PreInterpretation V U) (hD : PreInterpretation.DModel P T D)
    (hG : P.Satisfies (G.restrictNames T.literalSyntax.datatype V hV)) : DSatisfiable.{u} T D G := by
  obtain ⟨ρ, hρ⟩ := hD
  let J := PreInterpretation.extend P
  have hinc := G.include_restrictNames T.literalSyntax.datatype V hV
  have hj : J.Satisfies G := (congrArg (fun X => J.Satisfies X) hinc).mp
    ((PreInterpretation.satisfies_extend P _).mpr hG)
  apply (d_satisfiable_iff_no_illTyped T D G).mpr
  intro t ht l hl hi
  have hname : V (.inr l) := hV _ ⟨t, ht, t.literal_in_names T.literalSyntax.datatype l hl⟩
  have hu := PreInterpretation.illTyped_undefined P hρ ⟨l, hname⟩ hi
  have hju : J.IL l = none := by
    simpa only [J, PreInterpretation.extend, dif_pos hname] using hu
  exact J.graph_with_undefined_literal_false G l hju t ht hl hj

namespace FiniteDatatypeModel

variable {Iri Literal Value B : Type} {U : Type u}
  {V : Set (Name Iri Literal)} {S : Set B}

/-- Compression preserves local datatype values, one premise, and conclusion falsity. -/
theorem compress (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (ρ : ValueRealization Value U) (hD : I.DConditions T D ρ)
    (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B)
    (hV : Set.subset (G.vocabulary T.literalSyntax.datatype) V)
    (hB : Set.subset G.hasBlank S) (hG : I.Satisfies G) :
    ∃ P : PreInterpretation V U,
      P.BoundedDomain (v.triples.length + b.triples.length + 1) ∧
      PreInterpretation.DConditions P T D ρ ∧
      P.Satisfies (G.restrictNames T.literalSyntax.datatype V hV) ∧
      ∀ (C : Type) (E : GeneralizedGraph Iri Literal C)
        (hE : Set.subset (E.vocabulary T.literalSyntax.datatype) V),
        P.Satisfies (E.restrictNames T.literalSyntax.datatype V hE) → I.Satisfies E := by
  obtain ⟨A, hOn, hTrue⟩ := hG
  let P := I.comapNames (fun i : VocabularyIRI V => i.val) (fun l : VocabularyLiteral V => l.val)
  let R := FiniteSimpleModel.restriction I v b A
  let G₀ := G.restrictNames T.literalSyntax.datatype V hV
  have hinc := G.include_restrictNames T.literalSyntax.datatype V hV
  have hp : P.GraphTrue A G₀ := (I.graphTrue_mapNames _ _ A G₀).mp (hinc.symm ▸ hTrue)
  have hkeep : ∀ c r, A c = some r → R.keep r.val := by
    intro c r hr
    exact FiniteSimpleModel.assignment_kept I v b A c (hB c ((hOn c).mp ⟨r, hr⟩)) r hr
  refine ⟨R.interpretation, FiniteSimpleModel.restriction_bounded I v b A,
    PreInterpretation.conditions_domainRestriction P R (PreInterpretation.conditions_of_full I hD),
    R.satisfies_lower G₀ A hkeep hp, ?_⟩
  intro C E hE hPE
  have heinc := E.include_restrictNames T.literalSyntax.datatype V hE
  exact heinc ▸ (I.satisfies_mapNames _ _ _).mpr (R.satisfies_lift _ hPE)

end FiniteDatatypeModel

section Comparison
variable {Iri Literal Value B₁ B₂ : Type} {V : Set (Name Iri Literal)} {S : Set B₁}

/-- One direction only: full non-entailment supplies a finite weakened countermodel. -/
theorem bounded_d_pre_countermodel (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : Set.subset (G.vocabulary T.literalSyntax.datatype) V)
    (hE : Set.subset (E.vocabulary T.literalSyntax.datatype) V)
    (hB : Set.subset G.hasBlank S) (h : ¬ DEntails.{u} T D G E) :
    ∃ (U : Type u) (P : PreInterpretation V U),
      P.BoundedDomain (v.triples.length + b.triples.length + 1) ∧
      PreInterpretation.DModel P T D ∧
      P.Satisfies (G.restrictNames T.literalSyntax.datatype V hG) ∧
      ¬ P.Satisfies (E.restrictNames T.literalSyntax.datatype V hE) := by
  classical
  obtain ⟨U, hu⟩ := Classical.not_forall.mp h
  obtain ⟨I, hi⟩ := Classical.not_forall.mp hu
  obtain ⟨hD, hnot⟩ := Classical.not_imp.mp hi
  obtain ⟨hIG, hIE⟩ := Classical.not_imp.mp hnot
  obtain ⟨ρ, hρ⟩ := hD
  obtain ⟨P, hb, hd, hg, hreflect⟩ := FiniteDatatypeModel.compress I T D ρ hρ v b G hG hB hIG
  exact ⟨U, P, hb, ⟨ρ, hd⟩, hg, fun he => hIE (hreflect B₂ E hE he)⟩

theorem d_entailment_of_bounded_preinterpretations (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : Enumeration V) (b : Enumeration S)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂)
    (hG : Set.subset (G.vocabulary T.literalSyntax.datatype) V)
    (hE : Set.subset (E.vocabulary T.literalSyntax.datatype) V)
    (hB : Set.subset G.hasBlank S)
    (h : ∀ (U : Type u) (P : PreInterpretation V U),
      P.BoundedDomain (v.triples.length + b.triples.length + 1) →
      PreInterpretation.DModel P T D →
      P.Satisfies (G.restrictNames T.literalSyntax.datatype V hG) →
      P.Satisfies (E.restrictNames T.literalSyntax.datatype V hE)) : DEntails.{u} T D G E := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨U, P, hb, hd, hg, he⟩ := bounded_d_pre_countermodel T D v b G E hG hE hB hn
  exact he (h U P hb hd hg)

theorem bounded_d_pre_model_of_satisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : Enumeration V) (b : Enumeration S) (G : GeneralizedGraph Iri Literal B₁)
    (hG : Set.subset (G.vocabulary T.literalSyntax.datatype) V) (hB : Set.subset G.hasBlank S)
    (h : DSatisfiable.{u} T D G) :
    ∃ (U : Type u) (P : PreInterpretation V U),
      P.BoundedDomain (v.triples.length + b.triples.length + 1) ∧
      PreInterpretation.DModel P T D ∧ P.Satisfies (G.restrictNames T.literalSyntax.datatype V hG) := by
  obtain ⟨U, I, ⟨ρ, hρ⟩, hg⟩ := h
  obtain ⟨P, hb, hd, hp, _⟩ := FiniteDatatypeModel.compress I T D ρ hρ v b G hG hB hg
  exact ⟨U, P, hb, ⟨ρ, hd⟩, hp⟩

/-- Satisfiability has both directions even though entailment completion is open. -/
theorem d_satisfiable_iff_bounded_preinterpretations (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : Enumeration V) (b : Enumeration S) (G : GeneralizedGraph Iri Literal B₁)
    (hG : Set.subset (G.vocabulary T.literalSyntax.datatype) V) (hB : Set.subset G.hasBlank S) :
    DSatisfiable.{u} T D G ↔
    ∃ (U : Type u) (P : PreInterpretation V U),
      P.BoundedDomain (v.triples.length + b.triples.length + 1) ∧
      PreInterpretation.DModel P T D ∧ P.Satisfies (G.restrictNames T.literalSyntax.datatype V hG) := by
  constructor
  · exact bounded_d_pre_model_of_satisfiable T D v b G hG hB
  · rintro ⟨U, P, _, hd, hg⟩
    exact d_satisfiable_of_preinterpretation T D G V hG P hd hg

end Comparison

/-- Finite inputs supply exact name and shared blank counts; completion remains open. -/
theorem finite_d_pre_countermodel (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G E : GeneralizedGraph Iri Literal B) (hG : FiniteGraph G) (hE : FiniteGraph E)
    (h : ¬ DEntails.{u} T D G E) :
    let V := Set.union (G.vocabulary T.literalSyntax.datatype) (E.vocabulary T.literalSyntax.datatype)
    ∃ (v : Enumeration V) (b : Enumeration (Set.union G.hasBlank E.hasBlank))
      (U : Type u) (P : PreInterpretation V U),
      P.BoundedDomain (v.triples.length + b.triples.length + 1) ∧
      PreInterpretation.DModel P T D ∧
      P.Satisfies (G.restrictNames T.literalSyntax.datatype V (fun _ => Or.inl)) ∧
      ¬ P.Satisfies (E.restrictNames T.literalSyntax.datatype V (fun _ => Or.inr)) := by
  obtain ⟨v⟩ := finite_shared_vocabulary T.literalSyntax.datatype G E hG hE
  obtain ⟨b⟩ := finite_shared_blank_support G E hG hE
  exact ⟨v, b, bounded_d_pre_countermodel T D v b G E
    (fun _ => Or.inl) (fun _ => Or.inr) (fun _ => Or.inl) h⟩

namespace FiniteDatatypeModel

/-- A §5 resource universe cannot have a zero-size exact enumeration. -/
theorem resource_enumeration_pos (I : SimpleInterpretation Iri Literal U)
    (e : Enumeration I.IR) : 0 < e.triples.length := by
  obtain ⟨r, hr⟩ := I.IR_nonempty
  exact List.length_pos_of_mem ((e.membership r).mpr hr)

theorem no_zero_resource_bound (I : SimpleInterpretation Iri Literal U) :
    ¬ ∃ e : Enumeration I.IR, e.triples.length ≤ 0 := by
  rintro ⟨e, he⟩
  exact Nat.not_lt_of_ge he (resource_enumeration_pos I e)

/-- Empty comparisons have no names or blanks, regardless of recognized datatypes. -/
theorem empty_comparison_counts (datatype : Literal → Iri)
    (v : Enumeration (Set.union
      (GeneralizedGraph.vocabulary datatype (Set.empty : GeneralizedGraph Iri Literal B))
      (GeneralizedGraph.vocabulary datatype (Set.empty : GeneralizedGraph Iri Literal B))))
    (b : Enumeration (Set.union
      (GeneralizedGraph.hasBlank (Set.empty : GeneralizedGraph Iri Literal B))
      (GeneralizedGraph.hasBlank (Set.empty : GeneralizedGraph Iri Literal B)))) :
    v.triples.length = 0 ∧ b.triples.length = 0 := by
  have hv : v.triples = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro n hn
    have h := (v.membership n).mp hn
    rcases h with ⟨_, hf, _⟩ | ⟨_, hf, _⟩ <;> exact hf)
  have hb : b.triples = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro n hn
    have h := (b.membership n).mp hn
    rcases h with ⟨_, hf, _⟩ | ⟨_, hf, _⟩ <;> exact hf)
  exact ⟨congrArg List.length hv, congrArg List.length hb⟩

/-- Checked boundary of the printed formula, not a declared source erratum.
The empty graph is D-satisfiable, but no nonempty-IR pre-interpretation meets
the printed bound for its empty comparison, whatever finite count d is used. -/
theorem empty_comparison_printed_bound_conflict (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (d : Nat)
    (v : Enumeration (Set.union
      (GeneralizedGraph.vocabulary T.literalSyntax.datatype (Set.empty : GeneralizedGraph Iri Literal B))
      (GeneralizedGraph.vocabulary T.literalSyntax.datatype (Set.empty : GeneralizedGraph Iri Literal B))))
    (b : Enumeration (Set.union
      (GeneralizedGraph.hasBlank (Set.empty : GeneralizedGraph Iri Literal B))
      (GeneralizedGraph.hasBlank (Set.empty : GeneralizedGraph Iri Literal B)))) :
    DSatisfiable.{u} T D (Set.empty : GeneralizedGraph Iri Literal B) ∧
    ¬ ∃ (U : Type u) (P : PreInterpretation
        (Set.union (GeneralizedGraph.vocabulary T.literalSyntax.datatype (Set.empty : GeneralizedGraph Iri Literal B))
          (GeneralizedGraph.vocabulary T.literalSyntax.datatype (Set.empty : GeneralizedGraph Iri Literal B))) U),
      ∃ e : Enumeration P.IR, e.triples.length ≤ (v.triples.length + b.triples.length) * (d + 1) := by
  refine ⟨empty_d_satisfiable T D, ?_⟩
  obtain ⟨hv, hb⟩ := empty_comparison_counts T.literalSyntax.datatype v b
  simp only [hv, hb, Nat.zero_add, Nat.zero_mul]
  rintro ⟨U, P, h⟩
  exact no_zero_resource_bound P h

end FiniteDatatypeModel

end RDF11
