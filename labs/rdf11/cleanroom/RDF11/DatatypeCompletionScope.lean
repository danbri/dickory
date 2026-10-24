/-
Appendix B datatype completion, read with §§4, 5 and 7: a scope check.
A global literal can force a datatype IRI's denotation into IR even when the
literal is absent from the comparison vocabulary. This matters for generalized
predicate blanks. The witness uses an abstract custom datatype theory, not XSD.
-/
import RDF11.FiniteDatatypeModels
import RDF11.LiteralSubstitution

namespace RDF11

/-- Fixed datatype identity can force a recognized IRI to denote a resource. -/
theorem SimpleInterpretation.datatype_name_resource_of_literal
    (I : SimpleInterpretation Iri Literal U) (h : I.DConditions T D ρ)
    (ha : D a) (hv : T.RecognizedValue D l (T.identified a)) : I.IR (I.IS a).val := by
  obtain ⟨r, _, hr⟩ := I.recognizedValue_denotes h hv
  have he := Option.some.inj ((I.recognized_datatype_denotation h ha).symm.trans hr)
  exact he.symm ▸ r.property

/-- A generalized predicate blank can use the resource forced by a global literal. -/
theorem d_predicate_blank_of_datatype_value (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (s p o : Iri) (l : Literal) (hp : D p)
    (hv : T.RecognizedValue D l (T.identified p)) :
    DEntails.{u} T D
      (Set.singleton (⟨.iri s, .iri p, .iri o⟩ : GeneralizedTriple Iri Literal Unit))
      (Set.singleton (⟨.iri s, .blank (), .iri o⟩ : GeneralizedTriple Iri Literal Unit)) := by
  intro U I hD hG
  obtain ⟨ρ, hρ⟩ := hD
  have hpr := I.datatype_name_resource_of_literal hρ hp hv
  obtain ⟨A, _, hA⟩ := hG
  obtain ⟨q, x, y, hq, hx, hy, hrel⟩ := hA _ rfl
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => some ⟨(I.IS p).val, hpr⟩, ?_⟩
  intro t ht
  have he : t = ⟨.iri s, .blank (), .iri o⟩ := ht
  subst t
  exact ⟨q, x, y, hq, hx, hy, hrel⟩

namespace DatatypeCompletionScope

inductive Iri where
  | node | property | datatype | lang
  deriving DecidableEq

abbrev Value := Sum (String × String) Iri

def theory : DatatypeTheory Iri Unit Value where
  literalSyntax := {
    langString := .lang
    lexical := fun _ => ""
    datatype := fun _ => .datatype
    language := fun _ => none
    languageTag := fun _ => True
    tag_valid := fun _ _ h => by cases h
    lower_valid := fun _ _ => True.intro
    tagged_iff := fun _ => by simp
  }
  identified := Sum.inr
  L2V := fun d _ => if d = .inr .datatype then some (.inr .property) else
    if d = .inr .lang then none else some (.inl ("", "en"))
  languageValue := fun s t => .inl (s, t)
  language_injective := fun _ _ _ _ h => Prod.mk.inj (Sum.inl.inj h)
  language_noL2V := fun _ => by simp

def recognized : Set Iri := fun i => i = .property ∨ i = .datatype

theorem recognized_value_spaces_nonempty (a : Iri) (ha : recognized a) :
    ∃ v, theory.recognizedSpace a v := by
  rcases ha with rfl | rfl
  · exact ⟨.inl ("", "en"), theory.l2v_in_datatypeSpace (s := "") (by simp [theory])⟩
  · exact ⟨.inr .property, theory.l2v_in_datatypeSpace (s := "") (by simp [theory])⟩

def vocabulary : Set (Name Iri Unit)
  | .inl .node => True
  | .inl .property => True
  | _ => False

def node : VocabularyIRI vocabulary := ⟨.node, True.intro⟩
def property : VocabularyIRI vocabulary := ⟨.property, True.intro⟩

def premise : GeneralizedGraph (VocabularyIRI vocabulary) (VocabularyLiteral vocabulary) Unit :=
  Set.singleton ⟨.iri node, .iri property, .iri node⟩

def conclusion : GeneralizedGraph (VocabularyIRI vocabulary) (VocabularyLiteral vocabulary) Unit :=
  Set.singleton ⟨.iri node, .blank (), .iri node⟩

def premodel : PreInterpretation vocabulary Bool where
  IR := fun x => x = false
  IR_nonempty := ⟨false, rfl⟩
  IP := fun x => x = true
  IEXT := fun _ _ => True
  IS := fun i => if i.val = .property then ⟨true, Or.inr rfl⟩ else ⟨false, Or.inl rfl⟩
  IL := fun l => False.elim l.property

def realization : ValueRealization Value Bool where
  value := fun v => if v = .inr .property then some true else none
  injective := by
    intro v w x hv hw
    split at hv <;> split at hw <;> simp_all

theorem local_conditions : PreInterpretation.DConditions premodel theory recognized realization where
  recognized_denotation := by
    intro a ha
    rcases a with ⟨a, hva⟩
    rcases ha with ha | ha
    · change a = .property at ha
      subst a
      simp [theory, realization, premodel]
    · change a = .datatype at ha
      subst a
      exact False.elim hva
  language := fun l _ _ _ => False.elim l.property
  ordinary := fun l _ _ => False.elim l.property

theorem premise_true : premodel.Satisfies premise := by
  apply (premodel.satisfies_iff_exists_graphTrue premise).mpr
  refine ⟨fun _ => none, ?_⟩
  intro t ht
  have he : t = ⟨.iri node, .iri property, .iri node⟩ := ht
  subst t
  refine ⟨⟨true, rfl⟩, ⟨false, rfl⟩, ⟨false, rfl⟩, ?_, ?_, ?_, True.intro⟩ <;>
    simp [SimpleInterpretation.denote, premodel, node, property]

theorem conclusion_false : ¬ premodel.Satisfies conclusion := by
  rintro ⟨A, _, hA⟩
  obtain ⟨p, _, _, hp, _, _, _⟩ := hA _ rfl
  change (A ()).map Subtype.val = some p.val at hp
  obtain ⟨r, _, hr⟩ := Option.map_eq_some_iff.mp hp
  have hf : r.val = false := r.property
  have ht : p.val = true := p.property
  have he : false = true := hf.symm.trans (hr.trans ht)
  cases he

theorem premodel_bounded : premodel.BoundedDomain 2 := by
  refine ⟨⟨[false, true], by decide, ?_⟩, Nat.le_refl 2⟩
  intro x
  cases x <;> simp [premodel]

theorem premise_inclusion : premise.mapNames Subtype.val Subtype.val =
    Set.singleton (⟨.iri .node, .iri .property, .iri .node⟩ : GeneralizedTriple Iri Unit Unit) := by
  apply Set.ext
  intro t
  simp [GeneralizedGraph.mapNames, Set.image, premise, Set.singleton, GeneralizedTriple.mapNames,
    Term.mapNames, node, property, eq_comm]

theorem conclusion_inclusion : conclusion.mapNames Subtype.val Subtype.val =
    Set.singleton (⟨.iri .node, .blank (), .iri .node⟩ : GeneralizedTriple Iri Unit Unit) := by
  apply Set.ext
  intro t
  simp [GeneralizedGraph.mapNames, Set.image, conclusion, Set.singleton, GeneralizedTriple.mapNames,
    Term.mapNames, node, eq_comm]

theorem comparison_vocabulary :
    Set.union ((premise.mapNames Subtype.val Subtype.val).vocabulary theory.literalSyntax.datatype)
      ((conclusion.mapNames Subtype.val Subtype.val).vocabulary theory.literalSyntax.datatype) = vocabulary := by
  rw [premise_inclusion, conclusion_inclusion]
  apply Set.ext
  intro n
  cases n with
  | inl i =>
    cases i <;> simp [GeneralizedGraph.vocabulary, Set.union, Set.singleton,
      GeneralizedTriple.names, Term.names, vocabulary, Set.empty]
  | inr l =>
    simp [GeneralizedGraph.vocabulary, Set.union, Set.singleton,
      GeneralizedTriple.names, Term.names, vocabulary, Set.empty]

theorem global_literal_absent : ¬ vocabulary (.inr ()) := fun h => h

theorem full_premise_satisfiable : DSatisfiable.{u} theory recognized
    (premise.mapNames Subtype.val Subtype.val) := by
  apply (d_satisfiable_iff_no_illTyped theory recognized _).mpr
  intro t ht l hl
  obtain ⟨q, hq, rfl⟩ := ht
  have he : q = ⟨.iri node, .iri property, .iri node⟩ := hq
  subst q
  simp [GeneralizedTriple.mapNames, Term.mapNames, GeneralizedTriple.hasLiteral, Term.hasLiteral] at hl

theorem literal_forces_property_resource :
    theory.RecognizedValue recognized () (theory.identified .property) := by
  apply DatatypeTheory.RecognizedValue.ordinary (T := theory) (D := recognized) () .datatype _
  · exact Or.inr rfl
  · decide
  · rfl
  · simp [theory]

theorem full_entailment : DEntails.{u} theory recognized
    (premise.mapNames Subtype.val Subtype.val) (conclusion.mapNames Subtype.val Subtype.val) := by
  rw [premise_inclusion, conclusion_inclusion]
  exact d_predicate_blank_of_datatype_value theory recognized .node .property .node ()
    (Or.inl rfl) literal_forces_property_resource

/-- No full model can preserve both displayed local satisfaction values. -/
theorem no_comparison_preserving_completion :
    ¬ ∃ (U : Type u) (I : SimpleInterpretation Iri Unit U),
      I.DModel theory recognized ∧
      (I.Satisfies (premise.mapNames Subtype.val Subtype.val) ↔ premodel.Satisfies premise) ∧
      (I.Satisfies (conclusion.mapNames Subtype.val Subtype.val) ↔ premodel.Satisfies conclusion) := by
  rintro ⟨U, I, hD, hg, he⟩
  exact conclusion_false (he.mp (full_entailment U I hD (hg.mpr premise_true)))

end DatatypeCompletionScope
end RDF11
