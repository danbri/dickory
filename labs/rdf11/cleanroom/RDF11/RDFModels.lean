/-
RDF 1.1 Semantics §8: an explicit family of full-domain RDF interpretations.
These sufficient parameter assumptions belong to the construction, not to the
specification's definition of every RDF interpretation. Non-type property
extensions remain an arbitrary relation. RDFS conditions are not asserted.
-/
import RDF11.RDF
import RDF11.DatatypeModels

namespace RDF11
namespace RDFModelConstruction

structure Parameters (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) : Prop where
  language_iri : T.literalSyntax.langString = v.iri .rdfLangString
  recognize_language : D (v.iri .rdfLangString)
  recognize_string : D (v.iri .xsdString)
  type_not_datatype : ¬ D (v.iri .rdfType)
  property_not_datatype : ¬ D (v.iri .rdfProperty)
  list_not_datatype : ¬ D (v.iri .rdfList)

abbrev Carrier.{u} (Iri Value : Type) := ULift.{u} (Sum Value (Option Iri))

def embed (w : Value) : Carrier.{u} Iri Value := ⟨.inl w⟩
def name (a : Iri) : Carrier.{u} Iri Value := ⟨.inr (some a)⟩
def unnamed : Carrier.{u} Iri Value := ⟨.inr none⟩

def lift : DatatypeModel.Carrier.{0} Value → Carrier.{u} Iri Value
  | ⟨.inl w⟩ => embed w
  | ⟨.inr ()⟩ => unnamed

def realization : ValueRealization Value (Carrier.{u} Iri Value) where
  value := fun w => some (embed w)
  injective := fun _ _ _ hv hw => Sum.inl.inj (congrArg ULift.down (Option.some.inj (hv.trans hw.symm)))

noncomputable def iriValue (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (a : Iri) : Carrier.{u} Iri Value := by
  classical
  exact if D a then embed (T.identified a) else name a

/-- Datatype objects classify their identity-indexed value spaces, including
langString and its aliases. Named columns are universal; the extra unnamed
resource has an empty column, allowing an empty class in the RDFS extension. -/
def typeExtension (T : DatatypeTheory Iri Literal Value)
    (x y : Carrier.{u} Iri Value) : Prop :=
  match y.down with
  | .inl d => ∃ w, T.datatypeSpace d w ∧ embed w = x
  | .inr (some _) => True
  | .inr none => False

noncomputable def interpretation (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    SimpleInterpretation Iri Literal (Carrier.{u} Iri Value) := by
  classical
  exact {
    IR := fun _ => True
    IR_nonempty := ⟨unnamed, True.intro⟩
    IP := fun _ => True
    IEXT := fun p xy => if p.val = name (v.iri .rdfType) then typeExtension T xy.1.val xy.2.val
      else R p.val xy.1.val xy.2.val
    IS := fun a => ⟨iriValue T D a, Or.inl True.intro⟩
    IL := fun l => ((DatatypeModel.interpretation.{0} T D).IL l).map (fun r => ⟨lift r.val, True.intro⟩)
  }

theorem iriValue_unrecognized (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (a : Iri) (h : ¬ D a) : iriValue.{u} T D a = name a := by
  simp [iriValue, h]

open Classical in
theorem relates_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (p x y : Carrier.{u} Iri Value) :
    (interpretation T D v R).Relates p x y ↔
      if p = name (v.iri .rdfType) then typeExtension T x y else R p x y := by
  simp [SimpleInterpretation.Relates, interpretation]

theorem literalValue_of_base (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (h : (DatatypeModel.interpretation.{0} T D).LiteralValue DatatypeModel.realization l w) :
    (interpretation T D v R).LiteralValue realization l w := by
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨⟨lift r.val, True.intro⟩, ?_, ?_⟩
  · simp [interpretation, hr]
  · have he : DatatypeModel.embed w = r.val := Option.some.inj hv
    change some (embed w) = some (lift r.val)
    rw [← he]
    rfl

theorem datatypes (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    (interpretation T D v R).DConditions T D realization := by
  have h := DatatypeModel.conditions.{0} T D
  constructor
  · intro hd
    simp [realization, interpretation, iriValue, hd]
  · intro l tag hd ht
    exact literalValue_of_base T D v R (h.language l tag hd ht)
  · intro a ha hn
    constructor
    · simp [realization, interpretation, iriValue, ha]
    · intro l hl
      have hb := (h.ordinary a ha hn).2 l hl
      cases hw : T.L2V (T.identified a) (T.literalSyntax.lexical l) with
      | none => simp only [hw] at hb; simp [interpretation, hb]
      | some w => exact literalValue_of_base T D v R (by simpa only [hw] using hb)

theorem datatype_column (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (a : Iri) (ha : D a) (x : Carrier.{u} Iri Value) :
    typeExtension T x (iriValue T D a) ↔
      ∃ w, T.recognizedSpace a w ∧ realization.value w = some x := by
  simp [iriValue, ha, typeExtension, embed, DatatypeTheory.recognizedSpace, realization]

theorem named_column (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (a : Iri) (ha : ¬ D a) (x : Carrier.{u} Iri Value) :
    typeExtension T x (iriValue T D a) := by
  simp [iriValue_unrecognized T D a ha, typeExtension, name]

theorem conditions (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (h : Parameters T D v)
    (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    (interpretation T D v R).RDFConditions T D v realization := by
  have ht := iriValue_unrecognized.{u} T D _ h.type_not_datatype
  have hp := named_column.{u} T D _ h.property_not_datatype
  have hl := named_column.{u} T D _ h.list_not_datatype
  refine {
    datatypes := datatypes T D v R
    language_iri := h.language_iri
    recognize_language := h.recognize_language
    recognize_string := h.recognize_string
    property := ?_
    values_realized := fun _ _ w _ => ⟨embed w, rfl⟩
    datatype_extension := ?_
    axioms := ?_
  }
  · intro x
    change True ↔ (interpretation T D v R).Relates (iriValue T D (v.iri .rdfType)) x (iriValue T D (v.iri .rdfProperty))
    rw [relates_iff, ht, if_pos rfl]
    exact ⟨fun _ => hp x, fun _ => True.intro⟩
  · intro a ha x
    change (interpretation T D v R).Relates (iriValue T D (v.iri .rdfType)) x (iriValue T D a) ↔ _
    rw [relates_iff, ht, if_pos rfl]
    exact datatype_column T D a ha x
  · intro t ht'
    rcases ht' with ⟨p, _, rfl⟩ | rfl
    · apply ((interpretation T D v R).iri_triple_true _ _ _ _).mpr
      change (interpretation T D v R).Relates (iriValue T D (v.iri .rdfType)) _ _
      rw [relates_iff, ht, if_pos rfl]
      exact hp _
    · apply ((interpretation T D v R).iri_triple_true _ _ _ _).mpr
      change (interpretation T D v R).Relates (iriValue T D (v.iri .rdfType)) _ _
      rw [relates_iff, ht, if_pos rfl]
      exact hl _

theorem model (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (h : Parameters T D v)
    (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    (interpretation T D v R).RDFModel T D v := ⟨realization, conditions T D v h R⟩

theorem empty_satisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFModel T D v ∧ I.Satisfies (Set.empty : GeneralizedGraph Iri Literal B) := by
  let I := interpretation.{u} T D v (fun _ _ _ => False)
  exact ⟨Carrier Iri Value, I, model T D v h _, I.satisfies_empty⟩

/-- The standard base recognition set meets the construction's exclusions by
syntactic vocabulary distinctness. Datatype meanings remain external. -/
theorem base_parameters (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (hlang : T.literalSyntax.langString = v.iri .rdfLangString) :
    Parameters T v.baseDatatypes v := by
  refine ⟨hlang, Or.inl rfl, Or.inr rfl, ?_, ?_, ?_⟩
  all_goals
    rintro (h | h)
    all_goals cases v.distinct _ _ h

theorem base_empty_satisfiable (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (hlang : T.literalSyntax.langString = v.iri .rdfLangString) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFModel T v.baseDatatypes v ∧ I.Satisfies (Set.empty : GeneralizedGraph Iri Literal B) :=
  empty_satisfiable T v.baseDatatypes v (base_parameters T v hlang)

theorem non_type_triple_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (R : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v R).Assignment B) (s p o : Iri)
    (hp : ¬ D p) (hne : p ≠ v.iri .rdfType) :
    (interpretation T D v R).TripleTrue A ⟨.iri s, .iri p, .iri o⟩ ↔
      R (name p) (iriValue T D s) (iriValue T D o) := by
  classical
  rw [(interpretation T D v R).iri_triple_true, relates_iff]
  change (if iriValue T D p = name (v.iri .rdfType) then _ else _) ↔ _
  simp [interpretation, iriValue_unrecognized T D p hp, name, hne]

/-- Two full RDF models disagree on a chosen non-type ground triple. -/
theorem non_type_triple_independent (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (h : Parameters T D v) (s p o : Iri)
    (hp : ¬ D p) (hne : p ≠ v.iri .rdfType) :
    let G : GeneralizedGraph Iri Literal B := Set.singleton ⟨.iri s, .iri p, .iri o⟩
    (∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFModel T D v ∧ I.Satisfies G) ∧
      ¬ RDFEntails.{u} T D v (Set.empty : GeneralizedGraph Iri Literal B) G := by
  dsimp only
  constructor
  · let I := interpretation.{u} T D v (fun _ _ _ => True)
    refine ⟨Carrier Iri Value, I, model T D v h _, ?_⟩
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨fun _ => none, ?_⟩
    rintro _ rfl
    exact (non_type_triple_iff T D v _ _ s p o hp hne).mpr True.intro
  · let I := interpretation.{u} T D v (fun _ _ _ => False)
    intro he
    have hg := he (Carrier Iri Value) I (model T D v h _) I.satisfies_empty
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp hg
    exact (non_type_triple_iff T D v _ A s p o hp hne).mp (hA _ rfl)

end RDFModelConstruction

namespace SimpleInterpretation

/-- Recognizing rdf:Property with an empty value space contradicts an RDF axiom. -/
theorem rdf_property_datatype_nonempty (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (hd : D (v.iri .rdfProperty)) :
    ∃ w, T.recognizedSpace (v.iri .rdfProperty) w := by
  have ht := h.axioms _ (Or.inl ⟨RDFSymbol.rdfType, True.intro, rfl⟩)
  have hr := (I.iri_triple_true (fun (_ : Empty) => none) _ _ _).mp ht
  obtain ⟨w, hw, _⟩ := (h.datatype_extension _ hd _).mp hr
  exact ⟨w, hw⟩

end SimpleInterpretation

theorem rdf_unsatisfiable_of_empty_property_datatype (T : DatatypeTheory Iri Literal Value)
    (D : Set Iri) (v : RDFVocabulary Iri) (hd : D (v.iri .rdfProperty))
    (hempty : ∀ w, ¬ T.recognizedSpace (v.iri .rdfProperty) w)
    (G : GeneralizedGraph Iri Literal B) : RDFUnsatisfiable.{u} T D v G := by
  rintro ⟨U, I, ⟨ρ, hρ⟩, _⟩
  obtain ⟨w, hw⟩ := I.rdf_property_datatype_nonempty hρ hd
  exact hempty w hw

end RDF11
