/-
RDF 1.1 Semantics §8. Named vocabulary, the complete infinite RDF axiom
family and the RDF conjunction over the existing D and property conditions.
The external datatype theory remains a parameter, not a concrete XSD library.
-/
import RDF11.Datatypes
import RDF11.Relations

namespace RDF11

inductive RDFSymbol where
  | rdfType | rdfProperty | rdfSubject | rdfPredicate | rdfObject
  | rdfFirst | rdfRest | rdfValue | rdfNil | rdfList | rdfLangString | xsdString
  | rdfStatement | rdfAlt | rdfBag | rdfSeq
  | container : Nat → RDFSymbol
  deriving DecidableEq

/-- container n denotes rdf:_(n+1); the vocabulary has no finite cutoff. -/
structure RDFVocabulary (Iri : Type) where
  iri : RDFSymbol → Iri
  distinct : ∀ a b, iri a = iri b → a = b

def RDFSymbol.propertyAxiom : RDFSymbol → Prop
  | .rdfType | .rdfSubject | .rdfPredicate | .rdfObject | .rdfFirst | .rdfRest | .rdfValue
  | .container _ => True
  | _ => False

def RDFVocabulary.axioms (v : RDFVocabulary Iri) : GeneralizedGraph Iri Literal B :=
  fun t => (∃ p, p.propertyAxiom ∧ t = ⟨.iri (v.iri p), .iri (v.iri .rdfType), .iri (v.iri .rdfProperty)⟩) ∨
    t = ⟨.iri (v.iri .rdfNil), .iri (v.iri .rdfType), .iri (v.iri .rdfList)⟩

namespace SimpleInterpretation

structure RDFConditions (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri)
    (ρ : ValueRealization Value U) : Prop where
  datatypes : I.DConditions T D ρ
  language_iri : T.literalSyntax.langString = v.iri .rdfLangString
  recognize_language : D (v.iri .rdfLangString)
  recognize_string : D (v.iri .xsdString)
  property : I.RDFPropertyCondition (v.iri .rdfType) (v.iri .rdfProperty)
  values_realized : ∀ a, D a → ∀ w, T.recognizedSpace a w → ∃ x, ρ.value w = some x
  datatype_extension : ∀ a, D a → ∀ x,
    I.Relates (I.IS (v.iri .rdfType)).val x (I.IS a).val ↔
      ∃ w, T.recognizedSpace a w ∧ ρ.value w = some x
  axioms : I.GraphTrue (fun (_ : Empty) => none) v.axioms

def RDFModel (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri) : Prop :=
  ∃ ρ, I.RDFConditions T D v ρ

theorem rdfModel_is_dModel (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFModel T D v) : I.DModel T D := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, hρ.datatypes⟩

theorem rdf_value_space_resources (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (ha : D a) (hw : T.recognizedSpace a w) :
    ∃ r : I.Resource, ρ.value w = some r.val := by
  obtain ⟨x, hx⟩ := h.values_realized a ha w hw
  have ht := (h.datatype_extension a ha x).mpr ⟨w, hw, hx⟩
  exact ⟨⟨x, I.relates_subject ht⟩, hx⟩

theorem rdf_literal_typing (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (hd : D (T.literalSyntax.datatype l))
    (r : I.Resource) (hr : I.IL l = some r) :
    I.Relates (I.IS (v.iri .rdfType)).val r.val (I.IS (T.literalSyntax.datatype l)).val := by
  exact (h.datatype_extension _ hd r.val).mpr (I.recognized_literal_value h.datatypes hd r hr)

theorem rdf_disjoint_datatypes (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (ha : D a) (hb : D b)
    (disjoint : ∀ w, T.recognizedSpace a w → ¬ T.recognizedSpace b w)
    (hxa : I.Relates (I.IS (v.iri .rdfType)).val x (I.IS a).val)
    (hxb : I.Relates (I.IS (v.iri .rdfType)).val x (I.IS b).val) : False := by
  obtain ⟨wa, hwa, hva⟩ := (h.datatype_extension a ha x).mp hxa
  obtain ⟨wb, hwb, hvb⟩ := (h.datatype_extension b hb x).mp hxb
  have he := ρ.injective wa wb x hva hvb
  exact disjoint wa hwa (he ▸ hwb)

theorem rdf_axiom_true (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFConditions T D v ρ) (A : I.Assignment B)
    (t : GeneralizedTriple Iri Literal B) (ht : v.axioms t) : I.TripleTrue A t := by
  rcases ht with ⟨p, hp, rfl⟩ | rfl
  · have hx := h.axioms _ (Or.inl ⟨p, hp, rfl⟩)
    exact (I.iri_triple_true A _ _ _).mpr ((I.iri_triple_true (fun (_ : Empty) => none) _ _ _).mp hx)
  · have hx := h.axioms _ (Or.inr rfl)
    exact (I.iri_triple_true A _ _ _).mpr ((I.iri_triple_true (fun (_ : Empty) => none) _ _ _).mp hx)

end SimpleInterpretation

def RDFEntails.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) : Prop :=
  EntailsUnder.{u} (fun _ I => I.RDFModel T D v) G E

def RDFUnsatisfiable.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B) : Prop :=
  ¬ ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFModel T D v ∧ I.Satisfies G

def RDFVocabulary.baseDatatypes (v : RDFVocabulary Iri) : Set Iri :=
  fun a => a = v.iri .rdfLangString ∨ a = v.iri .xsdString

theorem d_implies_rdf_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (h : DEntails.{u} T D G E) : RDFEntails.{u} T D v G E :=
  stronger_conditions_preserve_entailment (fun _ I hI => I.rdfModel_is_dModel hI) h

theorem simple_implies_rdf_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (h : SimplyEntails.{u} G E) : RDFEntails.{u} T D v G E :=
  d_implies_rdf_entailment T D v (simple_implies_d_entailment T D h)

theorem rdf_empty_entails_axioms (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) :
    RDFEntails.{u} T D v (Set.empty : GeneralizedGraph Iri Literal B₁)
      (v.axioms : GeneralizedGraph Iri Literal B₂) := by
  rintro U I ⟨ρ, hρ⟩ _
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  exact ⟨fun _ => none, fun t ht => I.rdf_axiom_true hρ _ t ht⟩

theorem rdfD2 (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) (G : GeneralizedGraph Iri Literal B) :
    RDFEntails.{u} T D v G (propertyTypingImage (v.iri .rdfType) (v.iri .rdfProperty) G) := by
  rintro U I ⟨ρ, hρ⟩ hG
  exact rdfD2_entailment _ _ G U I hρ.property hG

end RDF11
