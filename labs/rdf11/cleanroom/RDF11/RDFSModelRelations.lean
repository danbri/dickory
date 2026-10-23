/-
An explicit RDFS model family, reusing the corrected RDF interpretation.
The hypotheses are sufficient construction choices, not added RDF restrictions.
Name-object class columns are universal; datatype-object columns retain exact values.
-/
import RDF11.RDFSModelConstraints

namespace RDF11
namespace RDFSModelConstruction

open RDFModelConstruction

/-- Coverage of the actual literal domain, not just a supply of semantic values. -/
def LanguageCoverage (T : DatatypeTheory Iri Literal Value) : Prop :=
  ∀ w, T.languageSpace w → ∃ l tag, T.literalSyntax.language l = some tag ∧
    T.languageValue (T.literalSyntax.lexical l) (asciiLower tag) = w

def SchemaSymbol (s : RDFSSymbol) : Prop :=
  s ≠ .rdf .rdfLangString ∧ s ≠ .rdf .xsdString

structure Parameters (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) : Prop where
  language_iri : T.literalSyntax.langString = v.iri (.rdf .rdfLangString)
  recognize_language : D (v.iri (.rdf .rdfLangString))
  recognize_string : D (v.iri (.rdf .xsdString))
  schema_unrecognized : ∀ s, SchemaSymbol s → ¬ D (v.iri s)
  language_coverage : LanguageCoverage T

theorem Parameters.toRDF (h : Parameters T D v) : RDFModelConstruction.Parameters T D v.toRDF where
  language_iri := h.language_iri
  recognize_language := h.recognize_language
  recognize_string := h.recognize_string
  type_not_datatype := h.schema_unrecognized _ (by simp [SchemaSymbol])
  property_not_datatype := h.schema_unrecognized _ (by simp [SchemaSymbol])
  list_not_datatype := h.schema_unrecognized _ (by simp [SchemaSymbol])

def schemaName (v : RDFSVocabulary Iri) (s : RDFSSymbol) : Carrier.{u} Iri Value := name (v.iri s)

@[simp] theorem schemaName_eq (v : RDFSVocabulary Iri) (s t : RDFSSymbol) :
    (schemaName.{u} (Value := Value) v s = schemaName v t) ↔ s = t := by
  constructor
  · intro h
    exact v.distinct s t (Option.some.inj (Sum.inr.inj (congrArg ULift.down h)))
  · rintro rfl; rfl

/-- All name-object class columns are universal in this witness family. -/
def NameObject (y : Carrier.{u} Iri Value) : Prop := ∃ a, y = name a

def subclass (T : DatatypeTheory Iri Literal Value) (x y : Carrier.{u} Iri Value) : Prop :=
  ∀ z, typeExtension T z x → typeExtension T z y

def subproperty (v : RDFSVocabulary Iri) (x y : Carrier.{u} Iri Value) : Prop :=
  x = y ∨ y = schemaName v .member ∨
    (x = schemaName v .isDefinedBy ∧ y = schemaName v .seeAlso)

/-- Schema roles are fixed; Q controls all remaining property extensions. -/
noncomputable def relation (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (p x y : Carrier.{u} Iri Value) : Prop := by
  classical
  exact if p = schemaName v (.rdf .rdfType) then typeExtension T x y
    else if p = schemaName v .subClassOf then subclass T x y
    else if p = schemaName v .subPropertyOf then subproperty v x y
    else if p = schemaName v .domain ∨ p = schemaName v .range then NameObject y
    else if p = schemaName v .member ∨ p = schemaName v .seeAlso then True
    else Q p x y

noncomputable def interpretation (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :=
  RDFModelConstruction.interpretation T D v.toRDF (relation T v Q)

theorem relates_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (p x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).Relates p x y ↔ relation T v Q p x y := by
  classical
  rw [interpretation, RDFModelConstruction.relates_iff]
  change (if p = schemaName v (.rdf .rdfType) then _ else _) ↔ _
  by_cases hp : p = schemaName v (.rdf .rdfType)
  · simp [hp, relation]
  · simp [hp]

theorem schema_denotation (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (s : RDFSSymbol) (hs : SchemaSymbol s) :
    ((interpretation T D v Q).IS (v.iri s)).val = schemaName v s :=
  iriValue_unrecognized T D _ (h.schema_unrecognized s hs)

theorem relates_subclass (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).Relates ((interpretation T D v Q).IS (v.iri .subClassOf)).val x y ↔
      subclass T x y := by
  rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]), relates_iff]
  simp [relation]

theorem relates_subproperty (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).Relates ((interpretation T D v Q).IS (v.iri .subPropertyOf)).val x y ↔
      subproperty v x y := by
  rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]), relates_iff]
  simp [relation]

theorem relates_domain (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).Relates ((interpretation T D v Q).IS (v.iri .domain)).val x y ↔
      NameObject y := by
  rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]), relates_iff]
  simp [relation]

theorem relates_range (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).Relates ((interpretation T D v Q).IS (v.iri .range)).val x y ↔
      NameObject y := by
  rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]), relates_iff]
  simp [relation]

theorem icext_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).ICEXT (v.iri (.rdf .rdfType)) y x ↔ typeExtension T x y := by
  unfold SimpleInterpretation.ICEXT
  rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]), relates_iff]
  simp [relation]

theorem named_column (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (s : RDFSSymbol) (hs : SchemaSymbol s) (x : Carrier.{u} Iri Value) :
    (interpretation T D v Q).ICEXT (v.iri (.rdf .rdfType))
      ((interpretation T D v Q).IS (v.iri s)).val x := by
  rw [icext_iff T D v h Q, schema_denotation T D v h Q s hs]
  trivial

theorem all_classes (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x : Carrier.{u} Iri Value) : (interpretation T D v Q).IC v x :=
  named_column T D v h Q .class_ (by simp [SchemaSymbol]) x

theorem all_literal_values (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x : Carrier.{u} Iri Value) : (interpretation T D v Q).LV v x :=
  named_column T D v h Q .literal (by simp [SchemaSymbol]) x

theorem subproperty_transitive (v : RDFSVocabulary Iri) (x y z : Carrier.{u} Iri Value)
    (hxy : subproperty v x y) (hyz : subproperty v y z) : subproperty v x z := by
  rcases hxy with rfl | rfl | ⟨rfl, rfl⟩
  · exact hyz
  · rcases hyz with rfl | rfl | ⟨hfalse, _⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · have hf := (schemaName_eq v .member .isDefinedBy).mp hfalse
      cases hf
  · rcases hyz with rfl | rfl | ⟨hfalse, _⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · have hf := (schemaName_eq v .seeAlso .isDefinedBy).mp hfalse
      cases hf

theorem subproperty_inclusion (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x y : Carrier.{u} Iri Value) (hxy : subproperty v x y) (a b : Carrier.{u} Iri Value)
    (hx : (interpretation T D v Q).Relates x a b) :
    (interpretation T D v Q).Relates y a b := by
  rcases hxy with rfl | rfl | ⟨_, rfl⟩
  · exact hx
  · rw [relates_iff]; simp [relation]
  · rw [relates_iff]; simp [relation]

end RDFSModelConstruction
end RDF11
