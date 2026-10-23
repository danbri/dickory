/-
RDF 1.1 Semantics §9. Classes and properties inhabit the same universe.
ICEXT is defined by rdf:type, not an injective class-to-set encoding.
The literal-image langString condition is retained explicitly.
-/
import RDF11.RDFRules

namespace RDF11

inductive RDFSSymbol where
  | rdf : RDFSymbol → RDFSSymbol
  | domain | range | resource | literal | datatype | class_
  | subClassOf | subPropertyOf | member | container | containerMembershipProperty
  | comment | seeAlso | isDefinedBy | label
  deriving DecidableEq

structure RDFSVocabulary (Iri : Type) where
  iri : RDFSSymbol → Iri
  distinct : ∀ a b, iri a = iri b → a = b

def RDFSVocabulary.toRDF (v : RDFSVocabulary Iri) : RDFVocabulary Iri where
  iri := fun s => v.iri (.rdf s)
  distinct := fun _ _ h => RDFSSymbol.rdf.inj (v.distinct _ _ h)

def rdfsDomainAxioms : List (RDFSSymbol × RDFSSymbol) := [
  (.rdf .rdfType, .resource), (.domain, .rdf .rdfProperty), (.range, .rdf .rdfProperty),
  (.subPropertyOf, .rdf .rdfProperty), (.subClassOf, .class_),
  (.rdf .rdfSubject, .rdf .rdfStatement), (.rdf .rdfPredicate, .rdf .rdfStatement),
  (.rdf .rdfObject, .rdf .rdfStatement), (.member, .resource),
  (.rdf .rdfFirst, .rdf .rdfList), (.rdf .rdfRest, .rdf .rdfList),
  (.seeAlso, .resource), (.isDefinedBy, .resource), (.comment, .resource),
  (.label, .resource), (.rdf .rdfValue, .resource)]

def rdfsRangeAxioms : List (RDFSSymbol × RDFSSymbol) := [
  (.rdf .rdfType, .class_), (.domain, .class_), (.range, .class_),
  (.subPropertyOf, .rdf .rdfProperty), (.subClassOf, .class_),
  (.rdf .rdfSubject, .resource), (.rdf .rdfPredicate, .resource),
  (.rdf .rdfObject, .resource), (.member, .resource),
  (.rdf .rdfFirst, .resource), (.rdf .rdfRest, .rdf .rdfList),
  (.seeAlso, .resource), (.isDefinedBy, .resource), (.comment, .literal),
  (.label, .literal), (.rdf .rdfValue, .resource)]

def rdfsHierarchyAxioms : List (RDFSSymbol × RDFSSymbol × RDFSSymbol) := [
  (.rdf .rdfAlt, .subClassOf, .container), (.rdf .rdfBag, .subClassOf, .container),
  (.rdf .rdfSeq, .subClassOf, .container),
  (.containerMembershipProperty, .subClassOf, .rdf .rdfProperty),
  (.isDefinedBy, .subPropertyOf, .seeAlso), (.datatype, .subClassOf, .class_)]

def rdfsAxiomSymbols (s p o : RDFSSymbol) : Prop :=
  (p = .domain ∧ (s, o) ∈ rdfsDomainAxioms) ∨
  (p = .range ∧ (s, o) ∈ rdfsRangeAxioms) ∨
  (s, p, o) ∈ rdfsHierarchyAxioms ∨
  ∃ n, s = .rdf (.container n) ∧
    ((p = .rdf .rdfType ∧ o = .containerMembershipProperty) ∨
     (p = .domain ∧ o = .resource) ∨ (p = .range ∧ o = .resource))

def RDFSVocabulary.axioms (v : RDFSVocabulary Iri) : GeneralizedGraph Iri Literal B :=
  fun t => ∃ s p o, rdfsAxiomSymbols s p o ∧
    t = ⟨.iri (v.iri s), .iri (v.iri p), .iri (v.iri o)⟩

namespace SimpleInterpretation

def ICEXT (I : SimpleInterpretation Iri Literal U) (typeIRI : Iri) (y : U) : Set U :=
  fun x => I.Relates (I.IS typeIRI).val x y

def IC (I : SimpleInterpretation Iri Literal U) (v : RDFSVocabulary Iri) : Set U :=
  I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .class_)).val

def LV (I : SimpleInterpretation Iri Literal U) (v : RDFSVocabulary Iri) : Set U :=
  I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .literal)).val

theorem icext_resources (I : SimpleInterpretation Iri Literal U) (typeIRI : Iri) (y : U) :
    Set.subset (I.ICEXT typeIRI y) I.IR := fun _ h => I.relates_subject h

theorem classes_are_resources (I : SimpleInterpretation Iri Literal U) (v : RDFSVocabulary Iri) :
    Set.subset (I.IC v) I.IR := I.icext_resources _ _

structure RDFSConditions (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (ρ : ValueRealization Value U) : Prop where
  rdf : I.RDFConditions T D v.toRDF ρ
  resource_extension : ∀ x, I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .resource)).val x ↔ I.IR x
  language_extension : ∀ x,
    I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri (.rdf .rdfLangString))).val x ↔
    ∃ l tag, T.literalSyntax.language l = some tag ∧
      ∃ r : I.Resource, I.IL l = some r ∧ r.val = x
  datatype_typing : ∀ a, D a →
    I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .datatype)).val (I.IS a).val
  domain : ∀ p c x y, I.Relates (I.IS (v.iri .domain)).val p c → I.Relates p x y →
    I.ICEXT (v.iri (.rdf .rdfType)) c x
  range : ∀ p c x y, I.Relates (I.IS (v.iri .range)).val p c → I.Relates p x y →
    I.ICEXT (v.iri (.rdf .rdfType)) c y
  subproperty_transitive : ∀ x y z,
    I.Relates (I.IS (v.iri .subPropertyOf)).val x y →
    I.Relates (I.IS (v.iri .subPropertyOf)).val y z →
    I.Relates (I.IS (v.iri .subPropertyOf)).val x z
  subproperty_reflexive : ∀ x, I.IP x → I.Relates (I.IS (v.iri .subPropertyOf)).val x x
  subproperty_endpoints : ∀ x y, I.Relates (I.IS (v.iri .subPropertyOf)).val x y → I.IP x ∧ I.IP y
  subproperty_inclusion : ∀ x y, I.Relates (I.IS (v.iri .subPropertyOf)).val x y →
    ∀ a b, I.Relates x a b → I.Relates y a b
  class_resource : ∀ x, I.IC v x →
    I.Relates (I.IS (v.iri .subClassOf)).val x (I.IS (v.iri .resource)).val
  subclass_transitive : ∀ x y z,
    I.Relates (I.IS (v.iri .subClassOf)).val x y →
    I.Relates (I.IS (v.iri .subClassOf)).val y z →
    I.Relates (I.IS (v.iri .subClassOf)).val x z
  subclass_reflexive : ∀ x, I.IC v x → I.Relates (I.IS (v.iri .subClassOf)).val x x
  subclass_endpoints : ∀ x y, I.Relates (I.IS (v.iri .subClassOf)).val x y → I.IC v x ∧ I.IC v y
  subclass_inclusion : ∀ x y, I.Relates (I.IS (v.iri .subClassOf)).val x y →
    Set.subset (I.ICEXT (v.iri (.rdf .rdfType)) x) (I.ICEXT (v.iri (.rdf .rdfType)) y)
  container_subproperty : ∀ x,
    I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .containerMembershipProperty)).val x →
    I.Relates (I.IS (v.iri .subPropertyOf)).val x (I.IS (v.iri .member)).val
  datatype_subclass : ∀ x,
    I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .datatype)).val x →
    I.Relates (I.IS (v.iri .subClassOf)).val x (I.IS (v.iri .literal)).val
  axioms : I.GraphTrue (fun (_ : Empty) => none) v.axioms

def RDFSModel (I : SimpleInterpretation Iri Literal U)
    (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri) : Prop :=
  ∃ ρ, I.RDFSConditions T D v ρ

theorem rdfsModel_is_rdfModel (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSModel T D v) : I.RDFModel T D v.toRDF := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, hρ.rdf⟩

theorem rdfs_property_extension (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) :
    I.IP = I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri (.rdf .rdfProperty))).val :=
  Set.ext h.rdf.property

theorem rdfs_datatype_extension (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (ha : D a) (x : U) :
    I.ICEXT (v.iri (.rdf .rdfType)) (I.IS a).val x ↔
      ∃ w, T.recognizedSpace a w ∧ ρ.value w = some x := h.rdf.datatype_extension a ha x

theorem rdfs_axiom_true (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (A : I.Assignment B)
    (t : GeneralizedTriple Iri Literal B) (ht : v.axioms t) : I.TripleTrue A t := by
  obtain ⟨s, p, o, ha, rfl⟩ := ht
  have hx := h.axioms _ ⟨s, p, o, ha, rfl⟩
  exact (I.iri_triple_true A _ _ _).mpr ((I.iri_triple_true (fun (_ : Empty) => none) _ _ _).mp hx)

theorem rdfs_iri_resource (I : SimpleInterpretation Iri Literal U)
    (h : I.RDFSConditions T D v ρ) (a : Iri) :
    I.Relates (I.IS (v.iri (.rdf .rdfType))).val (I.IS a).val (I.IS (v.iri .resource)).val := by
  apply (h.resource_extension _).mpr
  rcases (I.IS a).property with hr | hp
  · exact hr
  · exact I.rdf_properties_are_resources h.rdf.property _ hp

end SimpleInterpretation

def RDFSEntails.{u} (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G : GeneralizedGraph Iri Literal B₁) (E : GeneralizedGraph Iri Literal B₂) : Prop :=
  EntailsUnder.{u} (fun _ I => I.RDFSModel T D v) G E

theorem rdf_implies_rdfs_entailment (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : RDFEntails.{u} T D v.toRDF G E) : RDFSEntails.{u} T D v G E :=
  stronger_conditions_preserve_entailment (fun _ I hI => I.rdfsModel_is_rdfModel hI) h

theorem rdfs_empty_entails_axioms (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) :
    RDFSEntails.{u} T D v (Set.empty : GeneralizedGraph Iri Literal B₁)
      (v.axioms : GeneralizedGraph Iri Literal B₂) := by
  rintro U I ⟨ρ, hρ⟩ _
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  exact ⟨fun _ => none, fun t ht => I.rdfs_axiom_true hρ _ t ht⟩

end RDF11
