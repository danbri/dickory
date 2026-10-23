/-
Appendix D witnesses reuse one account of properties whose extensions remain
free in the RDFS construction. Their RDF/RDFS axioms still hold by `model`.
-/
import RDF11.RDFSModels

namespace RDF11.RDFSModelConstruction

open RDFModelConstruction

/-- Constructor-local dispatch boundary, not a new W3C vocabulary category. -/
def FreeProperty (p : RDFSSymbol) : Prop :=
  p ≠ .rdf .rdfType ∧ p ≠ .subClassOf ∧ p ≠ .subPropertyOf ∧
  p ≠ .domain ∧ p ≠ .range ∧ p ≠ .member ∧ p ≠ .seeAlso

theorem relates_free (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (p : RDFSSymbol) (hs : SchemaSymbol p) (hp : FreeProperty p)
    (x y : Carrier.{u} Iri Value) :
    (interpretation T D v Q).Relates ((interpretation T D v Q).IS (v.iri p)).val x y ↔
      Q (schemaName v p) x y := by
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  rw [schema_denotation T D v h Q p hs, relates_iff]
  simp [relation, h0, h1, h2, h3, h4, h5, h6]

theorem free_iri_triple_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (s p o : RDFSSymbol)
    (hs : SchemaSymbol s) (hp : SchemaSymbol p) (ho : SchemaSymbol o)
    (hf : FreeProperty p) :
    (interpretation T D v Q).TripleTrue A
      ⟨.iri (v.iri s), .iri (v.iri p), .iri (v.iri o)⟩ ↔
      Q (schemaName v p) (schemaName v s) (schemaName v o) := by
  rw [(interpretation T D v Q).iri_triple_true,
    relates_free T D v h Q p hp hf,
    schema_denotation T D v h Q s hs, schema_denotation T D v h Q o ho]

theorem schema_type_true (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (a : Iri)
    (c : RDFSSymbol) (hc : SchemaSymbol c) :
    (interpretation T D v Q).TripleTrue A
      ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri c)⟩ := by
  apply ((interpretation T D v Q).iri_triple_true A _ _ _).mpr
  exact named_column T D v h Q c hc _

/-- A blank subject is still existential; this equivalence keeps its denotation
explicit while exposing the free predicate and named object. -/
theorem free_blank_triple_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (b : B) (p o : RDFSSymbol)
    (hp : SchemaSymbol p) (ho : SchemaSymbol o) (hf : FreeProperty p) :
    (interpretation T D v Q).TripleTrue A
      ⟨.blank b, .iri (v.iri p), .iri (v.iri o)⟩ ↔
      ∃ x, (A b).map Subtype.val = some x ∧ Q (schemaName v p) x (schemaName v o) := by
  rw [(interpretation T D v Q).named_predicate_true]
  simp [SimpleInterpretation.denote, relates_free T D v h Q p hp hf,
    schema_denotation T D v h Q o ho]

/-- Arbitrary unrecognized IRIs use the constructor's name branch. -/
theorem unrecognized_denotation (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (a : Iri) (ha : ¬ D a) : ((interpretation T D v Q).IS a).val = name a :=
  iriValue_unrecognized T D a ha

/-- Expose a free relation while retaining the shared assignment of both terms. -/
theorem free_term_triple_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (s o : Term Iri Literal B)
    (p : RDFSSymbol) (hp : SchemaSymbol p) (hf : FreeProperty p) :
    (interpretation T D v Q).TripleTrue A ⟨s, .iri (v.iri p), o⟩ ↔
      ∃ x y, (interpretation T D v Q).denote A s = some x ∧
        (interpretation T D v Q).denote A o = some y ∧ Q (schemaName v p) x y := by
  rw [(interpretation T D v Q).named_predicate_true]
  simp only [relates_free T D v h Q p hp hf]

theorem free_unrecognized_object_triple_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (s : Term Iri Literal B)
    (p : RDFSSymbol) (hp : SchemaSymbol p) (hf : FreeProperty p) (a : Iri) (ha : ¬ D a) :
    (interpretation T D v Q).TripleTrue A ⟨s, .iri (v.iri p), .iri a⟩ ↔
      ∃ x, (interpretation T D v Q).denote A s = some x ∧ Q (schemaName v p) x (name a) := by
  rw [free_term_triple_iff T D v h Q A s (.iri a) p hp hf]
  simp [SimpleInterpretation.denote, unrecognized_denotation T D v Q a ha]

end RDF11.RDFSModelConstruction
