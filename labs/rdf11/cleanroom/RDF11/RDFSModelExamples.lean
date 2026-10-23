/-
Source-facing consequences of the explicit RDFS model family: §9 permits
semantic roles to overlap and does not transfer class properties to members
or member properties to classes. §9.1 distinguishes literal values from syntax.
-/
import RDF11.RDFSFreeProperties

namespace RDF11
namespace RDFSModelConstruction

open RDFModelConstruction

theorem iri_literal_true (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (a : Iri) :
    (interpretation T D v Q).TripleTrue A
      ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .literal)⟩ := by
  apply ((interpretation T D v Q).iri_triple_true A _ _ _).mpr
  exact named_column T D v h Q .literal (by simp [SchemaSymbol]) _

theorem iri_literal_satisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a : Iri) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (Set.singleton (α := GeneralizedTriple Iri Literal B)
        ⟨.iri a, .iri (v.iri (.rdf .rdfType)), .iri (v.iri .literal)⟩) := by
  let I := interpretation.{u} T D v (fun _ _ _ => False)
  refine ⟨Carrier Iri Value, I, model T D v h _, ?_⟩
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  rintro _ rfl
  exact iri_literal_true T D v h _ _ a

/-- This witness has completely overlapping roles without identifying datatype spaces. -/
theorem overlapping_roles_model (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      (∀ x, I.IR x ∧ I.IP x ∧ I.IC v x ∧ I.LV v x) := by
  let I := interpretation.{u} T D v (fun _ _ _ => False)
  refine ⟨Carrier Iri Value, I, model T D v h _, ?_⟩
  exact fun x => ⟨True.intro, True.intro, all_classes T D v h _ x, all_literal_values T D v h _ x⟩

/-- Distinct class resources may have the same extension. -/
theorem distinct_coextensive_classes (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    let I := interpretation T D v Q
    (I.IS (v.iri .class_)).val ≠ (I.IS (v.iri .resource)).val ∧
      I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .class_)).val =
        I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri .resource)).val := by
  dsimp only
  constructor
  · rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]),
      schema_denotation T D v h Q _ (by simp [SchemaSymbol])]
    intro he
    cases (schemaName_eq v .class_ .resource).mp he
  · apply Set.ext
    intro x
    exact ⟨fun _ => named_column T D v h Q .resource (by simp [SchemaSymbol]) x,
      fun _ => named_column T D v h Q .class_ (by simp [SchemaSymbol]) x⟩

theorem class_self_membership (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) :
    (interpretation T D v Q).TripleTrue A
      ⟨.iri (v.iri .class_), .iri (v.iri (.rdf .rdfType)), .iri (v.iri .class_)⟩ := by
  apply ((interpretation T D v Q).iri_triple_true A _ _ _).mpr
  exact all_classes T D v h Q _

theorem property_self_application (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) :
    (interpretation T D v Q).TripleTrue A
      ⟨.iri (v.iri .member), .iri (v.iri .member), .iri (v.iri .member)⟩ := by
  rw [(interpretation T D v Q).iri_triple_true,
    schema_denotation T D v h Q _ (by simp [SchemaSymbol]), relates_iff]
  simp [relation]

/-- rdf:value is an example property, not an operation on literal values.
The §8 property axiom and §9 Resource domain/range axioms are already satisfied
by `model`; its subject/object relation can still be the arbitrary relation Q. -/
theorem value_triple_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (s o : RDFSSymbol)
    (hs : SchemaSymbol s) (ho : SchemaSymbol o) :
    (interpretation T D v Q).TripleTrue A
      ⟨.iri (v.iri s), .iri (v.iri (.rdf .rdfValue)), .iri (v.iri o)⟩ ↔
      Q (schemaName v (.rdf .rdfValue)) (schemaName v s) (schemaName v o) := by
  exact free_iri_triple_iff T D v h Q A s (.rdf .rdfValue) o hs
    (by simp [SchemaSymbol]) ho (by simp [FreeProperty])

/-- A class/member typing assertion entails no transfer of an rdf:value assertion
between two distinct, unrecognized schema-name resources in either direction.
This is a concrete pair of countermodels for §9's non-inheritance observation,
not a prohibition of transfer under additional premises. -/
theorem no_class_member_property_transfer (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (s c : RDFSSymbol)
    (hs : SchemaSymbol s) (hc : SchemaSymbol c) (hne : s ≠ c) :
    let member : GeneralizedTriple Iri Literal Empty :=
      ⟨.iri (v.iri s), .iri (v.iri (.rdf .rdfType)), .iri (v.iri c)⟩
    let claim (x : RDFSSymbol) : GeneralizedTriple Iri Literal Empty :=
      ⟨.iri (v.iri x), .iri (v.iri (.rdf .rdfValue)), .iri (v.iri .resource)⟩
    (¬ RDFSEntails.{u} T D v (Set.ofList [member, claim c]) (Set.singleton (claim s))) ∧
    (¬ RDFSEntails.{u} T D v (Set.ofList [member, claim s]) (Set.singleton (claim c))) := by
  dsimp only
  have separate (origin destination : RDFSSymbol) (hfrom : SchemaSymbol origin) (hto : SchemaSymbol destination)
      (hne' : destination ≠ origin) :
      ¬ RDFSEntails.{u} (B₂ := Empty) T D v
        (Set.ofList [⟨.iri (v.iri s), .iri (v.iri (.rdf .rdfType)), .iri (v.iri c)⟩,
          (⟨.iri (v.iri origin), .iri (v.iri (.rdf .rdfValue)), .iri (v.iri .resource)⟩ : GeneralizedTriple Iri Literal Empty)])
        (Set.singleton ⟨.iri (v.iri destination), .iri (v.iri (.rdf .rdfValue)), .iri (v.iri .resource)⟩) := by
    let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
      fun _ x _ => x = schemaName v origin
    let I := interpretation T D v Q
    have hg : I.Satisfies (Set.ofList [
        ⟨.iri (v.iri s), .iri (v.iri (.rdf .rdfType)), .iri (v.iri c)⟩,
        (⟨.iri (v.iri origin), .iri (v.iri (.rdf .rdfValue)), .iri (v.iri .resource)⟩ : GeneralizedTriple Iri Literal Empty)]) := by
      apply (I.satisfies_iff_exists_graphTrue _).mpr
      refine ⟨fun _ => none, ?_⟩
      intro t ht
      simp [Set.ofList] at ht
      rcases ht with rfl | rfl
      · apply (I.iri_triple_true _ _ _ _).mpr
        exact named_column T D v h Q c hc _
      · exact (value_triple_iff T D v h Q _ origin .resource hfrom (by simp [SchemaSymbol])).mpr rfl
    intro he
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
    have hx := (value_triple_iff T D v h Q A destination .resource hto (by simp [SchemaSymbol])).mp (hA _ rfl)
    exact hne' ((schemaName_eq v destination origin).mp hx)
  exact ⟨separate c s hc hs hne, separate s c hs hc (Ne.symm hne)⟩

end RDFSModelConstruction
end RDF11
