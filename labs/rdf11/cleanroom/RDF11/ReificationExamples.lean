/-
Appendix D.1: checked counterexamples to automatic assertion/reification
inference. These are families of witnesses, not claims about every triple.
-/
import RDF11.Reification
import RDF11.RDFSFreeProperties

namespace RDF11.ReificationExamples
open RDFModelConstruction RDFSModelConstruction

/-- rdf:value is a free example predicate; s and o select named resources. -/
def valueTriple (v : RDFSVocabulary Iri) (s o : RDFSSymbol) : Triple Iri Literal B :=
  ⟨.iri (v.iri s), v.iri (.rdf .rdfValue), .iri (v.iri o)⟩

theorem reification_true (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (A : (interpretation T D v Q).Assignment B) (r s o : RDFSSymbol)
    (hr : SchemaSymbol r) (hs : SchemaSymbol s) (ho : SchemaSymbol o)
    (hsub : Q (schemaName v (.rdf .rdfSubject)) (schemaName v r) (schemaName v s))
    (hpred : Q (schemaName v (.rdf .rdfPredicate)) (schemaName v r) (schemaName v (.rdf .rdfValue)))
    (hobj : Q (schemaName v (.rdf .rdfObject)) (schemaName v r) (schemaName v o)) :
    (interpretation T D v Q).GraphTrue A
      ((valueTriple v s o).reification v.toRDF (.iri (v.iri r))).generalize := by
  rintro _ ⟨t, ht, rfl⟩
  simp [Triple.reification, Set.ofList] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact schema_type_true T D v h Q A _ (.rdf .rdfStatement) (by simp [SchemaSymbol])
  · exact (free_iri_triple_iff T D v h Q A r (.rdf .rdfSubject) s hr
      (by simp [SchemaSymbol]) hs (by simp [FreeProperty])).mpr hsub
  · exact (free_iri_triple_iff T D v h Q A r (.rdf .rdfPredicate) (.rdf .rdfValue) hr
      (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mpr hpred
  · exact (free_iri_triple_iff T D v h Q A r (.rdf .rdfObject) o hr
      (by simp [SchemaSymbol]) ho (by simp [FreeProperty])).mpr hobj

theorem reification_not_assertion (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (r s o : RDFSSymbol)
    (hr : SchemaSymbol r) (hs : SchemaSymbol s) (ho : SchemaSymbol o) :
    ¬ RDFSEntails.{u} T D v
      (((valueTriple v s o : Triple Iri Literal Empty).reification v.toRDF (.iri (v.iri r))).generalize)
      (Set.singleton (valueTriple v s o : Triple Iri Literal Empty).generalize) := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p _ _ => p ≠ schemaName v (.rdf .rdfValue)
  let I := interpretation T D v Q
  have hg : I.Satisfies (((valueTriple v s o : Triple Iri Literal Empty).reification v.toRDF
      (.iri (v.iri r))).generalize) := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨fun _ => none, reification_true T D v h Q _ r s o hr hs ho ?_ ?_ ?_⟩
    all_goals simp [Q]
  intro he
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  have hq := (free_iri_triple_iff T D v h Q A s (.rdf .rdfValue) o hs
    (by simp [SchemaSymbol]) ho (by simp [FreeProperty])).mp (hA _ rfl)
  exact hq rfl

/-- The conclusion allows an existential reification root, not just a fixed IRI. -/
theorem assertion_not_existential_reification (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (s o : RDFSSymbol)
    (hs : SchemaSymbol s) (ho : SchemaSymbol o) :
    ¬ RDFSEntails.{u} T D v
      (Set.singleton (valueTriple v s o : Triple Iri Literal Empty).generalize)
      (((valueTriple v s o : Triple Iri Literal Unit).reification v.toRDF (.blank ())).generalize) := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p _ _ => p = schemaName v (.rdf .rdfValue)
  let I := interpretation T D v Q
  have hg : I.Satisfies (Set.singleton (valueTriple v s o : Triple Iri Literal Empty).generalize) := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨fun _ => none, ?_⟩
    rintro _ rfl
    exact (free_iri_triple_iff T D v h Q _ s (.rdf .rdfValue) o hs
      (by simp [SchemaSymbol]) ho (by simp [FreeProperty])).mpr rfl
  intro he
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  have ht := hA _ ⟨⟨.blank (), v.iri (.rdf .rdfSubject), .iri (v.iri s)⟩,
    by simp [Triple.reification, Set.ofList, valueTriple, RDFSVocabulary.toRDF, Subject.toTerm], rfl⟩
  obtain ⟨x, y, _, _, hr⟩ := (I.named_predicate_true A (.blank ()) (.iri (v.iri s))
    (v.iri (.rdf .rdfSubject))).mp ht
  have hq := (relates_free T D v h Q (.rdf .rdfSubject) (by simp [SchemaSymbol])
    (by simp [FreeProperty]) x y).mp hr
  simp [Q] at hq

/-- Two distinct named resources can describe the same components without
transferring metadata. This is separate from the printed blank-node example. -/
theorem same_components_not_metadata (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (r₁ r₂ s o : RDFSSymbol)
    (hr₁ : SchemaSymbol r₁) (hr₂ : SchemaSymbol r₂) (hs : SchemaSymbol s) (ho : SchemaSymbol o)
    (hne : r₂ ≠ r₁) :
    let t : Triple Iri Literal Empty := valueTriple v s o
    let G : Graph Iri Literal Empty := Set.union (t.reification v.toRDF (.iri (v.iri r₁)))
      (Set.union (t.reification v.toRDF (.iri (v.iri r₂)))
        (Set.singleton (valueTriple v r₁ .resource)))
    ¬ RDFSEntails.{u} T D v G.generalize
      (Set.singleton (valueTriple v r₂ .resource : Triple Iri Literal Empty).generalize) := by
  dsimp only
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p x _ => p ≠ schemaName v (.rdf .rdfValue) ∨ x = schemaName v r₁
  let I := interpretation T D v Q
  have reif (r : RDFSSymbol) (hr : SchemaSymbol r) : I.GraphTrue (fun (_ : Empty) => none)
      ((valueTriple v s o).reification v.toRDF (.iri (v.iri r))).generalize := by
    apply reification_true T D v h Q _ r s o hr hs ho
    all_goals simp [Q]
  have hg : I.Satisfies (Graph.generalize (Set.union
      ((valueTriple v s o : Triple Iri Literal Empty).reification v.toRDF (.iri (v.iri r₁)))
      (Set.union ((valueTriple v s o).reification v.toRDF (.iri (v.iri r₂)))
        (Set.singleton (valueTriple v r₁ .resource))))) := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨fun _ => none, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rcases ht with ht | ht | rfl
    · exact reif r₁ hr₁ _ ⟨t, ht, rfl⟩
    · exact reif r₂ hr₂ _ ⟨t, ht, rfl⟩
    · exact (free_iri_triple_iff T D v h Q _ r₁ (.rdf .rdfValue) .resource hr₁
        (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mpr (Or.inr rfl)
  intro he
  obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  have hq := (free_iri_triple_iff T D v h Q A r₂ (.rdf .rdfValue) .resource hr₂
    (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mp (hA _ rfl)
  rcases hq with hf | heq
  · exact hf rfl
  · exact hne ((schemaName_eq v r₂ r₁).mp heq)

end RDF11.ReificationExamples
