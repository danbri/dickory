/-
Appendix D.3: collection countermodels preserve the printed existential shapes.
Arbitrary unrecognized item IRIs are allowed; constructor hypotheses remain.
-/
import RDF11.Collections
import RDF11.RDFSFreeProperties

namespace RDF11.CollectionExamples
open Collections RDFModelConstruction RDFSModelConstruction

theorem permutation_not_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a b : Iri)
    (ha : ¬ D a) (hb : ¬ D b) (hne : b ≠ a) :
    ¬ RDFSEntails.{u} T D v (twoItemChain v a b).generalize
      (twoItemChain v b a).generalize := by
  classical
  let u : Carrier.{u} Iri Value := schemaName v .resource
  let w : Carrier.{u} Iri Value := schemaName v .class_
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p x y => if p = schemaName v (.rdf .rdfFirst) then
      (x = u ∧ y = name a) ∨ (x = w ∧ y = name b)
    else if p = schemaName v (.rdf .rdfRest) then
      (x = u ∧ y = w) ∨ (x = w ∧ y = schemaName v (.rdf .rdfNil))
    else False
  let I := interpretation T D v Q
  let A : I.Assignment Bool := fun b => some ⟨if b then w else u, True.intro⟩
  have hg : I.Satisfies (twoItemChain v a b).generalize := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp [twoItemChain, cell, Set.union, Set.ofList] at ht
    rcases ht with (rfl | rfl) | (rfl | rfl)
    · apply (free_unrecognized_object_triple_iff T D v h Q A (.blank false) (.rdf .rdfFirst)
        (by simp [SchemaSymbol]) (by simp [FreeProperty]) a ha).mpr
      exact ⟨u, rfl, by simp [Q]⟩
    · apply (free_term_triple_iff T D v h Q A (.blank false) (.blank true) (.rdf .rdfRest)
        (by simp [SchemaSymbol]) (by simp [FreeProperty])).mpr
      exact ⟨u, w, rfl, rfl, by simp [Q]⟩
    · apply (free_unrecognized_object_triple_iff T D v h Q A (.blank true) (.rdf .rdfFirst)
        (by simp [SchemaSymbol]) (by simp [FreeProperty]) b hb).mpr
      exact ⟨w, rfl, by simp [Q]⟩
    · apply (free_blank_triple_iff T D v h Q A true (.rdf .rdfRest) (.rdf .rdfNil)
        (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mpr
      exact ⟨w, rfl, by simp [Q]⟩
  intro he
  obtain ⟨B, hB⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  have hfirst := hB _ ⟨⟨.blank false, v.iri (.rdf .rdfFirst), .iri b⟩,
    by simp [twoItemChain, cell, Set.union, Set.ofList], rfl⟩
  obtain ⟨x, hx, hqx⟩ := (free_unrecognized_object_triple_iff T D v h Q B (.blank false)
    (.rdf .rdfFirst) (by simp [SchemaSymbol]) (by simp [FreeProperty]) b hb).mp hfirst
  have hxw : x = w := by simpa [Q, name, hne] using hqx
  have hsecond := hB _ ⟨⟨.blank true, v.iri (.rdf .rdfFirst), .iri a⟩,
    by simp [twoItemChain, cell, Set.union, Set.ofList], rfl⟩
  obtain ⟨y, hy, hqy⟩ := (free_unrecognized_object_triple_iff T D v h Q B (.blank true)
    (.rdf .rdfFirst) (by simp [SchemaSymbol]) (by simp [FreeProperty]) a ha).mp hsecond
  have hyu : y = u := by simpa [Q, name, Ne.symm hne] using hqy
  have hrest := hB _ ⟨⟨.blank false, v.iri (.rdf .rdfRest), .blank true⟩,
    by simp [twoItemChain, cell, Set.union, Set.ofList], rfl⟩
  obtain ⟨x', y', hx', hy', hqr⟩ := (free_term_triple_iff T D v h Q B (.blank false)
    (.blank true) (.rdf .rdfRest) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mp hrest
  have ex := I.denote_unique B (.blank false) hx hx'
  have ey := I.denote_unique B (.blank true) hy hy'
  subst x'; subst y'
  simp [Q, hxw, hyu, u, w] at hqr

/-- Distinct semantic values, not just different spellings, witness branching. -/
theorem branching_consistent (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a b c : Iri)
    (ha : ¬ D a) (hb : ¬ D b) (hc : ¬ D c)
    (hab : a ≠ b) (hcn : c ≠ v.iri (.rdf .rdfNil)) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (branchingCell v a b c).generalize ∧
      (I.IS a).val ≠ (I.IS b).val ∧ (I.IS c).val ≠ (I.IS (v.iri (.rdf .rdfNil))).val := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop := fun _ _ _ => True
  let I := interpretation T D v Q
  let A : I.Assignment Unit := fun _ => some ⟨schemaName v .resource, True.intro⟩
  refine ⟨Carrier Iri Value, I, model T D v h Q, ?_, ?_, ?_⟩
  · apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp [branchingCell, cell, Set.union, Set.ofList] at ht
    rcases ht with (rfl | rfl) | (rfl | rfl)
    · exact (free_unrecognized_object_triple_iff T D v h Q A (.blank ()) (.rdf .rdfFirst)
        (by simp [SchemaSymbol]) (by simp [FreeProperty]) a ha).mpr ⟨_, rfl, True.intro⟩
    · exact (free_unrecognized_object_triple_iff T D v h Q A (.blank ()) (.rdf .rdfRest)
        (by simp [SchemaSymbol]) (by simp [FreeProperty]) c hc).mpr ⟨_, rfl, True.intro⟩
    · exact (free_unrecognized_object_triple_iff T D v h Q A (.blank ()) (.rdf .rdfFirst)
        (by simp [SchemaSymbol]) (by simp [FreeProperty]) b hb).mpr ⟨_, rfl, True.intro⟩
    · exact (free_blank_triple_iff T D v h Q A () (.rdf .rdfRest) (.rdf .rdfNil)
        (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mpr ⟨_, rfl, True.intro⟩
  · change ((interpretation T D v Q).IS a).val ≠ ((interpretation T D v Q).IS b).val
    rw [unrecognized_denotation T D v Q a ha, unrecognized_denotation T D v Q b hb]
    simpa [name] using hab
  · change ((interpretation T D v Q).IS c).val ≠ ((interpretation T D v Q).IS (v.iri (.rdf .rdfNil))).val
    rw [unrecognized_denotation T D v Q c hc,
      schema_denotation T D v h Q (.rdf .rdfNil) (by simp [SchemaSymbol])]
    simpa [schemaName, name] using hcn

/-- A first edge need not entail even an entirely existential rest edge. -/
theorem rest_existence_not_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a : Iri) :
    ¬ RDFSEntails.{u} T D v (headOnly v a).generalize
      (Set.singleton (⟨.blank false, .iri (v.iri (.rdf .rdfRest)), .blank true⟩ :
        GeneralizedTriple Iri Literal Bool)) := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p _ _ => p = schemaName v (.rdf .rdfFirst)
  let I := interpretation T D v Q
  let A : I.Assignment Unit := fun _ => some ⟨schemaName v .resource, True.intro⟩
  have hg : I.Satisfies (headOnly v a).generalize := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, ?_⟩
    rintro _ ⟨t, rfl, rfl⟩
    apply (I.named_predicate_true A (.blank ()) (.iri a) (v.iri (.rdf .rdfFirst))).mpr
    refine ⟨schemaName v .resource, (I.IS a).val, rfl, rfl, ?_⟩
    exact (relates_free T D v h Q (.rdf .rdfFirst) (by simp [SchemaSymbol])
      (by simp [FreeProperty]) _ _).mpr rfl
  intro he
  obtain ⟨B, hB⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  obtain ⟨x, y, _, _, hr⟩ := (free_term_triple_iff T D v h Q B (.blank false) (.blank true)
    (.rdf .rdfRest) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mp (hB _ rfl)
  simp [Q] at hr

/-- Derived witness: baseline RDFS does not enforce nil's empty-list convention
by prohibiting outgoing edges. A traversal may still stop on reaching nil. -/
theorem nil_self_edges_consistent (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (cell v (.iri (v.iri (.rdf .rdfNil))) (.iri (v.iri (.rdf .rdfNil)))
        (.iri (v.iri (.rdf .rdfNil))) : Graph Iri Literal Empty).generalize := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop := fun _ _ _ => True
  let I := interpretation T D v Q
  refine ⟨Carrier Iri Value, I, model T D v h Q, ?_⟩
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  simp [cell, Set.ofList] at ht
  rcases ht with rfl | rfl
  · exact (free_iri_triple_iff T D v h Q _ (.rdf .rdfNil) (.rdf .rdfFirst) (.rdf .rdfNil)
      (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [SchemaSymbol])
      (by simp [FreeProperty])).mpr True.intro
  · exact (free_iri_triple_iff T D v h Q _ (.rdf .rdfNil) (.rdf .rdfRest) (.rdf .rdfNil)
      (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [SchemaSymbol])
      (by simp [FreeProperty])).mpr True.intro

end RDF11.CollectionExamples
