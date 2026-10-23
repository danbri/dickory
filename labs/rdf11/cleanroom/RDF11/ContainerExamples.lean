/-
Appendix D.2 (informative): container type does not impose permutations or
filled index gaps. Both conclusion roots remain existential blank nodes.
-/
import RDF11.RDFSFreeProperties

namespace RDF11.ContainerExamples
open RDFModelConstruction RDFSModelConstruction

/-- Ordinary syntax for the two-position Bag example; container 0 is rdf:_1. -/
def twoMemberBag (v : RDFSVocabulary Iri) (a b : Iri) : Graph Iri Literal Unit :=
  Set.ofList [⟨.blank (), v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfBag))⟩,
    ⟨.blank (), v.iri (.rdf (.container 0)), .iri a⟩,
    ⟨.blank (), v.iri (.rdf (.container 1)), .iri b⟩]

/-- The printed permutation conclusion asserts only the two membership edges. -/
def twoPositions (v : RDFSVocabulary Iri) (a b : Iri) : Graph Iri Literal Unit :=
  Set.ofList [⟨.blank (), v.iri (.rdf (.container 0)), .iri a⟩,
    ⟨.blank (), v.iri (.rdf (.container 1)), .iri b⟩]

/-- Ordinary syntax with rdf:_1 and rdf:_3, leaving rdf:_2 unstated. -/
def gappedSequence (v : RDFSVocabulary Iri) (a b : Iri) : Graph Iri Literal Unit :=
  Set.ofList [⟨.blank (), v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfSeq))⟩,
    ⟨.blank (), v.iri (.rdf (.container 0)), .iri a⟩,
    ⟨.blank (), v.iri (.rdf (.container 2)), .iri b⟩]

theorem bag_permutation_not_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a b : RDFSSymbol)
    (ha : SchemaSymbol a) (hb : SchemaSymbol b) (hne : b ≠ a) :
    ¬ RDFSEntails.{u} T D v (twoMemberBag v (v.iri a) (v.iri b)).generalize
      (twoPositions v (v.iri b) (v.iri a)).generalize := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p _ y => (p = schemaName v (.rdf (.container 0)) ∧ y = schemaName v a) ∨
      (p = schemaName v (.rdf (.container 1)) ∧ y = schemaName v b)
  let I := interpretation T D v Q
  let A : I.Assignment Unit := fun _ => some ⟨name (v.iri .resource), True.intro⟩
  have hg : I.Satisfies (twoMemberBag v (v.iri a) (v.iri b)).generalize := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp [twoMemberBag, Set.ofList] at ht
    rcases ht with rfl | rfl | rfl
    · apply (I.named_predicate_true A _ _ _).mpr
      exact ⟨name (v.iri .resource), (I.IS (v.iri (.rdf .rdfBag))).val, rfl, rfl,
        named_column T D v h Q (.rdf .rdfBag) (by simp [SchemaSymbol]) _⟩
    · apply (free_blank_triple_iff T D v h Q A () (.rdf (.container 0)) a
        (by simp [SchemaSymbol]) ha (by simp [FreeProperty])).mpr
      exact ⟨name (v.iri .resource), rfl, Or.inl ⟨rfl, rfl⟩⟩
    · apply (free_blank_triple_iff T D v h Q A () (.rdf (.container 1)) b
        (by simp [SchemaSymbol]) hb (by simp [FreeProperty])).mpr
      exact ⟨name (v.iri .resource), rfl, Or.inr ⟨rfl, rfl⟩⟩
  intro he
  obtain ⟨B, hB⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  have ht := hB _ ⟨⟨.blank (), v.iri (.rdf (.container 0)), .iri (v.iri b)⟩,
    by simp [twoPositions, Set.ofList], rfl⟩
  obtain ⟨x, _, hx⟩ := (free_blank_triple_iff T D v h Q B () (.rdf (.container 0)) b
    (by simp [SchemaSymbol]) hb (by simp [FreeProperty])).mp ht
  simp [Q, hne] at hx

/-- No existential root and object can supply the missing second position. -/
theorem second_position_not_entailed (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a b : RDFSSymbol)
    (ha : SchemaSymbol a) (hb : SchemaSymbol b) :
    ¬ RDFSEntails.{u} T D v (gappedSequence v (v.iri a) (v.iri b)).generalize
      (Set.singleton (⟨.blank false, .iri (v.iri (.rdf (.container 1))), .blank true⟩ :
        GeneralizedTriple Iri Literal Bool)) := by
  let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
    fun p _ _ => p ≠ schemaName v (.rdf (.container 1))
  let I := interpretation T D v Q
  let A : I.Assignment Unit := fun _ => some ⟨name (v.iri .resource), True.intro⟩
  have hg : I.Satisfies (gappedSequence v (v.iri a) (v.iri b)).generalize := by
    apply (I.satisfies_iff_exists_graphTrue _).mpr
    refine ⟨A, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp [gappedSequence, Set.ofList] at ht
    rcases ht with rfl | rfl | rfl
    · apply (I.named_predicate_true A _ _ _).mpr
      exact ⟨name (v.iri .resource), (I.IS (v.iri (.rdf .rdfSeq))).val, rfl, rfl,
        named_column T D v h Q (.rdf .rdfSeq) (by simp [SchemaSymbol]) _⟩
    · apply (free_blank_triple_iff T D v h Q A () (.rdf (.container 0)) a
        (by simp [SchemaSymbol]) ha (by simp [FreeProperty])).mpr
      exact ⟨name (v.iri .resource), rfl, by simp [Q]⟩
    · apply (free_blank_triple_iff T D v h Q A () (.rdf (.container 2)) b
        (by simp [SchemaSymbol]) hb (by simp [FreeProperty])).mpr
      exact ⟨name (v.iri .resource), rfl, by simp [Q]⟩
  intro he
  obtain ⟨B, hB⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
  obtain ⟨x, y, _, _, hr⟩ := (I.named_predicate_true B (.blank false) (.blank true)
    (v.iri (.rdf (.container 1)))).mp (hB _ rfl)
  have hq := (relates_free T D v h Q (.rdf (.container 1)) (by simp [SchemaSymbol])
    (by simp [FreeProperty]) x y).mp hr
  exact hq rfl

/-- The same resource may be both a Bag and a Seq. -/
theorem bag_and_sequence_consistent (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (a : Iri) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (Graph.generalize (Set.ofList [
        (⟨.iri a, v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfBag))⟩ : Triple Iri Literal Empty),
        ⟨.iri a, v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfSeq))⟩])) := by
  let I := interpretation.{u} T D v (fun _ _ _ => False)
  refine ⟨Carrier Iri Value, I, model T D v h _, ?_⟩
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  simp [Set.ofList] at ht
  rcases ht with rfl | rfl
  · exact schema_type_true T D v h _ _ a (.rdf .rdfBag) (by simp [SchemaSymbol])
  · exact schema_type_true T D v h _ _ a (.rdf .rdfSeq) (by simp [SchemaSymbol])

/-- A property on one identified container/member need not transfer to the
other. Additional premises and properties shared by all members are separate. -/
theorem no_container_member_property_transfer (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) (c m : RDFSSymbol)
    (hc : SchemaSymbol c) (hm : SchemaSymbol m) (hne : m ≠ c) :
    let premise (origin : RDFSSymbol) : Graph Iri Literal Empty := Set.ofList [
      ⟨.iri (v.iri c), v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfBag))⟩,
      ⟨.iri (v.iri c), v.iri (.rdf (.container 0)), .iri (v.iri m)⟩,
      ⟨.iri (v.iri origin), v.iri (.rdf .rdfValue), .iri (v.iri .resource)⟩]
    let claim (destination : RDFSSymbol) : GeneralizedGraph Iri Literal Empty := Set.singleton
      ⟨.iri (v.iri destination), .iri (v.iri (.rdf .rdfValue)), .iri (v.iri .resource)⟩
    (¬ RDFSEntails.{u} T D v (premise c).generalize (claim m)) ∧
      (¬ RDFSEntails.{u} T D v (premise m).generalize (claim c)) := by
  dsimp only
  have separate (origin destination : RDFSSymbol) (hfrom : SchemaSymbol origin)
      (hto : SchemaSymbol destination) (hdiff : destination ≠ origin) :
      ¬ RDFSEntails.{u} T D v (Graph.generalize (Set.ofList [
        (⟨.iri (v.iri c), v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfBag))⟩ : Triple Iri Literal Empty),
        ⟨.iri (v.iri c), v.iri (.rdf (.container 0)), .iri (v.iri m)⟩,
        ⟨.iri (v.iri origin), v.iri (.rdf .rdfValue), .iri (v.iri .resource)⟩]))
        (Set.singleton (⟨.iri (v.iri destination), .iri (v.iri (.rdf .rdfValue)),
          .iri (v.iri .resource)⟩ : GeneralizedTriple Iri Literal Empty)) := by
    let Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop :=
      fun p x _ => p ≠ schemaName v (.rdf .rdfValue) ∨ x = schemaName v origin
    let I := interpretation T D v Q
    have hg : I.Satisfies (Graph.generalize (Set.ofList [
        (⟨.iri (v.iri c), v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfBag))⟩ : Triple Iri Literal Empty),
        ⟨.iri (v.iri c), v.iri (.rdf (.container 0)), .iri (v.iri m)⟩,
        ⟨.iri (v.iri origin), v.iri (.rdf .rdfValue), .iri (v.iri .resource)⟩])) := by
      apply (I.satisfies_iff_exists_graphTrue _).mpr
      refine ⟨fun _ => none, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      simp [Set.ofList] at ht
      rcases ht with rfl | rfl | rfl
      · exact schema_type_true T D v h Q _ _ (.rdf .rdfBag) (by simp [SchemaSymbol])
      · exact (free_iri_triple_iff T D v h Q _ c (.rdf (.container 0)) m hc
          (by simp [SchemaSymbol]) hm (by simp [FreeProperty])).mpr (by simp [Q])
      · exact (free_iri_triple_iff T D v h Q _ origin (.rdf .rdfValue) .resource hfrom
          (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mpr (Or.inr rfl)
    intro he
    obtain ⟨A, hA⟩ := (I.satisfies_iff_exists_graphTrue _).mp (he _ I (model T D v h Q) hg)
    have hq := (free_iri_triple_iff T D v h Q A destination (.rdf .rdfValue) .resource hto
      (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [FreeProperty])).mp (hA _ rfl)
    rcases hq with hf | heq
    · exact hf rfl
    · exact hdiff ((schemaName_eq v destination origin).mp heq)
  exact ⟨separate c m hc hm hne, separate m c hm hc (Ne.symm hne)⟩

end RDF11.ContainerExamples
