/-
Appendix D.2 permits infinite membership. The same RDFS model satisfies an
infinite ordinary graph and every displayed finite prefix with its next edge.
This does not prove arbitrary-graph membership-extension consistency.
-/
import RDF11.RDFSFreeProperties
import RDF11.NameInfinitude
import RDF11.FiniteEntailment

namespace RDF11.ContainerInfinitude
open RDFModelConstruction RDFSModelConstruction

/-- A fixed IRI-named Bag root; RDF roles need not be disjoint. -/
def bagType (v : RDFSVocabulary Iri) : Triple Iri Literal Empty :=
  ⟨.iri (v.iri .resource), v.iri (.rdf .rdfType), .iri (v.iri (.rdf .rdfBag))⟩

/-- Position n+1 has the corresponding indexed-vocabulary IRI as its object. -/
def indexedTriple (v : RDFSVocabulary Iri) (n : Nat) : Triple Iri Literal Empty :=
  ⟨.iri (v.iri .resource), v.iri (.rdf (.container n)), .iri (v.iri (.rdf (.container n)))⟩

def allIndexed (v : RDFSVocabulary Iri) : Graph Iri Literal Empty :=
  fun t => t = bagType v ∨ ∃ n, t = indexedTriple v n

def finitePrefix (v : RDFSVocabulary Iri) (k : Nat) : Graph Iri Literal Empty :=
  Set.ofList (bagType v :: (List.range k).map (indexedTriple v))

noncomputable def prefixEnumeration (v : RDFSVocabulary Iri) (k : Nat) :
    Enumeration (finitePrefix (Literal := Literal) v k) := by
  classical
  exact Enumeration.fromList _

theorem prefix_subset (v : RDFSVocabulary Iri) (k : Nat) :
    Set.subset (finitePrefix (Literal := Literal) v k) (allIndexed v) := by
  intro t ht
  simp [finitePrefix, Set.ofList, List.mem_map] at ht
  rcases ht with rfl | ⟨n, _, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨n, rfl⟩

theorem prefix_next (v : RDFSVocabulary Iri) (k : Nat) :
    finitePrefix (Literal := Literal) v (k + 1) = Set.union (finitePrefix v k) (Set.singleton (indexedTriple v k)) := by
  apply Set.ext
  intro t
  simp [finitePrefix, Set.ofList, List.range_succ, List.map_append, Set.union, Set.singleton, or_assoc]

theorem allIndexed_ground (v : RDFSVocabulary Iri) :
    (allIndexed (Literal := Literal) v).generalize.ground := by
  intro b
  cases b

theorem indexed_generalize_injective (v : RDFSVocabulary Iri) (m n : Nat)
    (he : (indexedTriple (Literal := Literal) v m).generalize = (indexedTriple v n).generalize) : m = n :=
  v.toRDF.container_injective m n (Term.iri.inj (congrArg GeneralizedTriple.predicate he))

theorem allIndexed_not_finite (v : RDFSVocabulary Iri) :
    ¬ FiniteGraph (allIndexed (Literal := Literal) v).generalize := by
  apply Enumeration.no_enumeration_of_nat_injection _ (fun n => (indexedTriple v n).generalize)
  · intro n
    exact ⟨indexedTriple v n, Or.inr ⟨n, rfl⟩, rfl⟩
  · exact indexed_generalize_injective v

/-- The already verified RDFS construction with all free property edges true. -/
noncomputable def interpretation (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) : SimpleInterpretation Iri Literal (Carrier.{u} Iri Value) :=
  RDFSModelConstruction.interpretation T D v (fun _ _ _ => True)

theorem allIndexed_true (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    (interpretation.{u} T D v).GraphTrue (fun (_ : Empty) => none) (allIndexed v).generalize := by
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with rfl | ⟨n, rfl⟩
  · exact schema_type_true T D v h _ _ _ (.rdf .rdfBag) (by simp [SchemaSymbol])
  · exact (free_iri_triple_iff T D v h _ _ .resource (.rdf (.container n)) (.rdf (.container n))
      (by simp [SchemaSymbol]) (by simp [SchemaSymbol]) (by simp [SchemaSymbol])
      (by simp [FreeProperty])).mpr True.intro

theorem allIndexed_satisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (allIndexed v).generalize := by
  let I := interpretation.{u} T D v
  exact ⟨Carrier Iri Value, I, model T D v h _,
    (I.satisfies_iff_exists_graphTrue _).mpr ⟨fun _ => none, allIndexed_true T D v h⟩⟩

theorem prefixes_extend_in_common_model (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      ∀ k, FiniteGraph (finitePrefix (Literal := Literal) v k).generalize ∧ I.Satisfies (finitePrefix v k).generalize ∧
        I.Satisfies (Graph.generalize (Set.union (finitePrefix v k) (Set.singleton (indexedTriple v k)))) := by
  obtain ⟨U, I, hI, hg⟩ := allIndexed_satisfiable.{u} T D v h
  have hp (k : Nat) : I.Satisfies (finitePrefix v k).generalize := by
    apply I.satisfies_subgraph _ hg
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, prefix_subset v k t ht, rfl⟩
  refine ⟨U, I, hI, fun k => ⟨?_, hp k, ?_⟩⟩
  · exact ⟨(prefixEnumeration v k).image Triple.generalize⟩
  · rw [← prefix_next]
    exact hp (k + 1)

/-- This chosen model has distinct denotations; no unique-name rule is imposed
on other models of the infinite graph. -/
theorem infinite_members_witness (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (allIndexed v).generalize ∧ ∃ (root : U) (member : Nat → U),
        I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri (.rdf .rdfBag))).val root ∧
        (∀ n, member n = (I.IS (v.iri (.rdf (.container n)))).val) ∧
        (∀ m n, member m = member n → m = n) ∧
        (∀ n, I.Relates (I.IS (v.iri (.rdf (.container n)))).val root (member n) ∧
          I.Relates (I.IS (v.iri .member)).val root (member n)) := by
  let I := interpretation.{u} T D v
  let root : Carrier.{u} Iri Value := name (v.iri .resource)
  let member (n : Nat) : Carrier.{u} Iri Value := schemaName v (.rdf (.container n))
  refine ⟨Carrier Iri Value, I, model T D v h _,
    (I.satisfies_iff_exists_graphTrue _).mpr ⟨fun _ => none, allIndexed_true T D v h⟩,
    root, member, named_column T D v h _ (.rdf .rdfBag) (by simp [SchemaSymbol]) root, ?_, ?_, ?_⟩
  · intro n
    exact (schema_denotation T D v h _ (.rdf (.container n)) (by simp [SchemaSymbol])).symm
  · intro m n he
    exact RDFSymbol.container.inj (RDFSSymbol.rdf.inj ((schemaName_eq v _ _).mp he))
  · intro n
    have hi : I.Relates (I.IS (v.iri (.rdf (.container n)))).val root (member n) :=
      (relates_free T D v h _ (.rdf (.container n)) (by simp [SchemaSymbol])
        (by simp [FreeProperty]) root (member n)).mpr True.intro
    have hs := (conditions T D v h (fun _ _ _ => True)).container_subproperty
      (I.IS (v.iri (.rdf (.container n)))).val
      (named_column T D v h _ .containerMembershipProperty (by simp [SchemaSymbol]) _)
    exact ⟨hi, (conditions T D v h (fun _ _ _ => True)).subproperty_inclusion _ _ hs root (member n) hi⟩

theorem nonfinite_member_extension (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U), I.RDFSModel T D v ∧
      I.Satisfies (allIndexed v).generalize ∧ ∃ root,
        I.ICEXT (v.iri (.rdf .rdfType)) (I.IS (v.iri (.rdf .rdfBag))).val root ∧
        ¬ Nonempty (Enumeration (fun y => I.Relates (I.IS (v.iri .member)).val root y)) := by
  obtain ⟨U, I, hI, hg, root, member, hb, _, hinj, hm⟩ := infinite_members_witness.{u} T D v h
  exact ⟨U, I, hI, hg, root, hb,
    Enumeration.no_enumeration_of_nat_injection _ member (fun n => (hm n).2) hinj⟩

end RDF11.ContainerInfinitude
