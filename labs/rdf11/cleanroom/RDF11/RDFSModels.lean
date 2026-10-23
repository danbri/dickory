/-
RDF 1.1 Semantics §9: build every RDFS condition, including the full axiom
families, over the existing RDF model. The interpretation is a sufficient
witness family; it is not a characterization of all RDFS models or graphs.
-/
import RDF11.RDFSModelRelations

namespace RDF11
namespace RDFSModelConstruction

open RDFModelConstruction

theorem domain_targets : ∀ pair ∈ rdfsDomainAxioms, SchemaSymbol pair.2 := by
  simp [rdfsDomainAxioms, SchemaSymbol]

theorem range_targets : ∀ pair ∈ rdfsRangeAxioms, SchemaSymbol pair.2 := by
  simp [rdfsRangeAxioms, SchemaSymbol]

theorem hierarchy_cases : ∀ t ∈ rdfsHierarchyAxioms,
    (t.2.1 = .subClassOf ∧ SchemaSymbol t.2.2) ∨
      (t.1 = .isDefinedBy ∧ t.2.1 = .subPropertyOf ∧ t.2.2 = .seeAlso) := by
  simp [rdfsHierarchyAxioms, SchemaSymbol]

theorem axioms (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    (interpretation T D v Q).GraphTrue (fun (_ : Empty) => none) v.axioms := by
  let I := interpretation T D v Q
  have hd (s o : Iri) (ho : NameObject (I.IS o).val) :
      I.Relates (I.IS (v.iri .domain)).val (I.IS s).val (I.IS o).val :=
    (relates_domain T D v h Q _ _).mpr ho
  have hr (s o : Iri) (ho : NameObject (I.IS o).val) :
      I.Relates (I.IS (v.iri .range)).val (I.IS s).val (I.IS o).val :=
    (relates_range T D v h Q _ _).mpr ho
  have hn (o : RDFSSymbol) (ho : SchemaSymbol o) : NameObject (I.IS (v.iri o)).val := by
    rw [schema_denotation T D v h Q o ho]
    exact ⟨v.iri o, rfl⟩
  have hc (s o : RDFSSymbol) (ho : SchemaSymbol o) :
      I.Relates (I.IS (v.iri .subClassOf)).val (I.IS (v.iri s)).val (I.IS (v.iri o)).val := by
    apply (relates_subclass T D v h Q _ _).mpr
    intro z _
    exact (icext_iff T D v h Q _ _).mp (named_column T D v h Q o ho z)
  rintro t ⟨s, p, o, ha, rfl⟩
  apply (I.iri_triple_true _ _ _ _).mpr
  rcases ha with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha | ⟨n, rfl, ha⟩
  · exact hd _ _ (hn o (domain_targets (s, o) ha))
  · exact hr _ _ (hn o (range_targets (s, o) ha))
  · have hh := hierarchy_cases (s, p, o) ha
    rcases hh with ⟨rfl, ho⟩ | ⟨rfl, rfl, rfl⟩
    · exact hc _ _ ho
    · apply (relates_subproperty T D v h Q _ _).mpr
      rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol]),
        schema_denotation T D v h Q _ (by simp [SchemaSymbol])]
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact named_column T D v h Q .containerMembershipProperty (by simp [SchemaSymbol]) _
    · exact hd _ _ (hn .resource (by simp [SchemaSymbol]))
    · exact hr _ _ (hn .resource (by simp [SchemaSymbol]))

theorem language_extension (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop)
    (x : Carrier.{u} Iri Value) :
    (interpretation T D v Q).ICEXT (v.iri (.rdf .rdfType))
      ((interpretation T D v Q).IS (v.iri (.rdf .rdfLangString))).val x ↔
    ∃ l tag, T.literalSyntax.language l = some tag ∧
      ∃ r : (interpretation T D v Q).Resource,
        (interpretation T D v Q).IL l = some r ∧ r.val = x := by
  let I := interpretation T D v Q
  have hR := RDFModelConstruction.conditions.{u} T D v.toRDF h.toRDF (relation T v Q)
  have hd : D T.literalSyntax.langString := h.language_iri ▸ h.recognize_language
  constructor
  · intro hx
    obtain ⟨w, hw, hwx⟩ := (hR.datatype_extension _ h.recognize_language x).mp hx
    have hwl : T.languageSpace w := by
      simpa [← h.language_iri, T.recognizedSpace_language] using hw
    obtain ⟨l, tag, ht, he⟩ := h.language_coverage w hwl
    obtain ⟨r, hr, hv⟩ := hR.datatypes.language l tag hd ht
    have hv' : realization.value w = some r.val := by simpa [he] using hv
    exact ⟨l, tag, ht, r, hr, Option.some.inj (hv'.symm.trans hwx)⟩
  · rintro ⟨l, tag, ht, r, hr, rfl⟩
    have hl : T.literalSyntax.datatype l = v.iri (.rdf .rdfLangString) :=
      ((T.literalSyntax.tagged_iff l).mp ⟨tag, ht⟩).trans h.language_iri
    have hdl : D (T.literalSyntax.datatype l) := hl ▸ h.recognize_language
    have hv := I.rdf_literal_typing hR hdl r hr
    simpa only [hl, I, SimpleInterpretation.ICEXT, RDFSVocabulary.toRDF] using hv

theorem conditions (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    (interpretation T D v Q).RDFSConditions T D v realization := by
  let I := interpretation T D v Q
  refine {
    rdf := RDFModelConstruction.conditions T D v.toRDF h.toRDF (relation T v Q)
    resource_extension := ?_
    language_extension := language_extension T D v h Q
    datatype_typing := ?_
    domain := ?_
    range := ?_
    subproperty_transitive := ?_
    subproperty_reflexive := ?_
    subproperty_endpoints := ?_
    subproperty_inclusion := ?_
    class_resource := ?_
    subclass_transitive := ?_
    subclass_reflexive := ?_
    subclass_endpoints := ?_
    subclass_inclusion := ?_
    container_subproperty := ?_
    datatype_subclass := ?_
    axioms := axioms T D v h Q
  }
  · intro x
    exact ⟨fun _ => True.intro, fun _ => named_column T D v h Q .resource (by simp [SchemaSymbol]) x⟩
  · intro a _
    exact named_column T D v h Q .datatype (by simp [SchemaSymbol]) _
  · intro p c x y hpc _
    obtain ⟨a, rfl⟩ := (relates_domain T D v h Q _ _).mp hpc
    apply (icext_iff T D v h Q _ _).mpr
    trivial
  · intro p c x y hpc _
    obtain ⟨a, rfl⟩ := (relates_range T D v h Q _ _).mp hpc
    apply (icext_iff T D v h Q _ _).mpr
    trivial
  · intro x y z hxy hyz
    exact (relates_subproperty T D v h Q x z).mpr (subproperty_transitive v x y z
      ((relates_subproperty T D v h Q x y).mp hxy) ((relates_subproperty T D v h Q y z).mp hyz))
  · intro x _
    exact (relates_subproperty T D v h Q x x).mpr (Or.inl rfl)
  · intro _ _ _
    exact ⟨True.intro, True.intro⟩
  · intro x y hxy a b hx
    exact subproperty_inclusion T D v Q x y ((relates_subproperty T D v h Q x y).mp hxy) a b hx
  · intro x _
    apply (relates_subclass T D v h Q _ _).mpr
    intro z _
    exact (icext_iff T D v h Q _ _).mp (named_column T D v h Q .resource (by simp [SchemaSymbol]) z)
  · intro x y z hxy hyz
    apply (relates_subclass T D v h Q _ _).mpr
    intro w hw
    exact ((relates_subclass T D v h Q _ _).mp hyz) w
      (((relates_subclass T D v h Q _ _).mp hxy) w hw)
  · intro x _
    exact (relates_subclass T D v h Q x x).mpr (fun _ hx => hx)
  · intro x y _
    exact ⟨all_classes T D v h Q x, all_classes T D v h Q y⟩
  · intro x y hxy z hz
    exact (icext_iff T D v h Q z y).mpr (((relates_subclass T D v h Q x y).mp hxy) z
      ((icext_iff T D v h Q z x).mp hz))
  · intro x _
    apply (relates_subproperty T D v h Q _ _).mpr
    rw [schema_denotation T D v h Q _ (by simp [SchemaSymbol])]
    exact Or.inr (Or.inl rfl)
  · intro x _
    apply (relates_subclass T D v h Q _ _).mpr
    intro z _
    exact (icext_iff T D v h Q _ _).mp (named_column T D v h Q .literal (by simp [SchemaSymbol]) z)

theorem model (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v)
    (Q : Carrier.{u} Iri Value → Carrier.{u} Iri Value → Carrier.{u} Iri Value → Prop) :
    (interpretation T D v Q).RDFSModel T D v := ⟨realization, conditions T D v h Q⟩

theorem base_parameters (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (hlang : T.literalSyntax.langString = v.iri (.rdf .rdfLangString))
    (hcoverage : LanguageCoverage T) : Parameters T v.toRDF.baseDatatypes v := by
  refine ⟨hlang, Or.inl rfl, Or.inr rfl, ?_, hcoverage⟩
  intro s hs ha
  rcases ha with ha | ha
  · exact hs.1 (v.distinct _ _ ha)
  · exact hs.2 (v.distinct _ _ ha)

theorem empty_satisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (h : Parameters T D v) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T D v ∧ I.Satisfies (Set.empty : GeneralizedGraph Iri Literal B) := by
  let I := interpretation.{u} T D v (fun _ _ _ => False)
  exact ⟨Carrier Iri Value, I, model T D v h _, I.satisfies_empty⟩

theorem base_empty_satisfiable (T : DatatypeTheory Iri Literal Value) (v : RDFSVocabulary Iri)
    (hlang : T.literalSyntax.langString = v.iri (.rdf .rdfLangString))
    (hcoverage : LanguageCoverage T) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T v.toRDF.baseDatatypes v ∧
      I.Satisfies (Set.empty : GeneralizedGraph Iri Literal B) :=
  empty_satisfiable T v.toRDF.baseDatatypes v (base_parameters T v hlang hcoverage)

/-- For the base recognition set, coverage is both necessary and sufficient for
inhabitation of the current full RDFS model class, with names aligned. -/
theorem base_model_exists_iff_language_coverage (T : DatatypeTheory Iri Literal Value)
    (v : RDFSVocabulary Iri) (hlang : T.literalSyntax.langString = v.iri (.rdf .rdfLangString)) :
    (∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T v.toRDF.baseDatatypes v) ↔ LanguageCoverage T := by
  constructor
  · rintro ⟨U, I, hI⟩ w hw
    exact I.rdfsModel_language_literal_coverage hI w hw
  · intro hcoverage
    obtain ⟨U, I, hI, _⟩ := base_empty_satisfiable.{u} (B := Empty) T v hlang hcoverage
    exact ⟨U, I, hI⟩

end RDFSModelConstruction
end RDF11
