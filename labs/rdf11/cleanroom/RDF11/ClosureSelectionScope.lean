/-
Appendix A: the printed E-only container-axiom selection, held fixed.
The premise uses rdf:_17 and the conclusion uses rdfs:member. A rule-closed
syntactic overapproximation proves absence from the selected closure. It is
not a full RDFS model and does not replace the separate consistency witness.
-/
import RDF11.ClosureSelectionFrame
import RDF11.ContainerEntailment
import RDF11.RDFSFreeProperties
import RDF11.Interpolation

namespace RDF11.ClosureSelection

abbrev Iri := Sum RDFSSymbol Bool

def vocabulary : RDFSVocabulary Iri where
  iri := Sum.inl
  distinct := fun _ _ h => Sum.inl.inj h

def schemaTag : RDFSSymbol → Tag
  | .rdf .rdfType => .typing
  | .subClassOf => .subclass
  | .subPropertyOf => .subproperty
  | .member => .member
  | .domain | .range => .domainRange
  | .containerMembershipProperty => .cmp
  | .rdf (.container 0) => .selected
  | .rdf (.container (_ + 1)) => .free
  | .rdf .rdfSubject | .rdf .rdfPredicate | .rdf .rdfObject
  | .rdf .rdfFirst | .rdf .rdfRest | .rdf .rdfValue
  | .seeAlso | .isDefinedBy | .comment | .label => .free
  | _ => .top

def iriTag : Iri → Tag
  | .inl s => schemaTag s
  | .inr _ => .user

def termTag : Term Iri Literal B → Tag
  | .iri i => iriTag i
  | .literal _ | .blank _ => .invalid

def Supported (t : GeneralizedTriple Iri Literal B) : Prop :=
  holds (termTag t.subject) (termTag t.predicate) (termTag t.object)

theorem schema_valid (s : RDFSSymbol) : schemaTag s ≠ .invalid := by
  cases s with
  | rdf r => cases r <;> simp [schemaTag]; rename_i n; cases n <;> simp
  | _ => simp [schemaTag]

def subject : Iri := .inr false
def object : Iri := .inr true

def premiseTriple : Triple Iri Literal B :=
  ⟨.iri subject, vocabulary.iri (.rdf (.container 16)), .iri object⟩

def conclusionTriple : Triple Iri Literal B :=
  ⟨.iri subject, vocabulary.iri .member, .iri object⟩

def premise : Graph Iri Literal B := Set.singleton premiseTriple
def conclusion : Graph Iri Literal B := Set.singleton conclusionTriple

theorem premise_supported : Set.subset (premise : Graph Iri Literal B).generalize Supported := by
  rintro _ ⟨_, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem conclusion_unsupported : ¬ Supported (conclusionTriple : Triple Iri Literal B).generalize :=
  fun h => h

theorem rdf_step_closed (T : DatatypeTheory Iri Literal Value)
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H Supported)
    (h : RDFStep T vocabulary.toRDF.baseDatatypes vocabulary.toRDF H t) : Supported t := by
  cases h with
  | rdfD2 t ht => exact type_top (predicate_valid (hH t ht))
  | GrdfD1 s p l ht _ => exact False.elim ((object_valid (hH _ ht)) rfl)

theorem rdfs_step_closed (T : DatatypeTheory Iri Literal Value)
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H Supported)
    (h : RDFSStep T vocabulary.toRDF.baseDatatypes vocabulary H t) : Supported t := by
  cases h with
  | rdfs1 a ha =>
    rcases ha with rfl | rfl
    · exact type_top (schema_valid (.rdf .rdfLangString))
    · exact type_top (schema_valid (.rdf .xsdString))
  | rdfs2 p c s o hd ht => exact domain_closed (hH _ hd) (hH _ ht)
  | rdfs3 p c s o hd ht => exact range_closed (hH _ hd) (hH _ ht)
  | rdfs4a s p o ht =>
    have h := hH _ ht
    exact type_top (subject_valid h)
  | rdfs4b s p o ht =>
    have h := hH _ ht
    exact type_top (object_valid h)
  | rdfs5 p q r hpq hqr =>
    have h₁ := hH _ hpq
    have h₂ := hH _ hqr
    exact subproperty_trans h₁ h₂
  | rdfs6 p hp =>
    have h := hH _ hp
    exact subproperty_refl (subject_valid h)
  | rdfs7 p q s o hpq ht => exact subproperty_use (hH _ hpq) (hH _ ht)
  | rdfs8 c hc =>
    have h := hH _ hc
    exact subclass_top (subject_valid h)
  | rdfs9 c d x hcd hx => exact subclass_use (hH _ hcd) (hH _ hx)
  | rdfs10 c hc =>
    have h := hH _ hc
    exact subclass_refl (subject_valid h)
  | rdfs11 c d e hcd hde =>
    have h₁ := hH _ hcd
    have h₂ := hH _ hde
    exact subclass_trans h₁ h₂
  | rdfs12 p hp => exact container_subproperty (hH _ hp)
  | rdfs13 c hc =>
    have h := hH _ hc
    exact subclass_top (subject_valid h)

theorem step_closed (T : DatatypeTheory Iri Literal Value)
    (H : GeneralizedGraph Iri Literal B) (hH : Set.subset H Supported)
    (h : RDFSGeneralizedStep T vocabulary.toRDF.baseDatatypes vocabulary H t) : Supported t :=
  h.elim (rdf_step_closed T H hH) (rdfs_step_closed T H hH)

theorem rdf_axioms_supported :
    Set.subset (vocabulary.toRDF.axioms : GeneralizedGraph Iri Literal B) Supported := by
  intro t ht
  rcases ht with ⟨p, _, rfl⟩ | rfl
  · exact type_top (schema_valid (.rdf p))
  · exact type_top (schema_valid (.rdf .rdfNil))

theorem domain_axioms_supported : ∀ pair ∈ rdfsDomainAxioms,
    holds (schemaTag pair.1) .domainRange (schemaTag pair.2) := by
  simp [rdfsDomainAxioms, schemaTag, holds]

theorem range_axioms_supported : ∀ pair ∈ rdfsRangeAxioms,
    holds (schemaTag pair.1) .domainRange (schemaTag pair.2) := by
  simp [rdfsRangeAxioms, schemaTag, holds]

theorem hierarchy_axioms_supported : ∀ t ∈ rdfsHierarchyAxioms,
    holds (schemaTag t.1) (schemaTag t.2.1) (schemaTag t.2.2) := by
  simp [rdfsHierarchyAxioms, schemaTag, holds]

def containerTyping (n : Nat) : GeneralizedTriple Iri Literal B :=
  ⟨.iri (vocabulary.iri (.rdf (.container n))), .iri (vocabulary.iri (.rdf .rdfType)),
    .iri (vocabulary.iri .containerMembershipProperty)⟩

theorem rdfs_axioms_supported_or_container (t : GeneralizedTriple Iri Literal B)
    (ht : vocabulary.axioms t) : Supported t ∨ ∃ n, t = containerTyping n := by
  obtain ⟨s, p, o, ha, rfl⟩ := ht
  rcases ha with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha | ⟨n, rfl, ha⟩
  · exact Or.inl (domain_axioms_supported (s, o) ha)
  · exact Or.inl (range_axioms_supported (s, o) ha)
  · exact Or.inl (hierarchy_axioms_supported (s, p, o) ha)
  · rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨n, rfl⟩
    · exact Or.inl ⟨schema_valid (.rdf (.container n)), rfl⟩
    · exact Or.inl ⟨schema_valid (.rdf (.container n)), rfl⟩

theorem containerTyping_names_iff (datatype : Literal → Iri) (n k : Nat) :
    (containerTyping n : GeneralizedTriple Iri Literal B).names datatype
      (.inl (vocabulary.iri (.rdf (.container k)))) ↔ n = k := by
  simp [containerTyping, GeneralizedTriple.names, Term.names, vocabulary, eq_comm]

theorem conclusion_has_no_container (datatype : Literal → Iri) (n : Nat) :
    ¬ (conclusion : Graph Iri Literal B).generalize.vocabulary datatype
      (.inl (vocabulary.iri (.rdf (.container n)))) := by
  rintro ⟨_, ⟨_, rfl, rfl⟩, hn⟩
  simp [conclusionTriple, Triple.generalize, Subject.toTerm, GeneralizedTriple.names,
    Term.names, vocabulary, subject, object] at hn

theorem noncontainer_axioms_supported (datatype : Literal → Iri) :
    Set.subset (NonContainerAxioms datatype (fun n => vocabulary.iri (.rdf (.container n)))
      (Set.union vocabulary.toRDF.axioms vocabulary.axioms))
      (Supported : GeneralizedGraph Iri Literal B) := by
  rintro t ⟨ha, hn⟩
  rcases ha with ha | ha
  · exact rdf_axioms_supported t ha
  · rcases rdfs_axioms_supported_or_container t ha with hs | ⟨n, rfl⟩
    · exact hs
    · exact False.elim (hn ⟨n, (containerTyping_names_iff datatype n n).mpr rfl⟩)

theorem fallback_axioms_supported (datatype : Literal → Iri) :
    Set.subset (ContainerAxioms datatype (fun n => vocabulary.iri (.rdf (.container n)))
      (Set.union vocabulary.toRDF.axioms vocabulary.axioms) 0)
      (Supported : GeneralizedGraph Iri Literal B) := by
  rintro t ⟨ha, hn⟩
  rcases ha with ha | ha
  · exact rdf_axioms_supported t ha
  · rcases rdfs_axioms_supported_or_container t ha with hs | ⟨n, rfl⟩
    · exact hs
    · have he := (containerTyping_names_iff datatype n 0).mp hn
      subst n
      exact ⟨schema_valid (.rdf (.container 0)), Or.inr ⟨rfl, rfl⟩⟩

theorem seed_supported (datatype : Literal → Iri) :
    Set.subset (AxiomSeed datatype (fun n => vocabulary.iri (.rdf (.container n)))
      (Set.union vocabulary.toRDF.axioms vocabulary.axioms)
      (premise : Graph Iri Literal B).generalize (conclusion : Graph Iri Literal B).generalize) Supported := by
  intro t ht
  rcases ht with hp | hn | ⟨n, he, _⟩ | ⟨_, hf⟩
  · exact premise_supported t hp
  · exact noncontainer_axioms_supported datatype t hn
  · exact False.elim (conclusion_has_no_container datatype n he)
  · exact fallback_axioms_supported datatype t hf

theorem closure_supported (T : DatatypeTheory Iri Literal Value) :
    Set.subset (RDFSClosure T vocabulary
      (premise : Graph Iri Literal B).generalize (conclusion : Graph Iri Literal B).generalize) Supported :=
  ruleDerives_least _ _ _ (seed_supported T.literalSyntax.datatype)
    (fun H _ hH h => step_closed T H hH h)

theorem conclusion_absent (T : DatatypeTheory Iri Literal Value) :
    ¬ RDFSClosure T vocabulary (premise : Graph Iri Literal B).generalize
      (conclusion : Graph Iri Literal B).generalize conclusionTriple.generalize :=
  fun h => conclusion_unsupported (closure_supported T _ h)

theorem conclusion_ground : (conclusion : Graph Iri Literal B).generalize.ground := by
  rintro b ⟨_, ⟨_, rfl, rfl⟩, hb⟩
  exact hb.elim id (fun h => h.elim id id)

theorem closure_not_simply_entails (T : DatatypeTheory Iri Literal Value) :
    ¬ SimplyEntails.{u} (RDFSClosure T vocabulary
      (premise : Graph Iri Literal B).generalize (conclusion : Graph Iri Literal B).generalize) (conclusion : Graph Iri Literal B).generalize := by
  intro h
  exact conclusion_absent T ((ground_entailment_iff_subset _ _ conclusion_ground).mp h
    conclusionTriple.generalize ⟨conclusionTriple, rfl, rfl⟩)

theorem closure_has_no_conclusion_instance (T : DatatypeTheory Iri Literal Value)
    (μ : Substitution Iri Literal B) :
    ¬ Set.subset ((conclusion : Graph Iri Literal B).generalize.substitute μ)
      (RDFSClosure T vocabulary premise.generalize (conclusion : Graph Iri Literal B).generalize) := by
  rw [ground_substitute _ conclusion_ground μ]
  intro h
  exact conclusion_absent T (h conclusionTriple.generalize ⟨conclusionTriple, rfl, rfl⟩)

theorem full_entailment (T : DatatypeTheory Iri Literal Value) :
    RDFSEntails.{u} T vocabulary.toRDF.baseDatatypes vocabulary
      (premise : Graph Iri Literal B).generalize (conclusion : Graph Iri Literal B).generalize := by
  have h := container_membership_entailment.{u} T vocabulary.toRDF.baseDatatypes vocabulary
    (premise : Graph Iri Literal B).generalize (.iri subject) (.iri object) 16
    ⟨premiseTriple, rfl, rfl⟩
  have he : (conclusion : Graph Iri Literal B).generalize =
      Set.singleton ⟨.iri subject, .iri (vocabulary.iri .member), .iri object⟩ := by
    apply Set.ext
    intro t
    exact ⟨fun ⟨_, rfl, ht⟩ => ht.symm, fun ht => ⟨conclusionTriple, rfl, ht.symm⟩⟩
  rw [he]
  exact h

theorem premise_consistent (T : DatatypeTheory Iri Literal Value)
    (h : RDFSModelConstruction.Parameters T vocabulary.toRDF.baseDatatypes vocabulary) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T vocabulary.toRDF.baseDatatypes vocabulary ∧
      I.Satisfies (premise : Graph Iri Literal B).generalize := by
  let Q : RDFModelConstruction.Carrier.{u} Iri Value →
      RDFModelConstruction.Carrier.{u} Iri Value →
      RDFModelConstruction.Carrier.{u} Iri Value → Prop := fun _ _ _ => True
  let I := RDFSModelConstruction.interpretation T vocabulary.toRDF.baseDatatypes vocabulary Q
  refine ⟨_, I, RDFSModelConstruction.model T _ vocabulary h Q, ?_⟩
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨fun _ => none, ?_⟩
  rintro _ ⟨_, rfl, rfl⟩
  apply (I.iri_triple_true _ _ _ _).mpr
  exact (RDFSModelConstruction.relates_free T _ vocabulary h Q (.rdf (.container 16))
    (by simp [RDFSModelConstruction.SchemaSymbol])
    (by simp [RDFSModelConstruction.FreeProperty]) _ _).mpr True.intro

end RDF11.ClosureSelection
