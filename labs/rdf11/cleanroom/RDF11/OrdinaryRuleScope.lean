/-
RDF 1.1 Semantics Appendix A: the printed blank-predicate example.
The three ordinary premise triples entail the ordinary conclusion, but no
ordinary rule run detects it. The rule-correct generalized intermediate
retains ex:e; the source prints ex:c, recorded separately for review.
-/
import RDF11.OrdinaryRuleFrame
import RDF11.RDFSFreeProperties
import RDF11.Interpolation

namespace RDF11.OrdinaryRuleScope

def subpropertyTriple (b : B) : Triple Iri Literal B :=
  ⟨.iri (.inr .a), vocabulary.iri .subPropertyOf, .blank b⟩

def domainTriple (b : B) : Triple Iri Literal B :=
  ⟨.blank b, vocabulary.iri .domain, .iri (.inr .c)⟩

def assertionTriple : Triple Iri Literal B :=
  ⟨.iri (.inr .d), .inr .a, .iri (.inr .e)⟩

def conclusionTriple : Triple Iri Literal B :=
  ⟨.iri (.inr .d), vocabulary.iri (.rdf .rdfType), .iri (.inr .c)⟩

def premise (b : B) : Graph Iri Literal B :=
  Set.ofList [subpropertyTriple b, domainTriple b, assertionTriple]

def conclusion : Graph Iri Literal B := Set.singleton conclusionTriple

def intermediate (b : B) : GeneralizedTriple Iri Literal B :=
  ⟨.iri (.inr .d), .blank b, .iri (.inr .e)⟩

def printedIntermediate (b : B) : GeneralizedTriple Iri Literal B :=
  ⟨.iri (.inr .d), .blank b, .iri (.inr .c)⟩

theorem intermediate_not_printed (b : B) :
    (intermediate b : GeneralizedTriple Iri Literal B) ≠ printedIntermediate b := by
  intro h
  have he := congrArg GeneralizedTriple.object h
  cases he

theorem intermediate_not_ordinary (b : B) :
    ¬ (intermediate b : GeneralizedTriple Iri Literal B).Ordinary := by
  rintro ⟨t, ht⟩
  have hp := congrArg GeneralizedTriple.predicate ht
  cases hp

theorem premise_supported (b : B) :
    Set.subset (premise (Literal := Literal) b).generalize Supported := by
  rintro t ⟨q, hq, rfl⟩
  have hx : q = subpropertyTriple b ∨ q = domainTriple b ∨ q = assertionTriple := by
    simpa [premise, Set.ofList] using hq
  rcases hx with rfl | rfl | rfl
  · exact ⟨by change Tag.propertyA ≠ .invalid; decide,
      by change Tag.hidden ≠ .invalid; decide, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · exact ⟨by change Tag.hidden ≠ .invalid; decide, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl⟩

theorem conclusion_unsupported : ¬ Supported (conclusionTriple : Triple Iri Literal B).generalize :=
  fun h => Tag.noConfusion h.2

theorem seed_supported (T : DatatypeTheory Iri Literal Value) (b : B) :
    Set.subset (OrdinaryAxiomSeed T.literalSyntax.datatype
      (fun n => vocabulary.iri (.rdf (.container n)))
      (Set.union vocabulary.toRDF.axioms vocabulary.axioms)
      (premise b).generalize (conclusion : Graph Iri Literal B).generalize) Supported := by
  intro t ht
  rcases ordinaryAxiomSeed_subset _ _ _ _ _ t ht with hp | ha
  · exact premise_supported b t hp
  · exact ha.elim (rdf_axioms_supported t) (rdfs_axioms_supported t)

theorem ordinary_run_supported (T : DatatypeTheory Iri Literal Value) (b : B)
    (run : OrdinaryRDFSRun T vocabulary (premise b).generalize
      (conclusion : Graph Iri Literal B).generalize H) : Set.subset H Supported :=
  run_supported T (seed_supported T b) run

theorem ordinary_conclusion_absent (T : DatatypeTheory Iri Literal Value) (b : B)
    (run : OrdinaryRDFSRun T vocabulary (premise b).generalize
      (conclusion : Graph Iri Literal B).generalize H) : ¬ H conclusionTriple.generalize :=
  fun ht => conclusion_unsupported (ordinary_run_supported T b run _ ht)

theorem conclusion_ground : (conclusion : Graph Iri Literal B).generalize.ground := by
  rintro b ⟨_, ⟨_, rfl, rfl⟩, hb⟩
  exact hb.elim id (fun h => h.elim id id)

theorem ordinary_no_conclusion_instance (T : DatatypeTheory Iri Literal Value) (b : B)
    (run : OrdinaryRDFSRun T vocabulary (premise b).generalize
      (conclusion : Graph Iri Literal B).generalize H) (μ : Substitution Iri Literal B) :
    ¬ Set.subset ((conclusion : Graph Iri Literal B).generalize.substitute μ) H := by
  rw [ground_substitute _ conclusion_ground μ]
  intro h
  exact ordinary_conclusion_absent T b run (h _ ⟨conclusionTriple, rfl, rfl⟩)

theorem ordinary_not_simply_entails (T : DatatypeTheory Iri Literal Value) (b : B)
    (run : OrdinaryRDFSRun T vocabulary (premise b).generalize
      (conclusion : Graph Iri Literal B).generalize H) :
    ¬ SimplyEntails.{u} H (conclusion : Graph Iri Literal B).generalize := by
  intro h
  exact ordinary_conclusion_absent T b run
    ((ground_entailment_iff_subset _ _ conclusion_ground).mp h _ ⟨conclusionTriple, rfl, rfl⟩)

/-- All axioms, including every indexed container axiom, still cannot bridge
the ordinary-syntax obstruction. This stronger seed is not the printed seed. -/
theorem all_axioms_still_insufficient (T : DatatypeTheory Iri Literal Value) (b : B)
    (run : OrdinaryRun T vocabulary.toRDF.baseDatatypes vocabulary.toRDF
      (RDFSGeneralizedStep T vocabulary.toRDF.baseDatatypes vocabulary)
      (Set.union (premise b).generalize (Set.union vocabulary.toRDF.axioms vocabulary.axioms)) H) :
    ¬ H (conclusionTriple : Triple Iri Literal B).generalize := by
  apply fun ht => conclusion_unsupported (run_supported T ?_ run _ ht)
  intro t ht
  exact ht.elim (premise_supported b t) (fun ha => ha.elim (rdf_axioms_supported t) (rdfs_axioms_supported t))

/-- Least closure of ordinary conclusions with ALL axioms. It overapproximates
the printed axiom selection; no literal rule is enabled in this example. -/
def allAxiomOrdinaryClosure (T : DatatypeTheory Iri Literal Value) (b : B) :
    GeneralizedGraph Iri Literal B :=
  RuleDerives (fun H t => RDFSGeneralizedStep T vocabulary.toRDF.baseDatatypes vocabulary H t ∧ t.Ordinary)
    (Set.union (premise b).generalize (Set.union vocabulary.toRDF.axioms vocabulary.axioms))

theorem allAxiomOrdinaryClosure_supported (T : DatatypeTheory Iri Literal Value) (b : B) :
    Set.subset (allAxiomOrdinaryClosure T b) Supported := by
  apply ruleDerives_least
  · intro t ht
    exact ht.elim (premise_supported b t) (fun ha => ha.elim (rdf_axioms_supported t) (rdfs_axioms_supported t))
  · intro H t hH ht
    exact step_closed T H hH ht.1 ht.2

theorem closure_no_literal (T : DatatypeTheory Iri Literal Value) (b : B)
    (ht : allAxiomOrdinaryClosure T b t) (l : Literal) : ¬ t.hasLiteral l :=
  supported_no_literal (allAxiomOrdinaryClosure_supported T b t ht) l

theorem allAxiomOrdinaryClosure_not_entails (T : DatatypeTheory Iri Literal Value) (b : B) :
    ¬ SimplyEntails.{u} (allAxiomOrdinaryClosure T b) (conclusion : Graph Iri Literal B).generalize := by
  intro he
  have ht := (ground_entailment_iff_subset _ _ conclusion_ground).mp he _ ⟨conclusionTriple, rfl, rfl⟩
  exact conclusion_unsupported (allAxiomOrdinaryClosure_supported T b _ ht)

theorem rdfs7_step (T : DatatypeTheory Iri Literal Value) (b : B) :
    RDFSStep T vocabulary.toRDF.baseDatatypes vocabulary (premise b).generalize (intermediate b) := by
  apply RDFSStep.rdfs7 (T := T) (v := vocabulary) (.iri (.inr .a)) (.blank b) (.iri (.inr .d)) (.iri (.inr .e))
  · exact ⟨subpropertyTriple b, by simp [premise, Set.ofList], rfl⟩
  · exact ⟨assertionTriple, by simp [premise, Set.ofList], rfl⟩

theorem generalized_intermediate (T : DatatypeTheory Iri Literal Value) (b : B) :
    RDFSClosure T vocabulary (premise b).generalize (conclusion : Graph Iri Literal B).generalize
      (intermediate b) := by
  apply RuleDerives.rule (RDFSClosure T vocabulary (premise b).generalize conclusion.generalize)
    (fun _ h => h)
  apply Or.inr
  apply RDFSStep.rdfs7 (T := T) (v := vocabulary) (.iri (.inr .a)) (.blank b) (.iri (.inr .d)) (.iri (.inr .e))
  · exact .premise (Or.inl ⟨subpropertyTriple b, by simp [premise, Set.ofList], rfl⟩)
  · exact .premise (Or.inl ⟨assertionTriple, by simp [premise, Set.ofList], rfl⟩)

theorem generalized_conclusion (T : DatatypeTheory Iri Literal Value) (b : B) :
    RDFSClosure T vocabulary (premise b).generalize (conclusion : Graph Iri Literal B).generalize
      conclusionTriple.generalize := by
  apply RuleDerives.rule (RDFSClosure T vocabulary (premise b).generalize conclusion.generalize)
    (fun _ h => h)
  apply Or.inr
  apply RDFSStep.rdfs2 (T := T) (v := vocabulary) (.blank b) (.iri (.inr .c)) (.iri (.inr .d)) (.iri (.inr .e))
  · exact .premise (Or.inl ⟨domainTriple b, by simp [premise, Set.ofList], rfl⟩)
  · exact generalized_intermediate T b

theorem full_entailment (T : DatatypeTheory Iri Literal Value) (b : B) :
    RDFSEntails.{u} T vocabulary.toRDF.baseDatatypes vocabulary
      (premise b).generalize (conclusion : Graph Iri Literal B).generalize := by
  apply rdfs_closure_simple_check_sound
  apply subgraph_entailment
  rintro _ ⟨_, rfl, rfl⟩
  exact generalized_conclusion T b

theorem premise_consistent (T : DatatypeTheory Iri Literal Value) (b : B)
    (h : RDFSModelConstruction.Parameters T vocabulary.toRDF.baseDatatypes vocabulary) :
    ∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T vocabulary.toRDF.baseDatatypes vocabulary ∧ I.Satisfies (premise b).generalize := by
  let D := vocabulary.toRDF.baseDatatypes
  let Q : RDFModelConstruction.Carrier.{u} Iri Value →
      RDFModelConstruction.Carrier.{u} Iri Value → RDFModelConstruction.Carrier.{u} Iri Value → Prop :=
    fun _ _ _ => True
  let I := RDFSModelConstruction.interpretation T D vocabulary Q
  have unrecognized (user : UserName) : ¬ D (.inr user) := by
    simp [D, RDFVocabulary.baseDatatypes, RDFSVocabulary.toRDF, vocabulary]
  have names (user : UserName) : (I.IS (.inr user)).val = RDFModelConstruction.name (.inr user) :=
    RDFSModelConstruction.unrecognized_denotation T D vocabulary Q _ (unrecognized user)
  let A : I.Assignment B := fun _ => some ⟨(I.IS (.inr .a)).val, True.intro⟩
  refine ⟨_, I, RDFSModelConstruction.model T D vocabulary h Q, ?_⟩
  apply (I.satisfies_iff_exists_graphTrue _).mpr
  refine ⟨A, ?_⟩
  rintro t ⟨q, hq, rfl⟩
  have hx : q = subpropertyTriple b ∨ q = domainTriple b ∨ q = assertionTriple := by
    simpa [premise, Set.ofList] using hq
  rcases hx with rfl | rfl | rfl
  · apply I.tripleTrue_of_relates A _ (o := (I.IS (.inr .a)).val) rfl rfl rfl
    exact (RDFSModelConstruction.relates_subproperty T D vocabulary h Q _ _).mpr (Or.inl rfl)
  · apply I.tripleTrue_of_relates A _ (s := (I.IS (.inr .a)).val) rfl rfl rfl
    apply (RDFSModelConstruction.relates_domain T D vocabulary h Q _ _).mpr
    exact ⟨.inr .c, names .c⟩
  · apply (I.iri_triple_true A _ _ _).mpr
    rw [RDFSModelConstruction.relates_iff]
    change RDFSModelConstruction.relation T vocabulary Q (I.IS (.inr .a)).val _ _
    rw [names .a]
    simp [RDFSModelConstruction.relation, RDFSModelConstruction.schemaName,
      RDFModelConstruction.name, vocabulary, Q]

theorem ordinary_incompleteness (T : DatatypeTheory Iri Literal Value) (b : B)
    (h : RDFSModelConstruction.Parameters T vocabulary.toRDF.baseDatatypes vocabulary) :
    (∃ (U : Type u) (I : SimpleInterpretation Iri Literal U),
      I.RDFSModel T vocabulary.toRDF.baseDatatypes vocabulary ∧ I.Satisfies (premise b).generalize) ∧
    RDFSEntails.{u} T vocabulary.toRDF.baseDatatypes vocabulary
      (premise b).generalize (conclusion : Graph Iri Literal B).generalize ∧
    ∀ H, OrdinaryRDFSRun T vocabulary (premise b).generalize (conclusion : Graph Iri Literal B).generalize H →
      ∀ μ, ¬ Set.subset ((conclusion : Graph Iri Literal B).generalize.substitute μ) H :=
  ⟨premise_consistent T b h, full_entailment T b, fun _ run μ => ordinary_no_conclusion_instance T b run μ⟩

end RDF11.OrdinaryRuleScope
