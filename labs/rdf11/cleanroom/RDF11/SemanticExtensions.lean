/-
RDF 1.1 Semantics §§3 and 5: semantic extensions retain simple truth conditions,
add model conditions, and may restrict graph syntax. This construction uses
ordinary RDF graphs, so an extension's legal predicate adds to RDF's syntax.
Admissibility is required before forming an entailment judgement; rejection is
not identified with semantic falsity. No syntax validator or decision procedure
is assumed. This is a sufficient construction, not a classification of OWL or
all possible enriched/modal semantic frameworks.
-/
import RDF11.RDFS
import RDF11.Transformations

namespace RDF11

structure SemanticExtension.{u} (Iri Literal : Type) where
  legal : ∀ {B : Type}, Graph Iri Literal B → Prop
  conditions : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop

namespace SemanticExtension

variable {Iri Literal : Type}

abbrev AdmissibleGraph (R : SemanticExtension.{u} Iri Literal) (B : Type) :=
  {G : Graph Iri Literal B // R.legal G}

abbrev Model (R : SemanticExtension.{u} Iri Literal) (U : Type u) :=
  {I : SimpleInterpretation Iri Literal U // R.conditions U I}

def Satisfies (R : SemanticExtension.{u} Iri Literal) (I : R.Model U)
    (G : R.AdmissibleGraph B) : Prop := I.val.Satisfies G.val.generalize

theorem satisfies_iff (R : SemanticExtension.{u} Iri Literal) (I : R.Model U)
    (G : R.AdmissibleGraph B) : R.Satisfies I G ↔ I.val.Satisfies G.val.generalize := Iff.rfl

def Entails (R : SemanticExtension.{u} Iri Literal)
    (G : R.AdmissibleGraph B₁) (E : R.AdmissibleGraph B₂) : Prop :=
  ∀ (U : Type u) (I : R.Model U), R.Satisfies I G → R.Satisfies I E

theorem entails_iff (R : SemanticExtension.{u} Iri Literal)
    (G : R.AdmissibleGraph B₁) (E : R.AdmissibleGraph B₂) :
    R.Entails G E ↔ EntailsUnder R.conditions G.val.generalize E.val.generalize := by
  constructor
  · exact fun h U I hI => h U ⟨I, hI⟩
  · exact fun h U I => h U I.val I.property

theorem preserves_simple (R : SemanticExtension.{u} Iri Literal)
    (G : R.AdmissibleGraph B₁) (E : R.AdmissibleGraph B₂)
    (h : SimplyEntails.{u} G.val.generalize E.val.generalize) : R.Entails G E :=
  (R.entails_iff G E).mpr (extension_preserves_simple_entailment R.conditions h)

theorem entails_refl (R : SemanticExtension.{u} Iri Literal) (G : R.AdmissibleGraph B) :
    R.Entails G G := fun _ _ h => h

theorem entails_trans (R : SemanticExtension.{u} Iri Literal)
    {G : R.AdmissibleGraph B₁} {H : R.AdmissibleGraph B₂} {E : R.AdmissibleGraph B₃}
    (hGH : R.Entails G H) (hHE : R.Entails H E) : R.Entails G E :=
  fun U I hG => hHE U I (hGH U I hG)

theorem subgraph_entails (R : SemanticExtension.{u} Iri Literal)
    (G E : R.AdmissibleGraph B) (h : Set.subset E.val G.val) : R.Entails G E := by
  apply R.preserves_simple
  apply subgraph_entailment
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, h t ht, rfl⟩

theorem premise_monotone (R : SemanticExtension.{u} Iri Literal)
    (G H : R.AdmissibleGraph B₁) (E : R.AdmissibleGraph B₂)
    (hGH : Set.subset G.val H.val) (hGE : R.Entails G E) : R.Entails H E :=
  R.entails_trans (R.subgraph_entails H G hGH) hGE

def Satisfiable (R : SemanticExtension.{u} Iri Literal) (G : R.AdmissibleGraph B) : Prop :=
  ∃ (U : Type u) (I : R.Model U), R.Satisfies I G

theorem unsatisfiable_entails (R : SemanticExtension.{u} Iri Literal)
    (G : R.AdmissibleGraph B₁) (E : R.AdmissibleGraph B₂)
    (h : ¬ R.Satisfiable G) : R.Entails G E := fun U I hG => False.elim (h ⟨U, I, hG⟩)

/-- Refinement restricts legal graphs and models while keeping simple truth. -/
structure Refines (stronger weaker : SemanticExtension.{u} Iri Literal) : Prop where
  admissible : ∀ {B} (G : Graph Iri Literal B), stronger.legal G → weaker.legal G
  models : ∀ U I, stronger.conditions U I → weaker.conditions U I

def Refines.graph {S R : SemanticExtension.{u} Iri Literal} (h : S.Refines R)
    (G : S.AdmissibleGraph B) : R.AdmissibleGraph B := ⟨G.val, h.admissible G.val G.property⟩

theorem Refines.entailment {S R : SemanticExtension.{u} Iri Literal} (h : S.Refines R)
    (G : S.AdmissibleGraph B₁) (E : S.AdmissibleGraph B₂)
    (he : R.Entails (h.graph G) (h.graph E)) : S.Entails G E :=
  fun U I => he U ⟨I.val, h.models U I.val I.property⟩

theorem Refines.satisfiability {S R : SemanticExtension.{u} Iri Literal} (h : S.Refines R)
    (G : S.AdmissibleGraph B) (hg : S.Satisfiable G) : R.Satisfiable (h.graph G) := by
  obtain ⟨U, I, hI⟩ := hg
  exact ⟨U, ⟨I.val, h.models U I.val I.property⟩, hI⟩

theorem Refines.trans {S R Q : SemanticExtension.{u} Iri Literal}
    (hSR : S.Refines R) (hRQ : R.Refines Q) : S.Refines Q where
  admissible := fun G h => hRQ.admissible G (hSR.admissible G h)
  models := fun U I h => hRQ.models U I (hSR.models U I h)

def meet (R S : SemanticExtension.{u} Iri Literal) : SemanticExtension.{u} Iri Literal where
  legal := fun G => R.legal G ∧ S.legal G
  conditions := fun U I => R.conditions U I ∧ S.conditions U I

theorem meet_refines_left (R S : SemanticExtension.{u} Iri Literal) : (R.meet S).Refines R where
  admissible := fun _ h => h.1
  models := fun _ _ h => h.1

theorem meet_refines_right (R S : SemanticExtension.{u} Iri Literal) : (R.meet S).Refines S where
  admissible := fun _ h => h.2
  models := fun _ _ h => h.2

/-- No additional graph syntax restrictions beyond ordinary RDF syntax. -/
def ofConditions (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop) :
    SemanticExtension.{u} Iri Literal where
  legal := fun _ => True
  conditions := C

def ofConditions.graph (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    (G : Graph Iri Literal B) : (ofConditions C).AdmissibleGraph B := ⟨G, True.intro⟩

theorem ofConditions_entails_iff
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    (G : Graph Iri Literal B₁) (E : Graph Iri Literal B₂) :
    (ofConditions C).Entails (ofConditions.graph C G) (ofConditions.graph C E) ↔
      EntailsUnder C G.generalize E.generalize := (ofConditions C).entails_iff _ _

def simple : SemanticExtension.{u} Iri Literal := ofConditions (fun _ _ => True)

def datatypes (T : DatatypeTheory Iri Literal Value) (D : Set Iri) :
    SemanticExtension.{u} Iri Literal := ofConditions (fun _ I => I.DModel T D)

def rdf (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri) :
    SemanticExtension.{u} Iri Literal := ofConditions (fun _ I => I.RDFModel T D v)

def rdfs (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri) :
    SemanticExtension.{u} Iri Literal := ofConditions (fun _ I => I.RDFSModel T D v)

theorem simple_entails_iff (G : Graph Iri Literal B₁) (E : Graph Iri Literal B₂) :
    simple.{u}.Entails ⟨G, True.intro⟩ ⟨E, True.intro⟩ ↔ SimplyEntails.{u} G.generalize E.generalize := by
  constructor
  · exact fun h U I => h U ⟨I, True.intro⟩
  · exact fun h U I => h U I.val

theorem datatypes_entails_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : Graph Iri Literal B₁) (E : Graph Iri Literal B₂) :
    (datatypes.{u} T D).Entails ⟨G, True.intro⟩ ⟨E, True.intro⟩ ↔
      DEntails.{u} T D G.generalize E.generalize := (datatypes.{u} T D).entails_iff _ _

theorem rdf_entails_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFVocabulary Iri)
    (G : Graph Iri Literal B₁) (E : Graph Iri Literal B₂) :
    (rdf.{u} T D v).Entails ⟨G, True.intro⟩ ⟨E, True.intro⟩ ↔
      RDFEntails.{u} T D v G.generalize E.generalize := (rdf.{u} T D v).entails_iff _ _

theorem rdfs_entails_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri) (v : RDFSVocabulary Iri)
    (G : Graph Iri Literal B₁) (E : Graph Iri Literal B₂) :
    (rdfs.{u} T D v).Entails ⟨G, True.intro⟩ ⟨E, True.intro⟩ ↔
      RDFSEntails.{u} T D v G.generalize E.generalize := (rdfs.{u} T D v).entails_iff _ _

theorem refines_simple (R : SemanticExtension.{u} Iri Literal) : R.Refines simple where
  admissible := fun _ _ => True.intro
  models := fun _ _ _ => True.intro

theorem rdf_refines_datatypes (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFVocabulary Iri) : (rdf.{u} T D v).Refines (datatypes.{u} T D) where
  admissible := fun _ _ => True.intro
  models := fun _ I h => I.rdfModel_is_dModel h

theorem rdfs_refines_rdf (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) : (rdfs.{u} T D v).Refines (rdf T D v.toRDF) where
  admissible := fun _ _ => True.intro
  models := fun _ I h => I.rdfsModel_is_rdfModel h

theorem datatype_refinement (T : DatatypeTheory Iri Literal Value)
    {D E : Set Iri} (hDE : Set.subset D E) :
    (datatypes.{u} T E).Refines (datatypes T D) where
  admissible := fun _ _ => True.intro
  models := fun _ I h => I.dModel_restrict h hDE

theorem no_additional_syntax (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (v : RDFSVocabulary Iri) (G : Graph Iri Literal B) :
    simple.{u}.legal G ∧ (datatypes.{u} T D).legal G ∧
      (rdf.{u} T D v.toRDF).legal G ∧ (rdfs.{u} T D v).legal G :=
  ⟨True.intro, True.intro, True.intro, True.intro⟩

theorem datatypes_satisfiable_iff (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : Graph Iri Literal B) :
    (datatypes.{u} T D).Satisfiable ⟨G, True.intro⟩ ↔ DSatisfiable.{u} T D G.generalize := by
  constructor
  · rintro ⟨U, I, hI⟩
    exact ⟨U, I.val, I.property, hI⟩
  · rintro ⟨U, I, hD, hG⟩
    exact ⟨U, ⟨I, hD⟩, hG⟩

/-- Validity transports a process's legal input/output pairs, not an obligation
to run that process. No legal conclusion is inferred from its entailment alone. -/
theorem valid_process (R : SemanticExtension.{u} Iri Literal)
    (process : GeneralizedGraph Iri Literal B₁ → GeneralizedGraph Iri Literal B₂ → Prop)
    (h : SimplyValid.{u} process) (G : R.AdmissibleGraph B₁) (E : R.AdmissibleGraph B₂)
    (hp : process G.val.generalize E.val.generalize) : R.Entails G E :=
  R.preserves_simple G E (h G.val.generalize E.val.generalize hp)

end SemanticExtension
end RDF11
