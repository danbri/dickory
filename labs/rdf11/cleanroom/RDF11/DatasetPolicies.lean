/-
RDF 1.1 Semantics §10 permits dataset content policies and semantic extensions;
it does not specify a unique dataset satisfaction/entailment relation.
These interfaces make a chosen policy and its assumptions explicit.
The default-content recommendation is represented by IncludesDefault, which
is not imposed on every DatasetRegime. Model may itself encode a modal system.
-/
import RDF11.DatasetIsomorphism

namespace RDF11

structure DatasetRegime (Iri Literal B : Type) (Model : Type u) where
  Satisfies : Model → Dataset Iri Literal B → Prop

namespace DatasetRegime

def Entails (P : DatasetRegime Iri Literal B Model)
    (D E : Dataset Iri Literal B) : Prop :=
  ∀ m, P.Satisfies m D → P.Satisfies m E

def EntailsUnder (P : DatasetRegime Iri Literal B Model) (models : Set Model)
    (D E : Dataset Iri Literal B) : Prop :=
  ∀ m, models m → P.Satisfies m D → P.Satisfies m E

theorem entails_refl (P : DatasetRegime Iri Literal B Model) (D : Dataset Iri Literal B) :
    P.Entails D D := fun _ h => h

theorem entails_trans (P : DatasetRegime Iri Literal B Model)
    {D E F : Dataset Iri Literal B} (hDE : P.Entails D E) (hEF : P.Entails E F) :
    P.Entails D F := fun m h => hEF m (hDE m h)

theorem restrict_entailment (P : DatasetRegime Iri Literal B Model) (models : Set Model)
    {D E : Dataset Iri Literal B} (h : P.Entails D E) : P.EntailsUnder models D E :=
  fun m _ => h m

theorem stronger_models_preserve_entailment (P : DatasetRegime Iri Literal B Model)
    {C D : Set Model} (hDC : Set.subset D C) {S E : Dataset Iri Literal B}
    (h : P.EntailsUnder C S E) : P.EntailsUnder D S E :=
  fun m hm => h m (hDC m hm)

def restricted (P : DatasetRegime Iri Literal B Model) (models : Set Model) :
    DatasetRegime Iri Literal B {m : Model // models m} where
  Satisfies := fun m D => P.Satisfies m.val D

theorem restricted_entails_iff (P : DatasetRegime Iri Literal B Model) (models : Set Model)
    (D E : Dataset Iri Literal B) :
    (P.restricted models).Entails D E ↔ P.EntailsUnder models D E :=
  ⟨fun h m hm => h ⟨m, hm⟩, fun h m => h m.val m.property⟩

/-- A designated graph interpretation may be a component of a larger model. -/
def IncludesDefault (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m)) : Prop :=
  ∀ m D, P.Satisfies m D → (I m).Satisfies D.defaultGraph.generalize

def EntailsGraph (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m))
    (D : Dataset Iri Literal B) (G : GeneralizedGraph Iri Literal C) : Prop :=
  ∀ m, P.Satisfies m D → (I m).Satisfies G

theorem default_content (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m))
    (h : P.IncludesDefault U I) (D : Dataset Iri Literal B) :
    P.EntailsGraph U I D D.defaultGraph.generalize := fun m => h m D

theorem default_graph_consequence (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m))
    (h : P.IncludesDefault U I) (D : Dataset Iri Literal B)
    (G : GeneralizedGraph Iri Literal C) (hG : SimplyEntails.{v} D.defaultGraph.generalize G) :
    P.EntailsGraph U I D G := fun m hm => hG (U m) (I m) (h m D hm)

theorem default_graph_consequence_under (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m))
    (h : P.IncludesDefault U I)
    (C : ∀ (V : Type v), SimpleInterpretation Iri Literal V → Prop)
    (hC : ∀ m, C (U m) (I m)) (D : Dataset Iri Literal B)
    (G : GeneralizedGraph Iri Literal A) (hG : RDF11.EntailsUnder C D.defaultGraph.generalize G) :
    P.EntailsGraph U I D G := fun m hm => hG (U m) (I m) (hC m) (h m D hm)

theorem graph_consequence_composition (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m))
    (D : Dataset Iri Literal B) (G : GeneralizedGraph Iri Literal A)
    (H : GeneralizedGraph Iri Literal C) (hG : P.EntailsGraph U I D G)
    (hGH : SimplyEntails.{v} G H) : P.EntailsGraph U I D H :=
  fun m hm => hGH (U m) (I m) (hG m hm)

theorem restriction_includes_default (P : DatasetRegime Iri Literal B Model)
    (U : Model → Type v) (I : (m : Model) → SimpleInterpretation Iri Literal (U m))
    (h : P.IncludesDefault U I) (models : Set Model) :
    (P.restricted models).IncludesDefault (fun m => U m.val) (fun m => I m.val) :=
  fun m D => h m.val D

/-- One chosen policy: only the default graph supplies content. -/
def simpleDefault : DatasetRegime Iri Literal B
    (Sigma fun U : Type u => SimpleInterpretation Iri Literal U) where
  Satisfies := fun m D => m.2.Satisfies D.defaultGraph.generalize

theorem simpleDefault_includes_default :
    (simpleDefault : DatasetRegime Iri Literal B _).IncludesDefault
      (fun m => m.1) (fun m => m.2) := fun _ _ h => h

theorem simpleDefault_entails_iff (D E : Dataset Iri Literal B) :
    (simpleDefault.{u}).Entails D E ↔
      SimplyEntails.{u} D.defaultGraph.generalize E.defaultGraph.generalize :=
  ⟨fun h U I => h ⟨U, I⟩, fun h m => h m.1 m.2⟩

theorem simpleDefault_isomorphism_invariant {D E : Dataset Iri Literal B}
    (e : DatasetIsomorphism D E)
    (m : Sigma fun U : Type u => SimpleInterpretation Iri Literal U) :
    simpleDefault.Satisfies m D ↔ simpleDefault.Satisfies m E :=
  e.default_isomorphism.satisfies_iff m.2

/-- The same chosen default-only policy over an explicitly selected graph regime. -/
def defaultUnder (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop) :
    DatasetRegime Iri Literal B
      {m : Sigma fun U : Type u => SimpleInterpretation Iri Literal U // C m.1 m.2} :=
  simpleDefault.restricted (fun m => C m.1 m.2)

theorem defaultUnder_entails_iff
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    (D E : Dataset Iri Literal B) :
    (defaultUnder C).Entails D E ↔ RDF11.EntailsUnder C D.defaultGraph.generalize E.defaultGraph.generalize :=
  ⟨fun h U I hC => h ⟨⟨U, I⟩, hC⟩, fun h m => h m.val.1 m.val.2 m.property⟩

theorem defaultUnder_includes_default
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop) :
    (defaultUnder C : DatasetRegime Iri Literal B _).IncludesDefault
      (fun m => m.val.1) (fun m => m.val.2) := fun _ _ h => h

theorem defaultUnder_isomorphism_invariant
    (C : ∀ (U : Type u), SimpleInterpretation Iri Literal U → Prop)
    {D E : Dataset Iri Literal B} (e : DatasetIsomorphism D E)
    (m : {m : Sigma fun U : Type u => SimpleInterpretation Iri Literal U // C m.1 m.2}) :
    (defaultUnder C).Satisfies m D ↔ (defaultUnder C).Satisfies m E :=
  e.default_isomorphism.satisfies_iff m.val.2

end DatasetRegime

/-- A truth-preserving map from models of a chosen new regime into an old one. -/
structure DatasetModelMap (P : DatasetRegime Iri Literal B M)
    (Q : DatasetRegime Iri Literal B N) where
  toModel : N → M
  truth_iff : ∀ m D, Q.Satisfies m D ↔ P.Satisfies (toModel m) D

theorem DatasetModelMap.preserves_entailment {P : DatasetRegime Iri Literal B M}
    {Q : DatasetRegime Iri Literal B N} (f : DatasetModelMap P Q)
    {D E : Dataset Iri Literal B} (h : P.Entails D E) : Q.Entails D E :=
  fun m hm => (f.truth_iff m E).mpr (h (f.toModel m) ((f.truth_iff m D).mp hm))

end RDF11
