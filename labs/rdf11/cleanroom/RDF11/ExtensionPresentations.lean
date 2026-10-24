/-
Supporting bridge for §§3 and 5. An enriched model may contain more data than
a simple interpretation. To reuse model-restriction results, exhibit a reduct
and prove exact RDF truth correspondence on admitted ordinary graphs. This
does not assume that arbitrary OWL, SPARQL or modal semantics supplies that
correspondence, nor does it cover a different graph language automatically.
-/
import RDF11.SemanticExtensions

namespace RDF11

structure ExtensionPresentation.{u, v} (Iri Literal : Type) where
  Models : (U : Type u) → Type v
  legal : ∀ {B : Type}, Graph Iri Literal B → Prop
  interpretation : ∀ U, Models U → SimpleInterpretation Iri Literal U
  truth : ∀ {B : Type} U, Models U → Graph Iri Literal B → Prop
  preserves_truth : ∀ {B : Type} U (m : Models U) (G : Graph Iri Literal B),
    legal G → (truth U m G ↔ (interpretation U m).Satisfies G.generalize)

namespace ExtensionPresentation

def toExtension (P : ExtensionPresentation.{u, v} Iri Literal) : SemanticExtension.{u} Iri Literal where
  legal := P.legal
  conditions := fun U I => ∃ m : P.Models U, P.interpretation U m = I

def Entails (P : ExtensionPresentation.{u, v} Iri Literal)
    (G : P.toExtension.AdmissibleGraph B₁) (E : P.toExtension.AdmissibleGraph B₂) : Prop :=
  ∀ U (m : P.Models U), P.truth U m G.val → P.truth U m E.val

theorem entails_iff (P : ExtensionPresentation.{u, v} Iri Literal)
    (G : P.toExtension.AdmissibleGraph B₁) (E : P.toExtension.AdmissibleGraph B₂) :
    P.Entails G E ↔ P.toExtension.Entails G E := by
  constructor
  · intro h U I hG
    obtain ⟨m, hm⟩ := I.property
    have hg : (P.interpretation U m).Satisfies G.val.generalize := hm ▸ hG
    have he := h U m ((P.preserves_truth U m G.val G.property).mpr hg)
    have he' := (P.preserves_truth U m E.val E.property).mp he
    change I.val.Satisfies E.val.generalize
    exact hm ▸ he'
  · intro h U m hg
    have hG := (P.preserves_truth U m G.val G.property).mp hg
    have hE := h U ⟨P.interpretation U m, ⟨m, rfl⟩⟩ hG
    exact (P.preserves_truth U m E.val E.property).mpr hE

theorem preserves_simple (P : ExtensionPresentation.{u, v} Iri Literal)
    (G : P.toExtension.AdmissibleGraph B₁) (E : P.toExtension.AdmissibleGraph B₂)
    (h : SimplyEntails.{u} G.val.generalize E.val.generalize) : P.Entails G E :=
  (P.entails_iff G E).mpr (P.toExtension.preserves_simple G E h)

end ExtensionPresentation
end RDF11
