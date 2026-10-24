/-
Derived guards for RDF 1.1 Semantics §§3, 5 and 7.2. A simple-valid operation
can violate an extension's syntax, while an admitted graph can be unsatisfiable.
The required-triple policy is illustrative; no such policy is imposed on RDF.
-/
import RDF11.SemanticExtensions

namespace RDF11.ExtensionBoundary

def requiresTriple (s p o : Iri) : SemanticExtension.{u} Iri Literal where
  legal := fun G => G ⟨.iri s, p, .iri o⟩
  conditions := fun _ _ => True

def assertion (s p o : Iri) : Graph Iri Literal B :=
  Set.singleton ⟨.iri s, p, .iri o⟩

theorem deletion_breaks_admissibility (s p o : Iri) :
    let R : SemanticExtension.{u} Iri Literal := requiresTriple s p o
    let G : Graph Iri Literal B := assertion s p o
    let E : Graph Iri Literal B := Set.empty
    R.legal G ∧ ¬ R.legal E ∧ SimplyEntails.{u} G.generalize E.generalize := by
  refine ⟨rfl, fun h => h, ?_⟩
  apply subgraph_entailment
  rintro _ ⟨_, h, _⟩
  exact False.elim h

/-- Literal lexical ill-typing is semantic inconsistency, not malformed triples. -/
theorem illTyped_admitted_unsatisfiable (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : Graph Iri Literal B) (t : Triple Iri Literal B) (l : Literal)
    (ht : G t) (hl : t.generalize.hasLiteral l) (hi : T.IllTyped D l) :
    (SemanticExtension.datatypes.{u} T D).legal G ∧
      ¬ (SemanticExtension.datatypes.{u} T D).Satisfiable ⟨G, True.intro⟩ := by
  refine ⟨True.intro, ?_⟩
  intro h
  exact illTyped_graph_unsatisfiable T D G.generalize t.generalize ⟨t, ht, rfl⟩ hl hi
    ((SemanticExtension.datatypes_satisfiable_iff T D G).mp h)

theorem illTyped_entails_admitted (T : DatatypeTheory Iri Literal Value) (D : Set Iri)
    (G : Graph Iri Literal B₁) (E : Graph Iri Literal B₂) (t : Triple Iri Literal B₁) (l : Literal)
    (ht : G t) (hl : t.generalize.hasLiteral l) (hi : T.IllTyped D l) :
    (SemanticExtension.datatypes.{u} T D).Entails ⟨G, True.intro⟩ ⟨E, True.intro⟩ :=
  (SemanticExtension.datatypes T D).unsatisfiable_entails _ _
    (illTyped_admitted_unsatisfiable T D G t l ht hl hi).2

end RDF11.ExtensionBoundary
