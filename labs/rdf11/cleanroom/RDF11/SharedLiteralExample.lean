/-
Appendix A's first example: two edges with the identical literal supply ONE
shared existential witness and its datatype. Names are parameters; the source
uses ex:a/ex:p and ex:b/ex:q with one xsd:string literal. This proves the
entailment and generalized-rule route, not failure of every rdfD1 reuse policy.
-/
import RDF11.EntailmentClosure

namespace RDF11.SharedLiteralExample

def premise (s₁ p₁ s₂ p₂ : Iri) (l : Literal) : Graph Iri Literal B :=
  Set.ofList [⟨.iri s₁, p₁, .literal l⟩, ⟨.iri s₂, p₂, .literal l⟩]

def conclusion (v : RDFVocabulary Iri) (datatype s₁ p₁ s₂ p₂ : Iri) (b : B) : Graph Iri Literal B :=
  Set.ofList [⟨.iri s₁, p₁, .blank b⟩, ⟨.iri s₂, p₂, .blank b⟩,
    ⟨.blank b, v.iri .rdfType, .iri datatype⟩]

/-- The same literal is substituted at every occurrence of the conclusion blank. -/
def substitution (l : Literal) : Substitution Iri Literal B := fun _ => some (.literal l)

theorem generalized_instance (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (s₁ p₁ s₂ p₂ : Iri) (l : Literal) (b : B)
    (hd : v.baseDatatypes (T.literalSyntax.datatype l)) :
    Set.subset ((conclusion v (T.literalSyntax.datatype l) s₁ p₁ s₂ p₂ b).generalize.substitute (substitution l))
      (RDFClosure T v (premise s₁ p₁ s₂ p₂ l).generalize
        (conclusion v (T.literalSyntax.datatype l) s₁ p₁ s₂ p₂ b).generalize) := by
  rintro t ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  have hx : q = ⟨.iri s₁, p₁, .blank b⟩ ∨ q = ⟨.iri s₂, p₂, .blank b⟩ ∨
      q = ⟨.blank b, v.iri .rdfType, .iri (T.literalSyntax.datatype l)⟩ := by
    simpa [conclusion, Set.ofList] using hq
  rcases hx with rfl | rfl | rfl
  · exact .premise (Or.inl ⟨⟨.iri s₁, p₁, .literal l⟩, by simp [premise, Set.ofList], rfl⟩)
  · exact .premise (Or.inl ⟨⟨.iri s₂, p₂, .literal l⟩, by simp [premise, Set.ofList], rfl⟩)
  · apply RuleDerives.rule (RDFClosure T v (premise s₁ p₁ s₂ p₂ l).generalize
      (conclusion v (T.literalSyntax.datatype l) s₁ p₁ s₂ p₂ b).generalize) (fun _ h => h)
    apply RDFStep.GrdfD1 (.iri s₁) (.iri p₁) l
    · exact .premise (Or.inl ⟨⟨.iri s₁, p₁, .literal l⟩, by simp [premise, Set.ofList], rfl⟩)
    · exact hd

theorem entailment (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (s₁ p₁ s₂ p₂ : Iri) (l : Literal) (b : B)
    (hd : v.baseDatatypes (T.literalSyntax.datatype l)) :
    RDFEntails.{u} T v.baseDatatypes v (premise (B := B) s₁ p₁ s₂ p₂ l).generalize
      (conclusion v (T.literalSyntax.datatype l) s₁ p₁ s₂ p₂ b).generalize :=
  rdf_closure_instance_check_sound T v _ _ (substitution l) (generalized_instance T v s₁ p₁ s₂ p₂ l b hd)

theorem string_entailment (T : DatatypeTheory Iri Literal Value) (v : RDFVocabulary Iri)
    (s₁ p₁ s₂ p₂ : Iri) (l : Literal) (b : B)
    (hl : T.literalSyntax.datatype l = v.iri .xsdString) :
    RDFEntails.{u} T v.baseDatatypes v (premise (B := B) s₁ p₁ s₂ p₂ l).generalize
      (conclusion v (v.iri .xsdString) s₁ p₁ s₂ p₂ b).generalize := by
  rw [← hl]
  exact entailment T v s₁ p₁ s₂ p₂ l b (Or.inr hl)

end RDF11.SharedLiteralExample
