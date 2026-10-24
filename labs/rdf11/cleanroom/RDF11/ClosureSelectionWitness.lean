/-
An inhabited datatype interface for the Appendix A selection example.
String lexical validity and language-tag validity stay explicit: this is not
an XML10 character validator or a BCP47 validator.
Typed literals retain every non-langString IRI; language literals carry a
valid-tag proof. String values and language-pair values remain distinct.
The generic result in ClosureSelectionScope also applies to other theories.
-/
import RDF11.ClosureSelectionScope

namespace RDF11.ClosureSelection

inductive WitnessLiteral (validTag : Set String) where
  | typed (lexical : String)
      (datatype : { a : Iri // a ≠ vocabulary.iri (.rdf .rdfLangString) })
  | tagged (lexical : String) (tag : { s : String // validTag s })

abbrev WitnessValue := Sum Iri (Sum String (String × String))

def witnessTheory (stringLexical : String → Bool) (validTag : Set String)
    (lower_valid : ∀ tag, validTag tag → validTag (asciiLower tag)) :
    DatatypeTheory Iri (WitnessLiteral validTag) WitnessValue where
  literalSyntax := {
    langString := vocabulary.iri (.rdf .rdfLangString)
    lexical := fun l => match l with
      | .typed s _ | .tagged s _ => s
    datatype := fun l => match l with
      | .typed _ a => a.val
      | .tagged _ _ => vocabulary.iri (.rdf .rdfLangString)
    language := fun l => match l with
      | .typed _ _ => none
      | .tagged _ tag => some tag.val
    languageTag := validTag
    tag_valid := by
      intro l tag h
      cases l with
      | typed _ _ => cases h
      | tagged _ t => exact Option.some.inj h ▸ t.property
    lower_valid := lower_valid
    tagged_iff := by
      intro l
      cases l with
      | typed _ a => simp [a.property]
      | tagged _ _ => simp
  }
  identified := Sum.inl
  L2V := fun d s => if d = .inl (vocabulary.iri (.rdf .xsdString)) ∧ stringLexical s = true
    then some (.inr (.inl s)) else none
  languageValue := fun s tag => .inr (.inr (s, tag))
  language_injective := fun _ _ _ _ h => Prod.mk.inj (Sum.inr.inj (Sum.inr.inj h))
  language_noL2V := fun _ => by simp [vocabulary]

theorem witness_language_coverage (stringLexical : String → Bool) (validTag : Set String)
    (lower_valid : ∀ tag, validTag tag → validTag (asciiLower tag)) :
    RDFSModelConstruction.LanguageCoverage (witnessTheory stringLexical validTag lower_valid) := by
  rintro w ⟨s, tag, ht, rfl⟩
  exact ⟨WitnessLiteral.tagged s ⟨tag, ht⟩, tag, rfl, rfl⟩

theorem witness_parameters (stringLexical : String → Bool) (validTag : Set String)
    (lower_valid : ∀ tag, validTag tag → validTag (asciiLower tag)) :
    RDFSModelConstruction.Parameters (witnessTheory stringLexical validTag lower_valid)
      vocabulary.toRDF.baseDatatypes vocabulary :=
  RDFSModelConstruction.base_parameters _ vocabulary rfl
    (witness_language_coverage stringLexical validTag lower_valid)

/-- A concrete inhabitant of the abstract interface; accepting every string
and tag here proves existence, not XML10 or BCP47 validation. -/
theorem witness_parameters_inhabited :
    ∃ T : DatatypeTheory Iri (WitnessLiteral (fun _ => True)) WitnessValue,
      RDFSModelConstruction.Parameters T vocabulary.toRDF.baseDatatypes vocabulary :=
  ⟨witnessTheory (fun _ => true) _ (fun _ _ => True.intro),
    witness_parameters (fun _ => true) _ (fun _ _ => True.intro)⟩

/-- All three obligations share the same theory, vocabulary and two graphs.
This establishes the discrepancy for the formal transcription, with the
concrete IRI encoding and language-tag validation boundaries still explicit. -/
theorem selection_counterexample (stringLexical : String → Bool) (validTag : Set String)
    (lower_valid : ∀ tag, validTag tag → validTag (asciiLower tag)) :
    let T := witnessTheory stringLexical validTag lower_valid
    let G := (premise : Graph Iri (WitnessLiteral validTag) B).generalize
    let E := (conclusion : Graph Iri (WitnessLiteral validTag) B).generalize
    (∃ (U : Type u) (I : SimpleInterpretation Iri (WitnessLiteral validTag) U),
      I.RDFSModel T vocabulary.toRDF.baseDatatypes vocabulary ∧ I.Satisfies G) ∧
    RDFSEntails.{u} T vocabulary.toRDF.baseDatatypes vocabulary G E ∧
    ¬ SimplyEntails.{u} (RDFSClosure T vocabulary G E) E :=
  ⟨premise_consistent _ (witness_parameters stringLexical validTag lower_valid),
    full_entailment _, closure_not_simply_entails _⟩

end RDF11.ClosureSelection
