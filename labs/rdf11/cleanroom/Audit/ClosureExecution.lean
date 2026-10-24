/-
Project-owned executable regressions, not W3C fixtures or concrete RDF parsing.
IRIs are symbolic names; literals retain a lexical string and datatype name.
The universal correctness evidence is in RDF11.ExecutableClosure.
-/
import RDF11.ExecutableClosure

namespace Spec2Lean.ClosureExecution
open RDF11 RDF11.ClosureEvaluation

abbrev Iri := Sum String RDFSSymbol
abbrev Literal := String × Iri
abbrev Triple := GeneralizedTriple Iri Literal Nat

def vocabulary : RDFSVocabulary Iri where
  iri := Sum.inr
  distinct := fun _ _ h => Sum.inr.inj h

def decode : Iri → Option Nat
  | .inr (.rdf (.container n)) => some n
  | _ => none

def decoder : ContainerDecoder (fun n => vocabulary.iri (.rdf (.container n))) where
  decode := decode
  correct := by
    intro a n
    cases a with
    | inl s => simp [decode, vocabulary]
    | inr s =>
      cases s with
      | rdf r => cases r <;> simp [decode, vocabulary]
      | _ => simp [decode, vocabulary]

def named (s p o : Iri) : Triple := ⟨.iri s, .iri p, .iri o⟩

def premise : Triple := named (.inl "s") (.inr (.rdf (.container 16))) (.inl "o")
def conclusion : Triple := named (.inl "s") (.inr .member) (.inl "o")

def checks : List (String × Bool) := Id.run do
  let rdfOnce := rdf Prod.snd vocabulary.toRDF decoder [premise] [conclusion]
  let rdfTwice := rdf Prod.snd vocabulary.toRDF decoder [premise, premise] [conclusion]
  let rdfsOnce := rdfs Prod.snd vocabulary decoder [premise] [conclusion]
  let rdfsTwice := rdfs Prod.snd vocabulary decoder [premise, premise] [conclusion]
  let indexed : List Triple := rdfIndexed vocabulary.toRDF 16
  let ax : AxiomLists Prod.snd (fun n => vocabulary.toRDF.iri (.container n)) vocabulary.toRDF.axioms :=
    rdfAxiomLists Prod.snd vocabulary.toRDF
  let fallback : Triple := named (.inr (.rdf (.container 0))) (.inr (.rdf .rdfType)) (.inr (.rdf .rdfProperty))
  let second : Triple := named (.inr (.rdf (.container 1))) (.inr (.rdf .rdfType)) (.inr (.rdf .rdfProperty))
  let embedded : Triple := ⟨.iri (.inl "s"), .iri (.inl "p"), .literal ("lex", .inr (.rdf (.container 23)))⟩
  let high : Triple := named (.inl "s") (.inr (.rdf (.container 1000000))) (.inl "o")
  let lit : Literal := ("text", .inr (.rdf .xsdString))
  let objectLiteral : Triple := ⟨.iri (.inl "s"), .iri (.inl "p"), .literal lit⟩
  let subjectLiteral : Triple := ⟨.literal lit, .iri (.inl "p"), .iri (.inl "o")⟩
  let typing : Triple := ⟨.literal lit, .iri (.inr (.rdf .rdfType)), .iri (.inr (.rdf .xsdString))⟩
  let selfJoin : Triple := named (.inr .domain) (.inr .domain) (.inl "c")
  let selfResult : Triple := named (.inr .domain) (.inr (.rdf .rdfType)) (.inl "c")
  let emptyRDF := rdf Prod.snd vocabulary.toRDF decoder ([] : List Triple) ([] : List Triple)
  let emptyRDFS := rdfs Prod.snd vocabulary decoder ([] : List Triple) ([] : List Triple)
  let lexicalA : Triple := ⟨.iri (.inl "s"), .iri (.inl "p"), .literal ("01", .inr (.rdf .xsdString))⟩
  let lexicalB : Triple := ⟨.iri (.inl "s"), .iri (.inl "p"), .literal ("1", .inr (.rdf .xsdString))⟩
  let lexicalSeed := ax.seed decoder [lexicalA, lexicalB, lexicalA] ([] : List Triple)
  return [
    ("duplicate inputs preserve RDF and RDFS counts", rdfOnce.length == rdfTwice.length && rdfsOnce.length == rdfsTwice.length && rdfsOnce.contains premise),
    ("output enumerations contain no duplicates", decide rdfTwice.Nodup && decide rdfsTwice.Nodup),
    ("selected nonempty axioms already in stage one trigger fallback", ax.fallback decoder indexed indexed && (ax.seed decoder indexed indexed).contains fallback),
    ("new selected axioms do not trigger fallback", !(ax.fallback decoder [] indexed) && !((ax.seed decoder [] indexed).contains fallback)),
    ("embedded literal datatype IRI selects its container index", (decoder.indices Prod.snd [embedded]).contains 23),
    ("large index selects one name without an index-prefix expansion", decoder.indices Prod.snd [high] == [1000000]),
    ("generalized literal typing uses object position only", (rdfNext Prod.snd vocabulary.toRDF [objectLiteral]).contains typing && !((rdfNext Prod.snd vocabulary.toRDF [subjectLiteral]).contains typing)),
    ("binary matching permits using one triple twice", (rdfsNext vocabulary [selfJoin]).contains selfResult),
    ("rdfs1 produces both base datatype facts without a premise", (rdfsZero vocabulary : List Triple).all (rdfsNext vocabulary []).contains),
    ("printed selection obstruction remains observable", !(rdfsOnce.contains conclusion)),
    ("empty-input closures omit rdf:_2 typing", !(emptyRDF.contains second) && !(emptyRDFS.contains second)),
    ("distinct literal spellings survive admission and deduplication", lexicalSeed.contains lexicalA && lexicalSeed.contains lexicalB && (lexicalSeed.filter (fun t => t == lexicalA || t == lexicalB)).length == 2)
  ]

end Spec2Lean.ClosureExecution
