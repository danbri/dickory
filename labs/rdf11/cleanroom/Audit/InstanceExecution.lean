/-
Project-owned symbolic regressions for the executable instance search.
They exercise the evaluator; the universal evidence is in InstanceSearch,
InstanceDecision and ClosureInstanceCheck. No concrete RDF parser is tested.
-/
import RDF11.ClosureInstanceCheck
import Audit.ClosureExecution

namespace Spec2Lean.InstanceExecution
open RDF11

abbrev GT := GeneralizedTriple String (String × String) Nat
abbrev OT := Triple String (String × String) Nat

def edge (s : Term String (String × String) Nat) (p : String)
    (o : Term String (String × String) Nat) : GT := ⟨s, .iri p, o⟩

def checks : List (String × Bool) := Id.run do
  let g := edge (.iri "s") "p" (.iri "o")
  let pattern := edge (.blank 0) "p" (.iri "o")
  let groundMissing := edge (.iri "s") "p" (.iri "other")
  let shared := [edge (.blank 0) "p" (.iri "a"), edge (.blank 0) "q" (.iri "b")]
  let separate := [edge (.iri "s1") "p" (.iri "a"), edge (.iri "s2") "q" (.iri "b")]
  let connected := [edge (.iri "s1") "p" (.iri "a"), edge (.iri "s1") "q" (.iri "b")]
  let simultaneousG := [edge (.blank 1) "p" (.iri "a"), edge (.iri "a") "q" (.iri "z")]
  let simultaneousE := [edge (.blank 0) "p" (.blank 1), edge (.blank 1) "q" (.iri "z")]
  let lexicalA := edge (.iri "s") "p" (.literal ("01", "datatype"))
  let lexicalB := edge (.iri "s") "p" (.literal ("1", "datatype"))
  let literalSubject := edge (.literal ("x", "datatype")) "p" (.iri "o")
  let ordinary : List OT := [⟨.blank 0, "p", .iri "o"⟩]
  let independent : List (Triple String (String × String) String) := [⟨.blank "x", "p", .iri "o"⟩]
  let certificateOK := match InstanceSearch.certificate [g] [pattern] with
    | none => false
    | some witness => InstanceSearch.accepts [g] [pattern] witness.val &&
        decide (witness.val.resolve 0 = .iri "s")
  let cv := ClosureExecution.vocabulary
  let cd := ClosureExecution.decoder
  let property : ClosureExecution.Triple :=
    ⟨.blank 0, .iri (.inr (.rdf .rdfType)), .iri (.inr (.rdf .rdfProperty))⟩
  let domain : ClosureExecution.Triple :=
    ClosureExecution.named (.inl "p") (.inr .domain) (.inl "Class")
  let assertion : ClosureExecution.Triple := ClosureExecution.named (.inl "s") (.inl "p") (.inl "o")
  let typed : ClosureExecution.Triple := ⟨.blank 0, .iri (.inr (.rdf .rdfType)), .iri (.inl "Class")⟩
  return [
    ("empty conclusion succeeds with an empty source", InstanceSearch.check ([] : List GT) []),
    ("empty source rejects a nonempty existential conclusion", !(InstanceSearch.check [] [pattern])),
    ("a successful search returns a checked substitution certificate", certificateOK),
    ("one conclusion blank must have one witness across triples", !(InstanceSearch.check separate shared) && InstanceSearch.check connected shared),
    ("distinct blanks and triples may collapse to one source triple", InstanceSearch.check [g] [pattern, edge (.blank 1) "p" (.iri "o")]),
    ("replacement blanks are not recursively substituted", InstanceSearch.check simultaneousG simultaneousE),
    ("shared blank identifiers need not be fixed by the conclusion mapping", InstanceSearch.check [edge (.blank 0) "q" (.iri "x"), g] [pattern]),
    ("source blanks are permissible replacement terms", InstanceSearch.check [edge (.blank 7) "p" (.iri "o")] [pattern]),
    ("ordinary conclusions may have generalized literal-subject instances", InstanceSearch.ordinaryCheck [literalSubject] ordinary),
    ("literal identity keeps distinct lexical spellings separate", !(InstanceSearch.check [lexicalA] [lexicalB])),
    ("embedded datatype names are not additional position terms", decide (.iri "datatype" ∉ InstanceSearch.terms [lexicalA])),
    ("ground conclusions reduce to exact triple inclusion", InstanceSearch.check [g, lexicalA] [g] && !(InstanceSearch.check [g] [groundMissing])),
    ("input duplicates and order preserve the result", InstanceSearch.check connected shared == InstanceSearch.check (connected.reverse ++ connected) (shared ++ shared)),
    ("separate blank domains are handled without identifying labels", InstanceSearch.apartCheck [edge (.blank 7) "p" (.iri "o")] independent),
    ("candidate count uses distinct terms and occurring blanks", (InstanceSearch.candidates [g, g] [edge (.blank 0) "p" (.blank 1)]).length == 9),
    ("RDF closure composes with an existential property check", ClosureEvaluation.rdfCheck Prod.snd cv.toRDF cd [assertion] [property]),
    ("RDFS closure composes with an existential domain check", ClosureEvaluation.rdfsCheck Prod.snd cv cd [domain, assertion] [typed]),
    ("full selected-closure check retains the completeness obstruction", !(ClosureEvaluation.rdfsCheck Prod.snd cv cd [ClosureExecution.premise] [ClosureExecution.conclusion]))
  ]

end Spec2Lean.InstanceExecution
