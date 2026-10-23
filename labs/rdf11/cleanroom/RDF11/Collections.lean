/-
Appendix D.3 collection descriptions use ordinary triples. These constructors
describe selected shapes; they impose no global well-formedness requirement.
-/
import RDF11.RDFS

namespace RDF11.Collections

/-- The two-triple head/tail idiom, without an added type assertion. -/
def cell (v : RDFSVocabulary Iri) (root : Subject Iri B)
    (item tail : Term Iri Literal B) : Graph Iri Literal B :=
  Set.ofList [⟨root, v.iri (.rdf .rdfFirst), item⟩,
    ⟨root, v.iri (.rdf .rdfRest), tail⟩]

/-- The printed four-triple, two-item chain with two existential blank nodes. -/
def twoItemChain (v : RDFSVocabulary Iri) (a b : Iri) : Graph Iri Literal Bool :=
  Set.union (cell v (.blank false) (.iri a) (.blank true))
    (cell v (.blank true) (.iri b) (.iri (v.iri (.rdf .rdfNil))))

/-- The printed multiple-head, multiple-tail description. -/
def branchingCell (v : RDFSVocabulary Iri) (a b c : Iri) : Graph Iri Literal Unit :=
  Set.union (cell v (.blank ()) (.iri a) (.iri c))
    (cell v (.blank ()) (.iri b) (.iri (v.iri (.rdf .rdfNil))))

def headOnly (v : RDFSVocabulary Iri) (a : Iri) : Graph Iri Literal Unit :=
  Set.singleton ⟨.blank (), v.iri (.rdf .rdfFirst), .iri a⟩

end RDF11.Collections
