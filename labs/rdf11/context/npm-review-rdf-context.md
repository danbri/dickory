# RDF-related motivation from the npm review

The independent review of `@factoidal/core` 0.11.0 found that behavior at ingestion and wrapper boundaries could differ from behavior exercised by internal tests. This note preserves the relevant motivation; the full package-review environment and its reproductions are not part of this source-first lab.

The duplicate-triple finding (R02) was especially relevant: repeated identical triples could affect public query results. A list representation and membership-only theorems do not establish RDF graph uniqueness or multiplicity-independent enumeration. This lab therefore defines graphs as extensional sets and gives finite enumerations a separate contract with membership and uniqueness proofs. A negative check asks Lean to reject an enumeration containing a duplicate.

Blank-node scope and transport through merge/ingestion paths also require explicit contracts. This lab models one shared assignment per graph and disjoint blank-node domains for binary merge, with a counterexample distinguishing merge from ordinary union. Those proofs do not yet establish that the package's ingestion or merge paths implement the model.

Other review findings involved recursive quoted terms, RDF 1.2 version/direction metadata, validation/serialization paths, public TypeScript declarations, and broader OWL claims. These require their own specified boundaries and are not silently absorbed into an RDF 1.1 Semantics coverage claim.

The eventual shipping obligation is a chain from reviewed specification claims through Lean definitions to concrete storage, parsing, query, serialization and JS/WASM interfaces. The current lab establishes only an initial part of that chain. Passing the draft verifier does not certify any published npm version.
