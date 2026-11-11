# Factoidal and Lean policy integration

The lab explores how formal guarantees about Factoidal can support claims about
the RDF data and policies processed by it. A proof that an evaluator implements
its specification and evidence that a particular offer satisfies an application
policy are different artifacts. The useful result is a checked connection
between them, with the inputs and assumptions available for inspection.

Factoidal's RDF representation and implementation are the basis of this work.
Dickory's separate reconstruction of RDF semantics is a possible later
comparison, not a substitute model for the integration.

Ontologies, queries, shapes, rule graphs, vocabulary identifiers and instance
data should normally be runtime inputs. A generic correctness theorem can
quantify over all admitted inputs, including ontologies and data created after
the theorem was proved. Selecting a supported entailment regime should also be
a runtime choice. Changes to those inputs do not, by themselves, require new
Lean declarations or recompilation. New vocabulary is not a request to generate
a Lean class for each IRI.

Compilation has a distinct role. A live compiler lets someone author a new Lean
policy, establish a new theorem, or construct a specialised executor. It must be
distinguished from executing Factoidal's already compiled WASM application.
Browser access to both is useful, but routine evaluation and certificate checking
should not depend on invoking the compiler again. New inference rules require
engine changes only when they cannot be expressed in an already supported rule
language.

There is a spectrum of integration mechanisms, each with a different obligation:

| Mechanism | What must connect to the formal claim |
| --- | --- |
| RDF or SPARQL supplied as text | Parsing and evaluation of the admitted language |
| Terms, graphs and parsed query expressions supplied as values | Their actual Factoidal types, identity rules and evaluation semantics |
| RDF notation embedded in Lean | Elaboration into those formal objects, rather than an unrelated sketch |
| A fixed query used by a Lean policy | The relationship between the query result and the policy predicate |
| A specialised query or policy executable | Equivalence to the specified evaluator on its admitted inputs |
| A certificate for one result | Valid derivation of that conclusion from the identified inputs |

Embedding a query string in Lean does not itself prove what that query means.
Likewise, proving a Boolean conjunction about supplied flags does not connect
those flags to the original RDF. A first implementation may accept external
query results as inputs to a checked policy, but its theorem then remains
conditional on those inputs. This is a useful intermediate boundary only if it
is visible and the missing connection is stated precisely.

The responsible-party example gives the experiment a concrete target. An offer
identifies a product and a responsible party. An application may require the
party to be classifiable as a Person or Organization, and route the offer
according to that evidence. A subclass assertion can justify an inferred type.
A range assertion can infer the type of an existing property value; it does not
require the property to exist. Requiring a responsible-party field needs an
explicit application constraint, with its own scope and treatment of missing
information.

Routing must distinguish Person established, Organization established, both
established and neither established. Membership in both classes is not an
inconsistency unless the selected semantics and axioms make it one. Failure to
establish membership is not proof of non-membership. Routing precedence may be
an application choice, but it must not be presented as semantic exclusion.
An inferred Person type also establishes nothing by itself about existence,
legal capacity, informed consent or authenticity.

A result needs a semantic context: the dataset and ontology revisions, selected
default and named graphs, active graph, entailment regime, supported syntax and
extensions, datatype treatment and blank-node scope. Policies that depend on
time or external observations need those inputs as well. Constructing a union
for reasoning is a declared operation, not an implicit interpretation of every
named graph. Unsupported regimes, invalid inputs and failed executions must
remain distinguishable from negative query results.

The desired proof chain has separate steps. First, the implementation must
satisfy the specified evaluator under stated admissibility conditions. Second,
the relevant query or checker must imply the application policy predicate;
equivalence is stronger and requires completeness as well as soundness. Third,
the operational decision must follow the policy and its external prerequisites.
For SPARQL results, the chosen equivalence must account for multiplicity where
applicable. These are proof targets, not consequences of putting the components
in one application.

Runtime certificates offer another connection. A certificate can identify a
conclusion, its premises and the inference rules used. A small checker can
validate the derivation against the designated graphs. A general theorem about
that checker can cover future certificates without generating a fresh Lean
proof for every incoming document. The lab should examine Factoidal's existing
derivation and checker facilities before designing another certificate system.

A domain certificate is not necessarily a Lean proof term. Lean source, kernel
expressions and compiled environments serve different purposes from an
application-defined RDF evidence format. Lean does not supply the latter by
default. JSON, CBOR or RDF can encode a certificate, but the encoding must have
a defined interpretation. RDF representation alone gives a certificate no
authority. A checker must reject invalid rule applications, missing premises,
circular justifications and ambiguous references.

Evidence identity must bind a conclusion to the dataset, ontology, query,
policy, regime and relevant implementation versions. A hash of input bytes
identifies that serialization; it is not automatically a canonical identity for
an RDF graph. Blank nodes, term equality and normalization need explicit rules
before graph identities or interchangeable encodings are claimed.

Positive derivations and negative claims require different evidence. A finite
derivation may establish a positive consequence. Establishing absence within a
closed-world policy additionally needs a complete search of an identified
snapshot and an explicit scope assumption. Neither a failed query nor an
interrupted search supplies that evidence. Different entailment regimes may
need different certificate forms.

Parsing, document integrity, signature verification, semantic derivation, query
evaluation and policy compliance should remain separately inspectable. A valid
signature concerns a payload and a key under a specified verification process;
an RDF assertion that a signature was verified cannot replace that process.
None of these checks, alone, proves that the asserted facts match the world.

Specialisation is an optional extension. A compiler could produce an executable
for a query together with evidence that it agrees with the generic evaluator.
That can be supported by a universal compiler-correctness theorem or by checking
each translation. The motivation is performance or an additional formal claim,
not a requirement to compile every changed ontology.

The immediate test of the lab is therefore substantive: can an edited policy
operate on Factoidal's runtime semantic inputs, expose exactly why it reached
a decision, and identify which parts of that explanation are checked? New
vocabulary, changed graph scope, ambiguous classification, missing evidence,
unsupported features and rejected proof candidates should make the boundaries
observable. A compiler button and a successful example are insufficient.
