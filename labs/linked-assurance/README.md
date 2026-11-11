# Linked Assurance

An experimental Factoidal and Lean policy workbench in its own Dickory lab.
[Design and proof obligations](DESIGN.md) explains the intended connections.
The existing `labs/rdf11/` formalization is independent and unchanged.

The browser uses a pinned Lean **4.33.1** wasm32 compiler and matching Init
library, including executable IR. Hello-world evaluation, theorem checking,
rejection and recovery pass in Node, Deno and Chromium. Chromium also checks
the actual policy contract, imports the compiled policy, runs five fixtures,
and rejects a mutation removing the permit gate. The compiler runs in a worker
and repeated fixtures reuse the imported environment. See
[the minimal checks](tools/hello/README.md).

The primary editor contains a real Lean module. Its `policy_contract` is checked
against the fixed `Workbench.permitRequirements` definition. Removing a required
gate breaks the contract. The adapter retains compiled `Policy.olean` artifacts
for reuse while small runtime fixtures are elaborated separately. RDF vocabulary,
queries, scopes and operational inputs do not change that compiled module.

Factoidal 0.35.1 parses one TriG document. The user selects its default graph,
one named graph, or an explicitly constructed union of `urn:lab:data` and
`urn:lab:ontology`. Selection happens before inference. Blank identities shared
within that document are retained. Other graphs are excluded. Only simple and
RDFS modes are admitted here; this is not a statement about all Factoidal modes.
Every parse/query/explanation operation runs in a worker with a wall-clock
budget, including engine loading. A deadline terminates the worker and supplies
no query answers. Failed ASK results remain “not established”, not refutations.

An optional `Description.ttl` is checked separately by Factoidal's `explain` API.
Its report includes a graph-derivation bundle, checker outcome, assumptions and
`entailedMeans`. This is distinct from a proof that an arbitrary edited SPARQL
query implements the policy. The app does not call the different FPP0 checker
on an incompatible graph-bundle format.

The ECDSA demonstration verifies a payload under a bundled public demo key.
The private key is not stored. The payload identifies the catalogue principal
and an expiry. This authenticates neither a released artifact nor a real-world
identity. Clock, permission and transport are explicit user-selected test
observations. The false-alarm example separately reports the declared attacker
objective; a protective shutdown can be an interruption success.

## Run locally

From the repository root:

```sh
python3 labs/linked-assurance/tools/hello/fetch.py
python3 labs/linked-assurance/tools/serve.py --isolate --port 8081
```

Open <http://127.0.0.1:8081/labs/linked-assurance/>. Without `--isolate`, the app
can request a service worker scoped only to the lab and reload. The compiler
requires a secure context, COOP/COEP and SharedArrayBuffer. If they are absent,
the UI reports `compiler_unavailable`. It does not redirect to another IDE.
The compiler downloads approximately 184 MB of pinned assets on first use.
Its upstream fork commit is `4f9018a62ead9be0ffd652021d5afc8501e92253`.
This matches Factoidal's Lean release version, but wasm32 and the patched fork
still require matching compiled modules; native Factoidal oleans are not imported.
The first support/policy compilations and fixture import take a few minutes.
Subsequent fixture runs in the tested browser took 62–700 ms including RDF work.

`compiler-assets.json` can point to the same bytes on a configurable host or
same-origin static mirror. Hash checks remain mandatory. Pages stages the pinned
compiler files from the repository's binary release; they are not Git source
files. npm dependencies and local input logs are excluded from the site.

## Verification

```sh
cd labs/linked-assurance
npm ci
node tools/check_runtime.mjs
python3 tools/check_lean.py
```

Use Node 22.12 or newer and Lean 4.33.1. The first command installs the pinned Factoidal test runtime. Runtime tests use
its actual WASM engine. Lean checks include a deliberately broken policy which
must be rejected, and concrete permit, denial, timeout and attacker cases.
Reports go to ignored `artifacts/`. Browser tests live beside the repository's
existing viewer checks in `tools/viewer-browser/`.

## Assurance boundary

The policy contract is conditional on the injected evidence and operational
state. The JavaScript serialization bridge, selected-graph construction,
compiler/host, runtime observations and correspondence between a query and the
intended application rule are not proved by that contract. `#eval` executes a
program; it is not a kernel proof of the execution result. The graph certificate
comes from Factoidal's checker, not from the browser Lean compiler independently
rechecking Factoidal's entire implementation.

The compiler audit prints the actual contract's axiom dependencies and rejects
additional axioms or `sorryAx`. This is a source-authoring aid, not a security
boundary for a hostile Lean metaprogram capable of fabricating diagnostic text.
No remote user code should be treated as certified solely from this UI report.

Hashes identify exact text bytes and serialized selected graphs. They do not
claim RDFC canonicalization, blank-node-isomorphism invariance, or datatype-value
normalization. The download contains the precise inputs, outputs, generated
fixture, source hashes, runtime versions and assumptions for review.

External dependencies and local SDK changes: [THIRD_PARTY.md](THIRD_PARTY.md).

## Factoidal source connection

[factoidal-build.json](factoidal-build.json) records the npm engine provenance
at core commit `6f57afba14e04ed648358e4693790edff69a6cd3`. Its relevant contracts
are [explainGraphOf_spec](https://github.com/danbri/factoidal-core/blob/6f57afba14e04ed648358e4693790edff69a6cd3/formal/lean4/L4Factoidal/Dataflow/ExplainGraph.lean)
and [checkGraphRun_sound](https://github.com/danbri/factoidal-core/blob/6f57afba14e04ed648358e4693790edff69a6cd3/formal/lean4/L4Factoidal/Dataflow/GraphClaim.lean).
They use Factoidal's own graph representation and RDFS entailment predicate.
The lab does not replace these with Dickory's RDF11 definitions. A negative
explanation retains the engine's named completeness assumption. The API's
theorem name and these links are not independent kernel checks of the binary
or its serialization bridge.

## Compiler follow-up

The earlier 4.28.0-pre distribution lacked required executable definitions.
Matching compiler/library bytes fixed that failure. Public module declarations
and explicit runtime/meta imports make exported definitions available to both
proof checking and evaluation. `tools/viewer-browser/linked-probe.mjs --policy`
checks this path using the actual browser compiler; no compiler result is mocked.
Browser support is currently established for Chromium, not phone browsers.

The exported `rdf.explanation.bundle` is Factoidal's graph derivation artefact,
also used by its `rdfsExplainGraphStage`. The lab calls `explain()` directly;
its graph selection and Lean adapter have not yet been composed as contracted
Factoidal pipeline stages. A standalone saved-bundle verifier is future work.
