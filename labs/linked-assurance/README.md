# Linked Assurance

An experimental Factoidal and Lean policy workbench in its own Dickory lab.
[Design and proof obligations](DESIGN.md) explains the intended connections.
The existing `labs/rdf11/` formalization is independent and unchanged.

**Browser compiler blocker:** the pinned WASM compiler/library distribution
fails to compile the support module with missing executable definitions,
including `Bool.repr._redArg` and `List.any._redArg`. This was observed with
hash-verified assets in cross-origin-isolated Chromium. The UI shows the actual
diagnostics and emits no substitute policy decision. Native Lean 4.33.1 checks
pass. RDF execution, Factoidal certificates and fixture export work without the
compiler.

The primary editor contains a real Lean module. Its `policy_contract` is checked
against the fixed `Workbench.permitRequirements` definition. Removing a required
gate breaks the contract. The adapter retains compiled `Policy.olean` artifacts
for reuse while small runtime fixtures are elaborated separately. That browser
path remains blocked by the distribution issue; native checks import the
compiled module successfully. RDF vocabulary,
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
python3 labs/linked-assurance/tools/serve.py --isolate
```

Open <http://127.0.0.1:8012/labs/linked-assurance/>. Without `--isolate`, the app
can request a service worker scoped only to the lab and reload. The compiler
requires a secure context, COOP/COEP and SharedArrayBuffer. If they are absent,
the UI reports `compiler_unavailable`. It does not redirect to another IDE.
The compiler downloads approximately 325 MB of pinned assets on first use.
The compiler identifies itself as Lean **4.28.0-pre**, commit
`38f3c0c45b8df6da2652faff6dcaa15afb5a6981`; it differs from the native Lean
4.33.1 test compiler. Its version probe's raw output and exit status are retained.

`compiler-assets.json` can point to the same bytes on a configurable host or
same-origin static mirror. Hash checks remain mandatory. The public whitelist
excludes downloaded binaries, npm dependencies and local input logs.

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

Use a complete, matching Lean WASM distribution with executable library code
(`.ir` and any required private environment data). Validate a support-module
import, the policy contract, repeated fixture runs and a rejected proof mutation.
A persistent worker compiler is preferable: the current SDK runs Lean in an
iframe and can block the UI during elaboration. Adding COOP/COEP alone cannot
repair missing executable code. Keep the unavailable state until those checks
pass. No test currently establishes browser reuse of `Policy.olean`.
