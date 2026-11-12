# Headless Linked Assurance — Node, Chromium, MCP, WebMCP

Two separate execution paths evaluate the same pinned Factoidal 0.35.1 RDF
scenario with the same explicit graph scope and entailment regime.

- Node CLI: a real Node.js worker thread imports the installed Factoidal
  package, including its WASM engine.
- Browser CLI: Playwright launches a real headless Chromium process. The
  page evaluates Factoidal inside a dedicated browser Web Worker. Its CDN
  imports are fulfilled from the pinned npm package's actual bytes.
- Browser WebMCP: document.modelContext.registerTool exposes the case
  catalogue and RDF evaluation to WebMCP-capable browsers.
- Node MCP: an MCP v2 server exposes the catalogue and real Node runner
  over the standard stdio transport.

## Install

From the repository root, with Node 22+:

    npm ci --prefix labs/linked-assurance
    npm ci --prefix tools/viewer-browser
    npm install --prefix labs/linked-assurance/tools/headless
    cd tools/viewer-browser && npx playwright install chromium

## CLI examples

Node execution:

    node labs/linked-assurance/tools/headless/node-runner.mjs --scenario vocabulary --scope union --regime RDFS

Browser execution:

    node tools/viewer-browser/linked-headless.mjs --scenario vocabulary --scope union --regime RDFS

Compare the distinct engines on the same input:

    node tools/viewer-browser/linked-headless.mjs --compare --scenario vocabulary --scope union --regime RDFS

Try a different graph and rule setting:

    node tools/viewer-browser/linked-headless.mjs --compare --scenario offer --variant both --regime RDFS

These CLIs print machine-readable JSON to stdout. A mismatched completed
comparison exits with a nonzero status.

## Node MCP server

Install the headless package first. Then start:

    node labs/linked-assurance/tools/headless/mcp-server.mjs

Configure an MCP client to launch that file with Node through stdio. Its
two tools are linked_assurance_cases and linked_assurance_evaluate.
The RDF runner actually uses Node worker_threads and the actual Factoidal WASM.
A third MCP tool, linked_assurance_policy, invokes native Lean 4.33.1 after verifying the demo credential and generating the Lean fixture.

## Browser WebMCP

The interactive application registers linked_assurance_cases and
linked_assurance_evaluate on document.modelContext when available.
This is currently an experimental Chromium feature. If it is absent,
the browser CLI calls the identical local handler and clearly reports
direct-browser-handler rather than claiming native WebMCP support.
The test-only fallback is exposed only with the ?headless=1 URL parameter.

The tools expose no filesystem, GitHub or credential-mutating operations.

## What is compared

The shared headless-contract.js module defines the request and normalized
observation shapes. Every completed comparison includes:

- The entire ordered ASK query list with exact texts and Boolean answers.
- Selected graph digest and original TriG bytes digest.
- Selected scope, regime, and engine version.
- Named graph and triple counts.
- A summary of available derivation/explanation evidence.

Elapsed time, diagnostic strings and Node/Chromium runtime attestation
are excluded from semantic equality. The latter are reported separately.

A timeout, parser error, cancellation or crash is NOT a false answer.
The parity tool reports incomparable when either path fails to complete.

## Runtime identity evidence

The Node runner reports process.versions.node, the real executable path,
worker_threads.threadId, and the absence of Window/Document.

The Chromium runner launches Playwright Chromium and obtains
Browser.getVersion over the Chrome DevTools Protocol. It also checks
Window, Document, Worker, navigator.userAgent and WebAssembly from
inside the loaded browser page.

These are real execution tests rather than a mathematically impossible
proof that arbitrary underlying hosts cannot emulate one another.

## Lean theorem and limits

lean/RunnerParity.lean proves conditional parity of the shared checked
policy and evidence adapter. Equal context, execution state, query
bindings, query observations and operational inputs imply equal resulting
policy decisions and attacker objective outcomes.

These equalities are premises checked for sampled runs by the parity
harness. Neither Lean nor the test suite proves global Node-vs-Chromium
WebAssembly semantics, JavaScript marshalling, memory management or
memory-crash freedom.

The generic node-runner and linked-headless CLIs compare the RDF/evidence
stage across multiple scenarios. Two additional paths exercise the **actual
Lean policy** on a matching fixture:

    node labs/linked-assurance/tools/headless/policy-runner.mjs --scenario vocabulary
    node tools/viewer-browser/lean-policy.mjs

The browser command is an existing headless policy regression runner, now
extended to independently execute the Node/native-Lean path and compare:

- default vocabulary fixture: decisions, attacker outcomes, fixture hash,
  and selected graph hash;
- false-alarm fixture: protective shutdown, attacker success and fixture hash.

Both must use pinned Lean 4.33.1: native Lean in Node and wasm32 Lean inside
Chromium. The browser needs the pinned verified compiler assets staged by
Dickory's site build; a bare checkout without those assets cannot run it.

**This is bounded test-case parity, not a universal equivalence proof of
Node and Chromium.** The Lean theorem states conditional application-policy
parity assuming identical evidence and operations. Neither the host
serialization bridge nor either runtime's memory behaviour has been
formally verified. The generic browser CLI's WebMCP tool does RDF evaluation;
full Lean execution remains available in the interactive UI and the
headless policy regression CLI.

## Checks

    node --test tools/viewer-browser/linked-headless-parity.test.mjs
    node --test labs/linked-assurance/tools/headless/tests/mcp.test.mjs

CI executes these on the review branch. Tests include nominal cases,
different scopes and regimes, false-alarm cases, invalid TriG and
independent runtime identity checks.
