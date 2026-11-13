# Dickory developer tool profile 0.2

This is an optional, Apache-2.0 application profile, not a competing MCP or
WebMCP standard. Sites choose **their own tool vocabulary, parameters,
capabilities and transports**. A tool name need not be RDF-related or known
when the Lean model was written. The supplied Linked Assurance catalogue is
one instance, not a mandatory global ontology.

## Protocol targets checked on 2026-11-12

- MCP specification **2026-07-28**, TypeScript SDK **2.4.0**.
  Tests and the CLI pin this revision, assert `getProtocolEra() === 'modern'`,
  and do not silently count legacy `initialize` handshakes as modern support.
- WebMCP **Draft Community Group Report snapshot, 2026-11-12**:
  `document.modelContext.registerTool`, `getTools`, `executeTool`,
  registration-lifetime AbortSignal, execution AbortSignal, and input/output
  schemas. The date is our snapshot identity, NOT a WebMCP wire-version field.
- WebMCP is document-local, not an MCP HTTP or stdio transport.

Primary references:
https://modelcontextprotocol.io/specification/2026-07-28
https://ts.sdk.modelcontextprotocol.io/v2/protocol-versions
https://ts.sdk.modelcontextprotocol.io/v2/serving/http.html
https://webmachinelearning.github.io/webmcp/

## Write a site profile

```js
import {defineProfile, createDispatcher} from './profile/core.js';
import {registerWebMCP} from './profile/webmcp.js';
const profile = defineProfile({
  id: 'my-site',
  transports: ['webmcp', 'mcp-stdio', 'mcp-http', 'local-cli'],
  enabledTools: ['my_site.describe'],
  tools: [{
    name: 'my_site.describe', description: 'Describe a supplied resource.',
    requires: ['read-resources'],
    inputSchema: {
      type: 'object', properties: {
        iri: {type:'string', maxLength:1000},
        includeLabels: {type:'boolean', default:true}
      }, required:['iri'], additionalProperties:false
    }
  }]
});
const dispatcher = createDispatcher({
  profile, transport:'webmcp', capabilities:['read-resources'],
  handlers:{'my_site.describe': async args => ({iri:args.iri})}
});
await registerWebMCP(dispatcher); // default same-origin exposure
```

See `profile/demo.html` for a runnable, dependency-free example.
Registration does not fetch or embed a language model. A client/browser agent
is separate. Site exposure is host-owned configuration; tool callers cannot
change the enabled list or manufacture a missing runtime capability.

## The portable signature fragment

Named top-level objects; nested objects/arrays; string, finite number,
safe integer, boolean and null; primitive enums; numeric, length and item
bounds. Every object declares `additionalProperties:false`. Required and
optional fields are distinct. Optional fields may have validated defaults;
required fields may not. Null is never silently interpreted as omission.
No coercion; an integer string is not an integer. Unsupported JSON Schema
keywords are rejected at profile construction, not ignored.

Defaults are explicitly applied by the shared decoder, recursively and in a
stable property order. JSON Schema's annotation alone does not supply values.
The library currently profiles a subset of JSON Schema; it does not constrain
the full expressive power of MCP or WebMCP. Extend the fragment with tests and
semantic obligations rather than claiming unimplemented schema support.

The Lean model proves field-resolution soundness, required-absence rejection,
resolved-value stability, disabled tool/transport and missing capability
rejection, restriction monotonicity, and transport-independent application
results **given equal resolved arguments**, when its kernel check passes.
The validation predicate is a parameter: these proofs are not a proof of the
JavaScript JSON parser or JSON Schema implementation. JavaScript-to-Lean
refinement remains an explicit obligation. Unit tests exercise the actual
JavaScript decoder/dispatcher.

## Site configuration for this lab

`developer-profile.json` chooses enabled tools, transports, maximum input size
and maximum RDF computation budget. Node can load a different host-owned JSON
file via `LINKED_PROFILE=/absolute/path/profile.json`. The browser loads the
site's same-origin file. Never take that filename from a tool argument.

All four operations are exposed on Node and browser:

- `linked_assurance_cases`
- `linked_assurance_evaluate`
- `linked_assurance_check_policy`
- `linked_assurance_policy`

Both policy implementations take the same `state` object: clock, transport,
permission, attacker objective, legitimacy oracle, and optionally credential
payload/signature. Defaults are synthetic DEMO observations, not authority or
real identity assertions. No state is taken from prior UI interactions.
`profile/policy-input.js` constructs both fixtures. The fixed repository policy
is used: this interface does NOT expose arbitrary Lean code execution. Native
Lean is not a sandbox. Site developers can supply reviewed additional handlers.

## Local launchers

Install exact top-level dependencies with:

```sh
npm ci --prefix labs/linked-assurance
npm ci --prefix tools/viewer-browser
npm install --prefix labs/linked-assurance/tools/headless
cd tools/viewer-browser && npx playwright install chromium
```

From the repository root:

```sh
node labs/linked-assurance/tools/headless/cli.mjs --backend node --tool linked_assurance_cases
node labs/linked-assurance/tools/headless/cli.mjs --backend mcp-stdio --tool linked_assurance_cases
node labs/linked-assurance/tools/headless/http-server.mjs
node labs/linked-assurance/tools/headless/cli.mjs --backend mcp-http --tool linked_assurance_cases
node tools/viewer-browser/linked-headless.mjs --tool linked_assurance_cases
```

Pass `--input request.json` to either CLI. Native policy checks require Lean
4.33.1. Browser policy checks require the pinned compiler assets and built
support/policy modules (the existing site workflow builds them).

HTTP binds **127.0.0.1 only**, with Host and Origin validation; it is not a
public multi-user deployment or a replacement for authentication. Both MCP
bindings use one server factory and advertise the same JSON Schemas.

The Chromium CLI requires actual native WebMCP registration and invocation.
It returns failure/exit 3 if unavailable. `--direct` is an explicitly labelled
diagnostic option and never satisfies the native-WebMCP tests. No navigator
alias, polyfill, or Node fallback is presented as the native browser API.

## Layered outcomes and cancellation

The shared envelope reports invocation status separately from the application's
RDF execution, Lean proof check, decision and attacker outcome. A returned
`deny` is not a protocol failure. A `protectiveShutdown` can be an attacker
success. Timeout supplies no false RDF answers. SDK/browser validation may
reject an invalid call before the handler; protocol-specific errors are not
promised byte-for-byte equal. Accepted arguments and application observations
are compared independently of transport wrappers.

RDF budgets terminate a real Worker/thread. Native Lean children are killed on
cancellation or their compiler deadline. The browser Lean compiler has its own
worker timeout; cancellation prevents result publication but does not currently
interrupt an active Lean compile immediately. Do not claim a stronger bound.

WebMCP metadata and MCP annotations are hints, not authorization. The default
WebMCP registration is same-origin; explicit cross-origin exposure must satisfy
the browser's Permissions Policy and two-sided opt-in requirements. Unknown
site effects default conservatively to consequential/non-read-only hints.
The lab explicitly marks its own fixed demonstration operations read-only;
they produce decision records rather than actually granting permission.

## Verification limits

`lean/DeveloperProfile.lean` is a checked mathematical model when CI passes.
`RunnerParity.lean` supplies the application-level conditional equality. Neither
proves Node/Chromium/WASM implementation equivalence or memory safety. Runtime
identity probes, exact input/fixture digests and protocol tests are independent
empirical evidence. Inspect the current CI result rather than inferring a pass
from this document. No result from a mocked adapter is labelled native support.

The model-check report records source hashes; the site build rejects stale
model evidence. It still does not turn the separately tested JavaScript
implementation into kernel-verified code. The SDK dependencies are pinned at
the top level; CI preserves the resolved npm lock as an artifact for audit.

The profile is not an authorization system for a hostile host. Tool handlers,
profile settings, user/clock observations, credentials and the JSON-to-Lean
bridge have explicit trust boundaries. Local clients can invoke the same
semantics by MCP or the CLI; no language model or paid subscription is required.
