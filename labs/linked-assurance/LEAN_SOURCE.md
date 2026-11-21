# Supplied Lean source, not only the fixed demonstration policy

The common API now has an **opt-in** `linked_assurance_compile_lean` tool.
Its input is actual top-level Lean 4 source. It uses native Lean 4.33.1 in
Node and the pinned 4.33.1 WASM compiler in the browser. The browser path
uses the real CLI module-export operation, not the warm checker that only
checks a file without producing a reusable module.

## Request

```json
{
  "source": "import Init\ndef answer : Nat := 42\nexample : answer = 42 := by rfl\n#eval answer\n",
  "environment": "core",
  "budgetMs": 120000,
  "includeArtifacts": true
}
```

`source` is required. `environment` is `core` or `workbench`. The latter
makes this lab's actual `Workbench.lean` importable. User source is a fixed
module named `Script`; it cannot supply output paths or compiler flags.
Portable scripts should use the shared Init library (plus Workbench when
selected). Native Lean may have other installed modules that the WASM
library does not bundle; unavailable imports are reported, not emulated.

## Native local CLI and MCP/stdin-stdout

Create `request.json` containing the request above, install the headless
package as described in `PROFILE.md`, and install native Lean 4.33.1.
From the repository root:

```sh
export LINKED_PROFILE="$PWD/labs/linked-assurance/developer-profile-scripts.json"
export LINKED_TRUST_LEAN_SOURCE=1
node labs/linked-assurance/tools/headless/cli.mjs \
  --backend node --tool linked_assurance_compile_lean --input request.json
node labs/linked-assurance/tools/headless/cli.mjs \
  --backend mcp-stdio --tool linked_assurance_compile_lean --input request.json
```

The default four-tool profile is unchanged. Both the site-owned enabled-tool
list AND the host environment opt-in must allow native source compilation.
The HTTP adapter never grants the unsandboxed `lean-source` capability, even
when that environment variable is present. An authenticated, sandboxed remote
compiler would be a separate implementation, not an implied permission here.

## Browser WebMCP

The site can enable `linked_assurance_compile_lean` in its same-origin
`developer-profile.json`, or construct a dispatcher with the supplied
`developer-profile-scripts.json` configuration. Registration uses the same
native WebMCP adapter as the other tools:

```js
const dispatcher = await createBrowserDispatcher({
  enabledTools: ['linked_assurance_compile_lean'],
  transports: ['webmcp']
});
await registerWebMCP(dispatcher);
```

The normal runtime setup still applies: matching hashed compiler assets,
HTTPS/localhost, cross-origin isolation and SharedArrayBuffer. Source
compilation has a fresh compiler instance; it never replaces the separately
checked policy module used by the UI. Calls are serialized within this
source-compiler service. Low-memory devices can still fail.

## What comes back

- `sourceSha256`: exact submitted UTF-8 source bytes.
- `compilation.accepted`: successful compiler exit without error diagnostics.
- `compilation.artifactProduced`: an actual exported `Script.olean` exists.
- `artifacts`: actual module files with byte counts and SHA-256 digests;
  base64 bytes are included only when requested.
- `diagnostics`, `stdout`, `stderr`: actual compiler output.
- `proof.placeholderDetected`: the compiler warned about `sorry`.
- `proof.policyContractChecked: false`: generic compilation does not claim to
  check a particular application policy contract.
- `proof.axiomAuditPerformed: false`: compiler acceptance permits explicit
  assumptions and is not a claim that every theorem is axiom-free.
- `compiler`: the target/runtime identity.

A compiler can accept a file containing `sorry`; that outcome is explicitly
`compiled_with_placeholders`, not a completed proof. A failed theorem is
`compile_rejected`, not a proof that the theorem is false. Exit zero without
a module is `compiler_fault`. Timeout, cancellation, missing compiler and
resource-limit results return no successful artifacts.

Native and WASM `.olean` bytes need not match. Returned modules require a
matching toolchain, target and imports. Do not load caller-supplied binary
modules from untrusted sources merely because they claim a familiar hash.
Artifacts here are returned to the developer; no public artifact upload or
arbitrary-module execution endpoint is provided.

## Compilation, checking and running are different

This tool emits Lean module artifacts. It does NOT compile a native executable
or a new standalone WASM application. It does NOT automatically install the
module as the current policy, assert its business-rule adequacy, or run a
separate runtime entry point against an RDF dataset.

`#eval`, initializers and metaprograms can execute DURING compilation. Thus
"compile only" is not an OS security sandbox. Native mode is restricted to
explicitly trusted local developer source. Source code can fabricate diagnostic
text; these receipts are developer diagnostics, not hostile-code certificates.
Browser code runs within its browser/WASM environment, but neither that host
nor its memory safety is formally verified by the profile theorems.

The existing editor still compiles edited policies against `policyAudit` and
runs them on generated fixtures. Exposing a reusable compile-token → audited
policy → arbitrary-state execution lifecycle through the tool API remains
separate work; do not confuse this generic compiler endpoint with that lifecycle.

## Limits and checks

The native path has a whole-request deadline, bounded captured output and
bounded returned artifacts; it kills the process group on Unix. On Windows
only the immediate compiler process is killed. These are operational controls,
not adversarial isolation. The browser deadline terminates an active compiler
worker and suppresses late results. Asset downloading/decompression during
setup may finish after cancellation; no compilation is started afterwards.

Tests use real Lean: valid source and `#eval`, rejected false theorem,
placeholder warning, actual Workbench import, module magic/hash, cancellation,
timeout, explicit source opt-in, and HTTP capability denial. A separate
Chromium test requires native WebMCP and checks actual emitted WASM-target
modules. CI results, not this document, determine which tests passed.
