# Lean WASM hello-world checks

These deliberately bypass the RDF/policy bridge. The same small programs run
under Node, Deno, and Chromium using identical Lean 4.33.1 WASM files and the
matching wasm32 Init `.olean`, `.ir`, and `.ir.sig` files.
The interactive page uses the lab's compact JS export loader; the Node/Deno and
reference browser harnesses use the original upstream JS.

The checks print a greeting, evaluate `2 + 2`, prove a theorem by `rfl`, reject a
false theorem with compiler status 1, recover after rejection, and evaluate a
library function. Both the outer IO result and enclosed compiler exit code are
checked. An IO success alone is insufficient. Requests return to the host event
loop between cases, and the browser checks that the page remains responsive.

The first successful run used Node 26.7.0, Deno 2.9.4, and Chromium 156.0.8078.4.
Cold Init import took 38–41 seconds; the small subsequent examples took 9–72 ms.
Reports, including source, diagnostics and runtime hashes, are written to
`artifacts/hello-*-checks.json` and are not committed.

From the repository root, obtain the exact upstream build and extract only its
runtime and core library (Python 3.14 or newer):

The smaller prepared mirror used by Pages is available with
`python3 labs/linked-assurance/tools/hello/fetch.py`. Its archive checksum is in
[web-bundle.json](web-bundle.json). The original upstream archive can instead be
prepared as follows (the upstream Actions artifact expires on 2026-12-09):

```sh
gh api repos/cauli/lean4/actions/artifacts/10171167184/zip > labs/linked-assurance/artifacts/lean-4.33.1-browser.zip
python3 labs/linked-assurance/tools/hello/prepare.py
node labs/linked-assurance/tools/hello/node.cjs
deno run -A labs/linked-assurance/tools/hello/node.cjs
node labs/linked-assurance/tools/build_browser_host.cjs
python3 labs/linked-assurance/tools/serve.py --isolate --port 8081
```

Use a current Node release; Node 22 rejects this full WASM build's export count.
Open <http://localhost:8081/labs/linked-assurance/tools/hello/> for the minimal
browser page. For the automated Chromium check, from `tools/viewer-browser`:

```sh
node linked-probe.mjs --hello
node linked-probe.mjs --startup --webkit --tasks --site=http://127.0.0.1:8081
```

The second command exercises the actual hello page, including a task that needs
the preloaded worker. On macOS it also samples new WebContent processes every
500 ms and reports aggregate peak RSS. That includes more than WASM linear
memory, but is a desktop measurement, not a prediction of an iPhone's limit.

[toolchain.json](toolchain.json) pins the successful upstream
[build](https://github.com/cauli/lean4/actions/runs/34519035716), archive and binary
checksums. `prepare.py` verifies those checksums and every Init olean's embedded
commit. The helper initialization follows the upstream Apache-2.0
[test harness](https://github.com/cauli/lean4/blob/4f9018a62ead9be0ffd652021d5afc8501e92253/tests/wasm/checks.cjs).

This matches Factoidal's Lean **release version**, not its compiled module ABI:
the browser uses a patched fork and wasm32 artifacts. Importing Factoidal Lean
modules will require a matching build of those modules. Factoidal's separate
WASM execution remains unchanged. These checks establish basic compiler
operation; they do not establish the policy bridge or module reuse.
