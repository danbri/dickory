# Headless Linked Assurance

See [the common developer profile](PROFILE.md) for current Node/stdio,
Node/Streamable HTTP, native Chromium/WebMCP, shared schemas, state bundles,
proof obligations and runnable CLI examples.

PR #2's earlier implicit fallback and divergent credential fixture have been
replaced. Native WebMCP is now required by default; direct browser invocation
is an explicitly labelled diagnostic mode. Both runtimes expose the same four
operations and use the same state/credential preparation code.
