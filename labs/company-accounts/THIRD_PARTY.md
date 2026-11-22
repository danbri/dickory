# Third-party historical material

The original 2004 SWAD-Europe company-accounts test cases belong to the
W3C SWAD-Europe project and its contributors. The report is credited to
Dan Brickley, Max Froumentin, Libby Miller and Damian Steer.

Original work: https://www.w3.org/2001/sw/Europe/reports/xml_test_cases/
Test directory: https://www.w3.org/2001/sw/Europe/reports/xml_test_cases/tests/

During the verified website build, \`fetch_sources.py\` retrieves the 51 items
linked in the test directory and three related report files. Each original
file is preserved byte-for-byte in the generated HTML as either text (with its
reversible decoding recorded) or base64 (the original ZIP). URLs, lengths and
SHA-256 hashes accompany each. Do not interpret this as an upstream
content-addressed revision: W3C's currently served bytes can change.

These files are **not** copyright-free, are not represented as public-domain,
and are **not** relicensed under Dickory's Apache-2.0 licence. Their reuse
remains subject to the applicable W3C documentation and software licence
terms, depending on the file. The archive is included to allow verification
of the project's historical mathematics and standard interfaces.

All new Lean model, UI, downloader and proof-audit scripts are additions
to Dickory; see the root LICENSE. This preservation makes no claim that the
interpretation in \`lean/Accounts.lean\` is endorsed by the original authors.

## Inline Lean 4.33.1 mobile compiler (original upstream slim distribution)

The same-origin runtime is the **unmodified, separately linked** slim variant
built by [cauli/lean4](https://github.com/cauli/lean4/tree/4f9018a62ead9be0ffd652021d5afc8501e92253)
at commit `4f9018a62ead9be0ffd652021d5afc8501e92253`, version **4.33.1**.
The exact original GitHub Actions build is
[run 34519035716](https://github.com/cauli/lean4/actions/runs/34519035716),
artifact `10171167184`, uploaded 10 September 2026.

The entire source artifact is authenticated with SHA-256
`cd942e1efcbf0a711f9a58cbbfe819fa312d845fa0d4289b032b33b7c8730d4f`
before we extract `bin-slim/lean.js` or `bin-slim/lean.wasm`.
The public `nightly.link` redirect is used only to retrieve the public
GitHub Actions archive; it is **not** a source of trust. Object hashes
and byte counts are recorded in the generated
`artifacts/slim-source-provenance.json` and `slim-compiler-assets.json`.
We do **not** rewrite, relink or prune the upstream binary.
The accompanying same-commit `Init` library and executable IR come from
Dickory's already permanent, SHA-256-verified 4.33.1 release.
The byte-stable full and slim binaries are independent and must not be
mixed with other `.olean` compiler commits.

The browser host and worker are Dickory's own JavaScript, adapted from
cauli's 4.33.1 WASM test harness, as explained in
[Linked Assurance](../linked-assurance/THIRD_PARTY.md). The source code of
`cauli/lean4-wasm-in-browser` is not copied into Dickory's on-device runner.

**Copyright and licences:** Lean itself is Apache-2.0. Its binary distribution
contains third-party components licensed under further terms, including
LLVM's Apache-2.0-with-LLVM-exceptions terms. Retain the complete
[Lean LICENSE](../linked-assurance/vendor/lean-LICENSE) and
[Lean LICENSES](../linked-assurance/vendor/lean-LICENSES) notices.
Redistribution is permitted under those conditions. The historical 2004
SWAD-Europe files remain independently licensed and are not relicensed by
this implementation.

The archived upstream Actions artifact expires on 9 December 2026; a permanent
Dickory mirror (and independently pinned sha256) is required for future
reproducible builds. This limitation is explicit until the mirror exists.
