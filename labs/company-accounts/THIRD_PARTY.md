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

## Inline Lean 4.33.1 mobile compiler (modified derived binary)

The on-device compiler in `artifacts/lean-slim.wasm` is **not** the
`cauli/lean4-wasm-in-browser` 4.33.0-pre binary. It is created locally during
the Dickory build from the existing, permanently mirrored
[cauli/lean4](https://github.com/cauli/lean4/tree/4f9018a62ead9be0ffd652021d5afc8501e92253)
compiler at source commit `4f9018a62ead9be0ffd652021d5afc8501e92253`,
version 4.33.1. The input WebAssembly SHA-256 is
`e24b3c712f59e983d7c805d5cc3faddd615398e820d27950834c9a3aa9e74151`.
The `prune_exports.py` transformation removes selected public function exports
from the WebAssembly export section. **All other WASM sections, including every
executable code section, are byte-for-byte unchanged.** The generated build
witness lists the retained exports, the source hash and each unchanged section
hash, and is available as `artifacts/slim-transform.json`.

The accompanying JavaScript loader and Init library come unchanged from the
already-verified Dickory 4.33.1 distribution. Their checksums are checked
separately. The on-device compiler uses Dickory's own wrapper and worker; no
JavaScript source from `cauli/lean4-wasm-in-browser` is copied for this path.

**Copyright and licences:** Lean itself is Apache-2.0. Its binary distribution
contains libraries and dependencies licensed under further terms, including
LLVM's Apache-2.0-with-LLVM-exceptions terms. Retain these complete notices:
[Lean LICENSE](../linked-assurance/vendor/lean-LICENSE) and
[Lean LICENSES](../linked-assurance/vendor/lean-LICENSES). We explicitly identify
our modified binary above; we do not overwrite upstream rights, copyright
statements or trademark provisions. The browser page links the notices.
The original historical SWAD-Europe files continue to have their own licences
and are not re-licensed by this implementation.
