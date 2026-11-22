# Original Lean 4.33.1 slim WASM browser compiler — Dickory mirror

This release preserves the **unmodified, separately linked** slim compiler
from cauli/lean4 at source commit `4f9018a62ead9be0ffd652021d5afc8501e92253`.
Lean release: **4.33.1** (Factoidal Core pins `leanprover/lean4:v4.33.1`).
This fork commit is different from the official release commit; their compiled
`.olean` files are not interchangeable.

Source: [cauli/lean4, Browser toolchain run 34519035716](https://github.com/cauli/lean4/actions/runs/34519035716),
artifact `10171167184`, original full archive SHA-256
`cd942e1efcbf0a711f9a58cbbfe819fa312d845fa0d4289b032b33b7c8730d4f`.
Original GitHub Actions artifact expires on 9 December 2026; this release
remains available after that expiry.

Binary asset checksums, **verified after extraction from the full authentic archive**:

| File | Bytes | SHA-256 |
|---|---:|---|
| `lean-slim.js` | 3,458,082 | `2fd9accb23220f3d2fb569c4085e77cbe4637728d7266ff990f969afa80d3c9f` |
| `lean-slim.wasm` | 72,746,800 | `7a2e180408cf8f2e81eec26bee8f698c738ad2a96e128f8f2aff5084b3b2f3fd` |

Dickory uses its existing independently pinned, matching-commit
`Init` library archive with this slim binary, not an unrelated Lean release.
CI runs actual theorem acceptance and false-theorem rejection in browser WebKit.

**Licensing:** Original Lean software under Apache-2.0 with bundled third-party
notices (including LLVM's Apache-2.0 with LLVM exceptions). Redistributed
`LICENSE` and `LICENSES` accompany the binaries. This is an upstream
unmodified binary, not a new Dickory compiler implementation.
