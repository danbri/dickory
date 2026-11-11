# External components

- `vendor/lean4.js` derives from **lean4.js 0.0.2**, by timqian,
  <https://github.com/timqian/lean4.js>, MIT. The npm package declares MIT
  and includes its README but no separate license file. That README is
  preserved as `vendor/lean4-README.md`. The published tarball is
  <https://registry.npmjs.org/lean4.js/-/lean4.js-0.0.2.tgz>, with npm integrity
  `sha512-9+lDBDENkqxJPkdtnkSPTPVocca+yFChxrAf5ZEV4UF7kaKFER7Vy4jqzKqKcOSUEbsHrcZ3dr4BnNo3/8ef2Q==`.
  Local changes select module names, return generated module artifacts for
  reuse, retain the compiler's returned exit code, and verify downloaded assets
  against `compiler-assets.json`. The SDK is part of the trusted execution host.
- `vendor/fflate.js` is the unchanged browser ESM entry of **fflate 0.8.2**,
  <https://github.com/101arrowz/fflate>, MIT. Its complete copyright and license
  notice is preserved in `vendor/fflate-LICENSE.txt`.
- The Lean compiler binaries and library archive are external downloads from
  <https://lean4-wasm.timqian.com/v0.0.0/>. Lean is Apache-2.0, with upstream
  notices and dependencies: <https://github.com/leanprover/lean4>.
  The SDK credits the WASM port at <https://github.com/cauli/lean4>.
  Exact asset byte lengths and SHA-256 hashes are in `compiler-assets.json`.
  These binaries are not committed or staged into the public site.
- **@factoidal/core 0.35.1** is loaded from its versioned npm browser entry.
  Source: <https://github.com/danbri/factoidal-core>. Native-runtime tests install
  the same version through `package-lock.json`. Factoidal's original notices
  remain in its package; no implementation files are copied into this lab.
