# External components

- `vendor/lean4.js` derives from **lean4.js 0.0.2**, by timqian,
  <https://github.com/timqian/lean4.js>, MIT. The npm package declares MIT
  and includes its README but no separate license file. That README is
  preserved as `vendor/lean4-README.md`. The published tarball is
  <https://registry.npmjs.org/lean4.js/-/lean4.js-0.0.2.tgz>, with npm integrity
  `sha512-9+lDBDENkqxJPkdtnkSPTPVocca+yFChxrAf5ZEV4UF7kaKFER7Vy4jqzKqKcOSUEbsHrcZ3dr4BnNo3/8ef2Q==`.
  Retained for the history of the earlier experiment; the active host is now
  `compiler.js` and `compiler-worker.js` and does not load this SDK.
- `vendor/fflate.js` is the unchanged browser ESM entry of **fflate 0.8.2**,
  <https://github.com/101arrowz/fflate>, MIT. Its complete copyright and license
  notice is preserved in `vendor/fflate-LICENSE.txt`.
- The Lean 4.33.1 compiler WASM and Init artifacts come unchanged from
  [cauli/lean4 build 34519035716](https://github.com/cauli/lean4/actions/runs/34519035716),
  commit `4f9018a62ead9be0ffd652021d5afc8501e92253`. The host initialization and
  UInt32 result decoding follow that fork's `tests/wasm` harness. Lean is
  Apache-2.0; [license](vendor/lean-LICENSE) and bundled
  [dependency notices](vendor/lean-LICENSES) are preserved. The local preparation
  script selects the Init closure and repacks it, without editing WASM or library bytes.
  `tools/build_browser_host.cjs` derives a smaller browser JS loader by replacing
  generated export assignments with a checked equivalent loop. Node and the
  reference browser harness retain the original JS. The browser-loader checksum
  is recorded separately from the upstream compiler identity.
  `tools/hello/toolchain.json` pins the upstream archive and binaries;
  `tools/hello/web-bundle.json` pins the mirror archive used by Pages.
  `compiler-assets.json` pins the three assets checked by the browser host.
- **@factoidal/core 0.35.1** is loaded from its versioned npm browser entry.
  Source: <https://github.com/danbri/factoidal-core>. Native-runtime tests install
  the same version through `package-lock.json`. Factoidal's original notices
  remain in its package; no implementation files are copied into this lab.
