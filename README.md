# Dickory

Experiments in mapping specifications to formal definitions and proofs, with reviewable source provenance.

- [Labs website](https://danbri.github.io/dickory/)
- [RDF 1.1 Semantics → Lean 4](labs/rdf11/cleanroom/README.md)
- [Spec2Lean requirements](labs/rdf11/spec2lean-requirements.md)
- [Build and publication status](https://github.com/danbri/dickory/actions/workflows/labs.yml)

The first lab is an incomplete, source-first reconstruction. Mechanical checks do not establish extraction fidelity, expert acceptance, complete RDF conformance, or correctness of the Factoidal npm package.

## Reproduce the RDF lab

Install Lean **4.33.1** (the lab's `lean-toolchain` selects it when using elan) and Python **3.14.7**. The exact Python version is recorded in the frozen source catalogue. No third-party Python packages are needed.

From the repository root:

```sh
cd labs/rdf11/cleanroom
python3 tools/verify.py
python3 tools/negative_checks.py
python3 tools/review_viewer.py
cd ../../..
python3 tools/build_site.py
python3 -m http.server --directory _site 8000
```

Open <http://localhost:8000/>. Generated evidence and the viewer are rebuilt locally and in CI; they are not committed. `_site/` contains only the explicitly selected public outputs.

The workflow verifies the lab on pushes and pull requests. Publication runs only from `main`, after verification succeeds. The stricter `verify.py --require-complete` gate deliberately fails for this draft: unresolved coverage remains visible in the published evidence.

CI also checks that the review viewer displays actual Lean definition/proof bodies, expands dependencies and retains claim links on reload. To run these browser checks after staging `_site/`, use `npm ci`, `npx playwright install chromium`, and `npm test` from `tools/viewer-browser/` (Node.js 20 or later). Screenshots and the check report go into the lab's ignored `artifacts/viewer-browser/` folder.

## GitHub Pages setup

In **Settings → Pages → Build and deployment → Source**, select **GitHub Actions**. Then run the **Verify labs and publish Pages** workflow on `main` (or push a change). The expected address is <https://danbri.github.io/dickory/>. Pages must be enabled before the deployment job can succeed.

## Licensing and provenance

Project additions use the repository's Apache 2.0 licence. The archived W3C specifications retain their own copyright notices and document licence; see [THIRD_PARTY.md](THIRD_PARTY.md). [Import provenance](labs/rdf11/publication-provenance.json) records the original Lean hashes and documentation adjustments.
