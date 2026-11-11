# Linked Assurance — Lean 4 × RDF workbench (experimental)

Imported standalone lab exploring the crossover between verification **of** software and verification **facilitated by** software. This is NOT an end-to-end verified RDF-to-Lean assurance system.

## Files

- index.html / style.css / app.js: browser UI and four editable RDF examples.
- scenarios.js: synthetic instance graphs, ontologies, illustrative Lean source.
- lean-host.js: draft in-app Lean4.js WASM compiler adapter **not yet wired**.
- rdf-worker.js: draft killable Factoidal query worker **not yet wired**.
- coi-sw.js: experimental COOP/COEP service worker **not established to work on Pages**.
- CODEX_HANDOFF.md: next implementation brief.

## Observed behaviour and limits

The prototype uses the released Factoidal browser module at https://danbri.github.io/factoidal/npm/factoidal/browser.js. Its SELECT results are accessed using output:'json'; RDFS inference is selected using entail:'RDFS'. The original hosted prototype was browser-tested for four examples and nine alternate datasets.

Currently app.js opens an external Lean playground, and its slider displays **policy pseudocode**. Both must be replaced with the user's requested real top-level Lean 4 editor and an **integrated** compiler. The UI has no complete RDF-to-Lean refinement theorem.

The OWL disjointness demo reads explicit ontology axioms but is not a complete OWL negative-classification/consistency checker. An RDF flag saying a signature was verified is not actual cryptographic verification.

## Pages integration

Dickory's existing tools/build_site.py stages this lab by explicit whitelist, and .github/workflows/labs.yml publishes the site. Do not add another Pages workflow. All HTML assets are relative to this lab directory under /dickory/labs/linked-assurance/.

A real in-app Lean compiler using SharedArrayBuffer needs cross-origin isolation. GitHub Pages normally doesn't expose configurable COOP/COEP headers; the included COI service worker is a draft, not proven. Investigate and test honestly, or host the compiler on a configurable origin within one unified UI.

Dickory additions are Apache-2.0; lean4.js itself is MIT. External binaries are not vendored in this import.
