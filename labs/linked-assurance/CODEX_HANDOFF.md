# Codex implementation brief — Dickory / Linked Assurance

## Objective

Build a *single-site* interactive policy lab using **actual top-level Lean 4**, not a metaphorical slider or invented pseudocode. The user edits Lean policies, RDF ontologies/graphs and operational state; compiles real Lean in the app; and runs the checked policy against Factoidal RDF entailments with explicit graph scope. The research theme is the crossover between proof **of** software and assurance **facilitated by** software.

## Respect existing Dickory

- Preserve labs/rdf11/ and its Lean 4.33.1 verification.
- Extend existing tools/build_site.py whitelist and .github/workflows/labs.yml, never add a competing Pages deployer.
- Publish at /dickory/labs/linked-assurance/. Assets must be relative. The import branch has already staged files and navigation.
- Keep this work isolated on a draft PR until validated.

## Tasks, in order

1. Replace the slider and every illustrative policy-view string with a **real Lean 4 policy editor** and an explicit catalogue of small runnable policy examples.
2. Preserve arbitrary RDF vocabulary as **runtime RDF terms**; no generated Lean class per fresh ontology IRI. Add concise reusable Lean vocabulary bindings, propositions, semantic-evidence structures and a policy outcome type. All examples must compile as real Lean.
3. Make data scope explicit: dataset, **default graph**, named graph(s), selected ontology graph(s), active graph, RDFS/simple/other entailment regime and precise external assumption set. Do not silently merge named graphs as default graph.
4. Embed actual Lean WASM compilation and diagnostics. Draft lean-host.js imports MIT lean4.js@0.0.2, but it is not wired. Browser pthreads need COOP/COEP and SharedArrayBuffer. GitHub Pages doesn't support arbitrary response headers. Test the service worker carefully; if not sufficient, use a configurable host with one integrated UI. **Never simulate compilation success.**
5. Evaluate RDF in a killable dedicated Worker (draft rdf-worker.js). Expose a wall-clock budget, default 10 seconds. On timeout terminate the worker and report execution timeout, not false entailment or denied policy.
6. Separate operational state: current/observed time, credential validity, signature verified by actual trusted operation vs merely asserted RDF signature flag, transport and encryption state, application permissions, resource exhaustion.
7. Distinguish four dimensions: (a) semantics entailed/refuted/unknown/inconsistent/unsupported; (b) execution completed/timed out/fault; (c) policy allow/deny/defer/escalate/shutdown; (d) attacker objective achieved/failed/unknown. A malicious false-positive alarm causing shutdown may be **attacker success** despite a protective action by defender.
8. Make policy compilation distinct from runtime evaluation; repeated runtime datasets/state changes must not require recompilation where the theorem is parametric.
9. Build a real Lean theorem corpus: allow implies credentials verified, allow implies unexpired, timeout doesn't prove bad content, shutdown is not attacker failure; no sorry/axioms/native_decide shortcuts. Show diagnostics and negative proof tests.
10. Expose manifest hash/version for RDF graph(s), ontology, SPARQL/entailment, Lean source, runtime flags and compile result. A Lean proof about booleans is NOT yet a proof that Factoidal marshalled the RDF evidence correctly.
11. Browser smoke tests for four demos and alternatives, new RDF subclass vocabularies, graph scoping, expired credentials, malicious false alerts, unsupported entailments, timeout, and failing Lean compilation. Keep a precise CI report.

## Prior prototype status

- Browser-tested Factoidal via published browser.js; query(...,{output:'json',entail:'RDFS'}) gives SPARQL Results JSON. SELECT's default return type is otherwise Map rows.
- Four demos: artificial purchaser/Offer, event attendee & consent, artifact release, and novel subclass vocab.
- HTML, CSS, JS are imported; current app.js is still a demonstration, not the requested final language/editor.
- Draft lean-host.js and rdf-worker.js are included but not wired.
- Pseudocode policy slider is slated for removal.
- Existing Hatchable URL is separate and not the desired repo/hosting destination.

## Formal boundaries

RDFS and OWL disjointness/negative entailment are not interchangeable. Open-world unknown is not negation. FOAF/schema Person do not mean necessarily alive/legal/capable. An asserted signature state is not cryptographic evidence. Lean kernel checking a proposition about injected data doesn't prove the origin/marshalling of those inputs. Maintain explicit status distinctions.

## References

- https://github.com/danbri/dickory
- https://github.com/danbri/factoidal-core
- https://github.com/timqian/lean4.js
- https://github.com/cauli/lean4-wasm-in-browser

Do NOT modify Factoidal or echochamber in this MVP.
