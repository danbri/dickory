# SWAD-Europe Company Accounts / Lean 4

An independently reviewable reconstruction of [SWAD-Europe 5.3 (2004)](https://www.w3.org/2001/sw/Europe/reports/xml_test_cases/), which was co-authored by Dan Brickley, Max Froumentin, Libby Miller and Damian Steer.

**Purpose:** place a precise financial interpretation in Lean, check consequences with actual Lean proofs, and place the original (not edited) RDF/N3, MathML, XSLT and output data beside it for falsifiable comparison. This does **not** assert that the historical N3 and MathML programs correctly implement the interpretation.

## What is specified

- Exactly one currency and a single reporting period per record.
- Money in **integer pence**; in the demonstration fixture, \`gbp n\` denotes 100n pence.
- Ratios are represented as unreduced exact \`Option (Int × Int)\` fractions, **not** floating point, and \`none\` explicitly denotes a zero denominator. \`sameExactValue\` compares fractions by cross multiplication; structural inequality of numerator/denominator pairs is **not** used to establish a numerical counterexample.
- Percentage expressions include ×100. Asset turnover and liquidity ratios are dimensionless.
- Rule 4 returns a rational estimate of headcount. It does not claim an integer-valued employee count without a separately checked divisibility condition.
- Rules 10 and 11 use **explicitly selected modern annual ratios** \`365 × debtors / annual sales\` and \`365 × stock / annual cost of sales\`. The 2004 formulas include very different factors; the lab must not silently imply equivalence.
- The current-assets model covers only stock, debtors and cash; an accounting framework with more categories requires an expanded specification.

The old report's unit conversion factors (\`1000000\`, \`100000\`, \`10000\` and \`27.29726\`) are left as **historical evidence**, not adopted as truth. A proper input adapter for \`reports.xml\` requires an independently documented mapping from each source field's encoded units into pence, people and annual reporting periods. This adapter is **not implemented** here.

## Proof-bearing results

\`lean/Accounts.lean\` contains the executable definitions and four particularly useful checked propositions:

1. \`acid_ignores_stock\`: a structural invariant under arbitrary stock replacement.
2. \`acid_undefined_at_zero_liabilities\`: an explicit undefined-denominator boundary.
3. \`archived_rule8_counterexample\`: an executable inequality between the proposed acid test and the documented incorrect N3 expression.
4. \`archived_rule10_counterexample\`: an executable inequality between the annual debtor-days convention and the N3 rule from 2004.

It also checks the rule-11 predicate-name mismatch and the current-assets component identity. Browser editing appends **fixed typed obligations** and checks the reported axioms of four mandatory theorem declarations. The separate rejection button first checks the current accepted source, then compiles a deliberately false equation, which must be rejected. A compiler crash is not reported as a proof failure.

These theorems are about a deliberately defined model. They **do not** prove the original data capture was correct, the importer or N3 engine matches the model, the WASM/compiler-host boundary is verified, or the financial interpretation is universally accepted. Source reviewers should treat those as independent obligations.

## Reproduce

With Lean 4.33.1 available on PATH:

\`\`\`sh
sh labs/company-accounts/verify.sh
python3 labs/company-accounts/fetch_sources.py
\`\`\`

\`fetch_sources.py\` checks the W3C directory listing against an explicit inventory of **51** files, retrieves them and the linked \`reports.xml\`, \`schema-content.rdf\`, \`mml_new.xsl\`, rejects missing/extra files, hashes the bytes, and embeds all **54** into \`artifacts/index.html\`. The binary archive is embedded as base64. The HTML file itself contains all retrieved source bodies and hashes; no network access to W3C is needed by the published lab. Its source inspector downloads original bytes.

The original report also links \`newdata.asc\`; at inspection it returned HTTP 404, and is not falsely represented as downloaded.

The GitHub Pages workflow fetches these sources during the site build and stages the generated HTML. The archival blobs are **not committed to Git** in this initial draft. The recorded SHA-256 hashes identify the downloaded snapshot but do **not** represent a pinned upstream revision: future W3C updates could change the served bytes. Strict byte pinning from a reviewed baseline is a separate follow-up.

## Live browser toolchain

The lab imports \`checkLean\` and \`auditContract\` from the existing
[\`linked-assurance/lean-host.js\`](../linked-assurance/lean-host.js). It therefore uses the existing pinned Lean 4.33.1 WASM binary and matching Init library. No new fake proof evaluator and no secondary compiler are introduced.

The lab has its own scoped COOP/COEP service-worker shim because the shared compiler requires cross-origin isolation and shared memory. As in Linked Assurance, mobile-browser startup and browser-side proof editing remain dependent on substantial memory availability.

## Source attribution and interpretation

Original report and directory: <https://www.w3.org/2001/sw/Europe/reports/xml_test_cases/>

The 2004 W3C historical files are preserved, credited, and identified by URL and SHA-256. They are **not relicensed** by Dickory's Apache 2.0 licence. \`THIRD_PARTY.md\` records the distinction.

The true remaining hard work is independent unit reconstruction, a typed RDF ingestion adapter, an exact interpreter for the relevant Content MathML and N3 subset, and a proof of a correspondence theorem between those parsed program representations and the Lean semantics. Displaying source beside a theorem is not such a proof.

## iPhone / mobile Lean strategy

The original Dickory browser compiler relies on a large Lean 4.33.1 WASM binary
and imported environment. Real iPhone WebKit reports show stack exhaustion, and
previous desktop WebKit investigations showed a multi-gigabyte peak. A JS
RangeError is a runtime failure, **not** Lean rejection or a refutation.

The lab therefore offers **two explicitly different paths** on mobile:

1. Inspect seven genuinely checked native Lean proofs, including all reported
   axioms and the negative test. The CI evidence is generated from actual
   `lean --json` diagnostics and tied to the exact `Accounts.lean` bytes by
   SHA-256. Modifications invalidate the evidence. It is not presented as a
   proof checked in the iPhone browser.
2. Open the current Lean source in the open-source
   [cauli Lean browser playground](https://lean.cau.li/?variant=slim), using
   its **slim on-device WASM compiler**. A compressed `#s=` URL fragment
   contains the complete text, without a server POST. Its first proof is a
   small Init-only acid-test example. A second link opens the full editable
   `Accounts.lean`. Click **Run** in that playground; only its diagnostics
   can establish a new on-device proof result. The slim binary does not
   currently have an exact-version-parity guarantee with Dickory's native
   4.33.1 compiler, and the full example has not been tested on a physical
   iPhone in this repository's CI.

The playground route is a real local prover, but hosted by a separate project.
The fragment is not sent in the HTTP request; however the destination's
JavaScript can read its contents. Do not use it for private Lean programs unless
you have reviewed the destination. Browser history can also retain the link.

A future integrated mobile runner can adapt or independently rebuild the slim
WASM variant, pin its exact artifact hashes and compiler version, run the actual
Dickory proof contracts in the phone worker, and retain the native CI record as
fallback. A remote native Lean backend is an alternative for code that cannot
be elaborated locally, but is not needed for the Init-only starting point.

The CI tests round-trip exact source through the mobile workspace codec and
exercise the source-bound proof viewer in desktop WebKit configured to emulate
an iPhone. They **do not** claim proof compilation on a physical iPhone.

## Inline, same-origin Lean 4.33.1 experiment

Factoidal Core's `formal/lean4/lean-toolchain` at commit
`57872a9b315b72cce3aca9942d909ee54d1ead99` selects
`leanprover/lean4:v4.33.1`. This lab is constrained to the **same release
version**, but a different compiler source commit:
the existing Dickory browser fork `cauli/lean4@4f9018a62ead9be0ffd652021d5afc8501e92253`.
The fork and Factoidal native release are *not* claimed ABI-identical; compiled
`.olean` files are never mixed.

The older full Dickory browser compiler had `105330` exported functions.
`tools/prune_exports.py` starts from its checksum-pinned binary and removes
unneeded public WebAssembly export entries while retaining required browser ABI
entry points and all non-function exports. It changes **only** the binary's
export section. All code, data and other sections remain unchanged. Its witness,
`artifacts/slim-transform.json`, records exact SHA-256 hashes. The existing
verified same-commit `Init.olean` and IR library are reused. The loader is
the existing compact Dickory JavaScript glue, not the unrelated 4.33.0-pre
mobile playground.

The **Verify this Lean source locally · 4.33.1** button downloads the smaller
same-origin compiler and checks actual editor bytes and four fixed theorem
types/axiom lists, then reports precise source SHA-256. Negative checking is a
separate real compiler run; a runtime fault or missing error diagnostic cannot
be counted as an expected theorem rejection.

This export-pruned runtime is not the same as cauli's own *relinked* 70 MB slim
compiler. Its memory use and physical-iPhone reliability still require direct
confirmation; do not describe successful desktop WebKit tests as iPhone proof
acceptance. The existing source-bound native CI report is preserved as a
working fallback without pretending it checked edited input.

See [third-party and modification notices](THIRD_PARTY.md) for licensing.
