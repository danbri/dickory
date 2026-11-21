# SWAD-Europe Company Accounts / Lean 4

An independently reviewable reconstruction of [SWAD-Europe 5.3 (2004)](https://www.w3.org/2001/sw/Europe/reports/xml_test_cases/), which was co-authored by Dan Brickley, Max Froumentin, Libby Miller and Damian Steer.

**Purpose:** place a precise financial interpretation in Lean, check consequences with actual Lean proofs, and place the original (not edited) RDF/N3, MathML, XSLT and output data beside it for falsifiable comparison. This does **not** assert that the historical N3 and MathML programs correctly implement the interpretation.

## What is specified

- Exactly one currency and a single reporting period per record.
- Money in **integer pence**; in the demonstration fixture, \`gbp n\` denotes 100n pence.
- Ratios are represented as unreduced exact \`Option (Int × Int)\` fractions, **not** floating point, and \`none\` explicitly denotes a zero denominator.
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
