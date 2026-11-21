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
