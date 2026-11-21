#!/usr/bin/env python3
"""Validate byte-exact completeness of the HTML-embedded original archive."""
import base64
import hashlib
import json
from pathlib import Path
import re
from fetch_sources import TEST_NAMES, RELATED

HERE = Path(__file__).resolve().parent
html = (HERE / "artifacts/index.html").read_text()
match = re.search(r'<script id="inlineArchive" type="application/json">([^<]+)</script>', html)
assert match, "No inline historical source block"
bundle = json.loads(match.group(1))
files = bundle["files"]
assert bundle["completeTestDir"] is True
assert bundle["testDirCount"] == 51
assert bundle["relatedCount"] == 3
assert len(files) == len(TEST_NAMES) + len(RELATED)
assert {f["name"] for f in files} == (
    {"tests/" + n for n in TEST_NAMES} | set(RELATED))
for file in files:
    if file["encoding"] == "base64":
        original = base64.b64decode(file["base64"], validate=True)
    else:
        original = file["text"].encode(file["encoding"])
    assert len(original) == file["bytes"], file["name"]
    assert hashlib.sha256(original).hexdigest() == file["sha256"], file["name"]
print(f"{len(files)} complete inline sources, all byte sizes and SHA-256 values verified")
