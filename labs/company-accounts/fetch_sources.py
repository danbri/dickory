#!/usr/bin/env python3
"""Acquire the complete published SWAD-Europe test-directory listing and embed
its byte-exact files directly in one offline-readable Dickory lab HTML file.

The original archive is not licensed by this project. Do not rewrite, normalize
or silently repair any historical sources. This script fetches using HTTPS at
BUILD time only; the published UI never requests the 2004 W3C server.
"""
from __future__ import annotations

from base64 import b64encode
from hashlib import sha256
from html.parser import HTMLParser
from io import BytesIO
import json
from pathlib import Path
import re
import time
from urllib.parse import urljoin
from urllib.request import Request, urlopen
from zipfile import ZipFile, BadZipFile

HERE = Path(__file__).resolve().parent
BASE = "https://www.w3.org/2001/sw/Europe/reports/xml_test_cases/"
TEST_URL = BASE + "tests/"
TEST_NAMES = (
    [f"_out_cwm{i}.n3" for i in range(1, 12)]
    + [f"_out_mml{i}.txt" for i in range(1, 12)]
    + [f"cwm{i}.n3" for i in range(1, 15)]
    + [f"mmlrule{i}.mml" for i in range(1, 12)]
    + ["mmlrules.mml", "readme-cwm.txt", "readme-xslt.txt",
       "xml_company_facts_tests.zip"]
)
# Supplementary files explicitly linked from the original report; the old
# newdata.asc source is currently 404 and is recorded as unavailable in README.
RELATED = ["reports.xml", "schema-content.rdf", "mml_new.xsl"]
MAX_BYTES = 5_000_000


class Listing(HTMLParser):
    def __init__(self):
        super().__init__()
        self.names = set()

    def handle_starttag(self, tag, attrs):
        if tag != "a":
            return
        attrs = dict(attrs)
        target = attrs.get("href", "")
        if re.fullmatch(r"[A-Za-z0-9_.-]+", target):
            self.names.add(target)


def request(url: str) -> bytes:
    last = None
    for attempt in range(3):
        try:
            req = Request(url, headers={"User-Agent": "Dickory-SWAD-research/1.0 (source-provenance)"})
            with urlopen(req, timeout=35) as response:
                if response.geturl().split("?")[0].replace("http:", "https:") != url:
                    raise ValueError(f"Unexpected redirect: {response.geturl()}")
                data = response.read(MAX_BYTES + 1)
            if not data or len(data) > MAX_BYTES:
                raise ValueError(f"Empty or oversized source: {url}")
            return data
        except Exception as exc:
            last = exc
            if attempt < 2:
                time.sleep(1 + attempt)
    raise RuntimeError(f"Failed to download {url}: {last}")


def archive_file(url: str, name: str) -> dict:
    data = request(url)
    if data[:20].lstrip().lower().startswith((b"<!doctype", b"<html")):
        raise ValueError(f"HTML response returned for archive file {name}")
    entry = {"name": name, "url": url, "sha256": sha256(data).hexdigest(),
             "bytes": len(data)}
    if name.endswith(".zip"):
        try:
            with ZipFile(BytesIO(data)) as z:
                bad = z.testzip()
                if bad:
                    raise ValueError(f"Corrupt ZIP entry: {bad}")
                members = z.namelist()
                if any(p.startswith("/") or ".." in Path(p).parts for p in members):
                    raise ValueError("Unsafe ZIP member name")
                entry["members"] = members
        except BadZipFile as exc:
            raise ValueError("Bad upstream ZIP") from exc
        entry["base64"] = b64encode(data).decode("ascii")
        entry["encoding"] = "base64"
    else:
        try:
            entry["text"] = data.decode("utf-8")
            entry["encoding"] = "utf-8"
        except UnicodeDecodeError:
            # Lossless, deterministic one-byte mapping, never replacement chars.
            entry["text"] = data.decode("latin-1")
            entry["encoding"] = "latin-1"
    return entry


def main():
    listing = Listing()
    listing.feed(request(TEST_URL).decode("utf-8"))
    expected = set(TEST_NAMES)
    actual = listing.names - {"Parent Directory"}
    # We only consider files with the expected source naming patterns. A newly
    # added file is a review event rather than something silently omitted.
    relevant = {n for n in actual if n.endswith((".n3", ".txt", ".mml", ".zip"))}
    if relevant != expected:
        raise SystemExit(f"Archive inventory drift. Missing: {sorted(expected-relevant)}; "
                         f"unexpected: {sorted(relevant-expected)}")
    files = [archive_file(urljoin(TEST_URL, name), "tests/" + name)
             for name in TEST_NAMES]
    files += [archive_file(urljoin(BASE, name), name) for name in RELATED]
    if len(files) != len(TEST_NAMES) + len(RELATED):
        raise SystemExit("Incomplete download")
    manifest = [{key: row[key] for key in ("name", "url", "sha256", "bytes", "encoding")}
                for row in files]
    bundle = {
        "origin": BASE,
        "directory": TEST_URL,
        "report": BASE,
        "snapshot": "build-time HTTPS retrieval, not an upstream immutable revision",
        "completeTestDir": True,
        "testDirCount": len(TEST_NAMES),
        "relatedCount": len(RELATED),
        "files": files,
    }
    serialized = json.dumps(bundle, ensure_ascii=True, separators=(",", ":"))
    # Protect the HTML script terminator even inside text retrieved externally.
    serialized = serialized.replace("<", r"\u003c").replace(">", r"\u003e")
    template = (HERE / "index.template.html").read_text()
    marker = "<!-- ARCHIVE_JSON -->"
    if template.count(marker) != 1:
        raise SystemExit("Missing exactly one inline archive placeholder")
    html = template.replace(marker,
        '<script id="inlineArchive" type="application/json">' + serialized + '</script>')
    output = HERE / "artifacts"
    output.mkdir(exist_ok=True)
    (output / "index.html").write_text(html)
    (output / "source-manifest.json").write_text(
        json.dumps({"source": TEST_URL, "entries": manifest}, indent=2) + "\n")
    print(f"Fetched and embedded {len(TEST_NAMES)} test-dir files and {len(RELATED)} "
          f"related source files into {output / 'index.html'}")


if __name__ == "__main__":
    main()
