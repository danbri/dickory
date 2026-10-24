#!/usr/bin/env python3
"""Stage an explicit set of public files after the RDF lab has been verified."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import hashlib
import json
import os
import shutil

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "_site"
LAB = Path("labs/rdf11")
ARTIFACTS = LAB / "cleanroom/artifacts"
FILES = [Path("index.html"), Path("labs/index.html"), LAB / "index.html"]
FILES += [ARTIFACTS / name for name in (
    "source-review.html", "verification.json", "negative-checks.json", "declarations.json",
    "closure-execution.json", "instance-execution.json"
)]


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.paths = []

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key in ("href", "src") and value:
                url = urlsplit(value)
                if not url.scheme and not url.netloc and url.path:
                    self.paths.append(unquote(url.path))


def main():
    evidence = json.loads((ROOT / ARTIFACTS / "verification.json").read_text())
    negative = json.loads((ROOT / ARTIFACTS / "negative-checks.json").read_text())
    execution = json.loads((ROOT / ARTIFACTS / "closure-execution.json").read_text())
    instances = json.loads((ROOT / ARTIFACTS / "instance-execution.json").read_text())
    if (evidence["errors"] or negative["status"] != "pass"
            or execution["status"] != "pass" or not execution["checks"]
            or instances["status"] != "pass" or not instances["checks"]):
        raise SystemExit("Refusing to publish failing verification evidence")
    for path in FILES:
        if not (ROOT / path).is_file():
            raise SystemExit(f"Missing generated or source file: {path}")
    if OUT.exists():
        shutil.rmtree(OUT)
    for path in FILES:
        destination = OUT / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / path, destination)
    build = {
        "commit": os.environ.get("GITHUB_SHA", "local-uncommitted-preview"),
        "run": os.environ.get("GITHUB_RUN_ID"),
        "coverage": "draft; expert reviews and full coverage remain incomplete",
        "sha256": {p.as_posix(): hashlib.sha256((OUT / p).read_bytes()).hexdigest()
                   for p in FILES},
    }
    (OUT / LAB / "build.json").write_text(json.dumps(build, indent=2) + "\n")
    (OUT / ".nojekyll").touch()
    for path in FILES:
        if path.suffix != ".html":
            continue
        parser = Links()
        parser.feed((OUT / path).read_text())
        for link in parser.paths:
            target = (OUT / path.parent / link).resolve()
            if not target.is_relative_to(OUT.resolve()):
                raise SystemExit(f"Link escapes site: {path}: {link}")
            if target.is_dir():
                target /= "index.html"
            if not target.is_file():
                raise SystemExit(f"Broken local link: {path}: {link}")
    print(f"Staged {len(FILES)} files plus build identity; local links checked: {OUT}")


if __name__ == "__main__":
    main()
