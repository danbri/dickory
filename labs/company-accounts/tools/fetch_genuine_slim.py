#!/usr/bin/env python3
"""Extract the genuine, separately linked slim WASM from the EXACT cauli/lean4
4.33.1 Actions build that Dickory already pins for its full compiler.

The public nightly.link proxy issues temporary, authenticated URLs for public
GitHub artifacts. Trust is NEVER placed in the proxy: independently verify the
ENTIRE 681MB archive against the existing pinned SHA-256 before extraction.
After initial review/publishing, a permanent Dickory release mirror will replace
the expiring Actions origin. No binary relinking or export editing occurs here.
"""
from __future__ import annotations
import hashlib
import json
import pathlib
import tarfile
import tempfile
import urllib.request
import zipfile

HERE=pathlib.Path(__file__).resolve().parent
COMPANY=HERE.parent
LINKED=COMPANY.parent/"linked-assurance"
OUT=COMPANY/"artifacts"
OUT.mkdir(parents=True,exist_ok=True)
PIN="4f9018a62ead9be0ffd652021d5afc8501e92253"
VERSION="4.33.1"
ARCHIVE_URL="https://nightly.link/cauli/lean4/suites/93513831068/artifacts/10171167184"
ARCHIVE_SIZE=681781041
ARCHIVE_SHA="cd942e1efcbf0a711f9a58cbbfe819fa312d845fa0d4289b032b33b7c8730d4f"
INNER="lean-4.33.1-linux_wasm32.tar.zst"
EXPECTED={"bin-slim/lean.js":"lean-slim.js","bin-slim/lean.wasm":"lean-slim.wasm"}
MAX_SIZES={"bin-slim/lean.js":12_000_000,"bin-slim/lean.wasm":110_000_000}

def sha256_file(path):
    with open(path,"rb") as stream:return hashlib.file_digest(stream,"sha256").hexdigest()

def download():
    fd,tmp=tempfile.mkstemp(prefix="slim-upstream-",suffix=".zip",dir=OUT)
    target=pathlib.Path(tmp)
    try:
        with open(fd,"wb") as output,urllib.request.urlopen(
            urllib.request.Request(ARCHIVE_URL,headers={"User-Agent":"DickorySlimBuild/1.0"}),
            timeout=120) as response:
            # A successful proxy redirect is NOT itself a trustworthy build.
            if response.status!=200 or not (
                response.headers.get("Content-Type","").startswith("application/zip") or
                response.headers.get("Content-Type","").startswith("application/octet-stream")):
                raise SystemExit("Unexpected upstream archive response type")
            while chunk:=response.read(8*1024*1024):
                output.write(chunk)
        if target.stat().st_size!=ARCHIVE_SIZE or sha256_file(target)!=ARCHIVE_SHA:
            raise SystemExit("Original cauli Lean 4.33.1 Actions archive SHA-256 mismatch")
        print("Authenticated upstream Actions ZIP SHA-256:",ARCHIVE_SHA)
        return target
    except BaseException:
        target.unlink(missing_ok=True)
        raise

def main():
    archive=download()
    result={}
    try:
        with zipfile.ZipFile(archive) as z:
            if z.namelist()!=[INNER]:
                raise SystemExit("Unexpected upstream ZIP inventory")
            with z.open(INNER) as compressed,tarfile.open(fileobj=compressed,mode="r|zst") as entries:
                for entry in entries:
                    parts=pathlib.PurePosixPath(entry.name).parts
                    if not parts or ".." in parts or entry.name.startswith("/"):
                        raise SystemExit("Unsafe upstream TAR member")
                    if not entry.isfile():
                        continue
                    rel="/".join(parts[1:])
                    if rel not in EXPECTED:continue
                    if rel in result:
                        raise SystemExit("Duplicate upstream slim file: "+rel)
                    if entry.size<=0 or entry.size>MAX_SIZES[rel]:
                        raise SystemExit("Invalid upstream slim object size: "+rel)
                    dest=OUT/EXPECTED[rel]
                    partial=dest.with_suffix(dest.suffix+".partial")
                    with entries.extractfile(entry) as src,partial.open("wb") as output:
                        remaining=entry.size
                        while remaining:
                            b=src.read(min(4*1024*1024,remaining))
                            if not b:raise SystemExit("Truncated original slim object")
                            output.write(b);remaining-=len(b)
                    partial.replace(dest)
                    result[rel]={"bytes":dest.stat().st_size,"sha256":sha256_file(dest)}
        if set(result)!=set(EXPECTED):
            raise SystemExit("Pinned upstream archive did not contain both slim objects")
        published=json.loads((LINKED/"compiler-assets.json").read_text())
        library=published["lean-lib.tar.gz"]
        manifest={
            "sourceCommit":PIN,"leanVersion":VERSION,
            "factoidalPin":"leanprover/lean4:v4.33.1",
            "origin":{
                "type":"cauli/lean4 GitHub Actions artifact, publicly proxied and SHA-256 checked",
                "run":34519035716,"artifactId":10171167184,
                "archiveSha256":ARCHIVE_SHA,"archiveBytes":ARCHIVE_SIZE
            },
            "runtime":{
                "lean.js":{
                    "url":"../company-accounts/artifacts/lean-slim.js",
                    **result["bin-slim/lean.js"]
                },
                "lean.wasm":{
                    "url":"../company-accounts/artifacts/lean-slim.wasm",
                    **result["bin-slim/lean.wasm"]
                },
                "lean-lib.tar.gz":{
                    "url":"./artifacts/toolchain-4.33.1/lean-lib.tar.gz",
                    "bytes":library["bytes"],"sha256":library["sha256"]
                }
            }
        }
        (OUT/"slim-compiler-assets.json").write_text(json.dumps(manifest,indent=2)+"\n")
        (OUT/"slim-source-provenance.json").write_text(json.dumps({
            "sourceCommit":PIN,"leanVersion":VERSION,
            "archiveSha256":ARCHIVE_SHA,
            "objects":result,
            "transformation":"None: original genuine separately linked slim Lean compiler bytes",
            "matchingInitSha256":library["sha256"]
        },indent=2)+"\n")
        print(json.dumps({"status":"pass","sourceCommit":PIN,"originalSlimObjects":result},indent=2))
    finally:
        archive.unlink(missing_ok=True)

if __name__=="__main__":main()
