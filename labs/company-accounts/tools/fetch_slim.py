#!/usr/bin/env python3
"""Verify and extract the slim Lean 4.33.1 WASM pair from Dickory's EXISTING
pinned cauli/lean4 GitHub Actions build. Never mix binaries or Init libraries.

The upstream Actions artifact expires in December 2026. A verified permanent
mirror is required before relying on this as a long-term build input.
"""
import hashlib
import json
import os
import pathlib
import tarfile
import tempfile
import urllib.request
import zipfile

HERE = pathlib.Path(__file__).resolve().parent
LAB = HERE.parent
UPSTREAM = json.loads((HERE / "slim-source.json").read_text())
OUTPUT = LAB / "artifacts"
OUTPUT.mkdir(parents=True,exist_ok=True)

def checksum(path):
    with open(path,"rb") as stream:
        return hashlib.file_digest(stream,"sha256").hexdigest()

def download():
    # Prefer a checked and immutable Dickory mirror once bootstrapped.
    mirror = UPSTREAM.get("mirror")
    if mirror and mirror.get("sha256") and mirror.get("url"):
        raise SystemExit("Slim mirror support requires its own immutable format; not configured yet.")
    url = UPSTREAM["archiveUrl"]
    req = urllib.request.Request(url,headers={
        "Accept":"application/vnd.github+json",
        "User-Agent":"dickory-pinned-slim-lean-builder",
    })
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if token:
        req.add_header("Authorization","Bearer "+token)
    fd, name = tempfile.mkstemp(prefix="lean-slim-source-",suffix=".zip",dir=OUTPUT)
    path=pathlib.Path(name)
    try:
        with os.fdopen(fd,"wb") as dest,urllib.request.urlopen(req,timeout=90) as response:
            while True:
                chunk=response.read(4*1024*1024)
                if not chunk:break
                dest.write(chunk)
        if path.stat().st_size != UPSTREAM["archiveBytes"] or checksum(path)!=UPSTREAM["archiveSha256"]:
            raise SystemExit("Lean 4.33.1 archive size/hash did not match pinned source identity")
        return path
    except BaseException:
        path.unlink(missing_ok=True)
        raise

def main():
    source=download()
    selected={}
    try:
        with zipfile.ZipFile(source) as z:
            if z.namelist()!=[UPSTREAM["archiveEntry"]]:
                raise SystemExit("Unexpected Lean archive layout")
            with z.open(UPSTREAM["archiveEntry"]) as comp,tarfile.open(fileobj=comp,mode="r|zst") as tar:
                for member in tar:
                    parts=pathlib.PurePosixPath(member.name).parts
                    if not parts or '..' in parts or member.name.startswith('/'):
                        raise SystemExit("Unsafe Lean archive path")
                    if not member.isfile(): continue
                    rel="/".join(parts[1:])
                    if rel not in {"bin-slim/lean.js","bin-slim/lean.wasm"}:
                        continue
                    if rel in selected:
                        raise SystemExit("Duplicate Lean slim runtime member")
                    dest=OUTPUT/("lean-slim.js" if rel.endswith(".js") else "lean-slim.wasm")
                    limit=10_000_000 if rel.endswith(".js") else 150_000_000
                    if member.size<=0 or member.size>limit:
                        raise SystemExit("Unexpected Lean slim asset size")
                    partial=dest.with_suffix(dest.suffix+".partial")
                    with tar.extractfile(member) as stream,open(partial,"wb") as out:
                        remaining=member.size
                        while remaining:
                            chunk=stream.read(min(4*1024*1024,remaining))
                            if not chunk:raise SystemExit("Truncated Lean slim runtime")
                            out.write(chunk);remaining-=len(chunk)
                    partial.replace(dest)
                    selected[rel]={"bytes":dest.stat().st_size,"sha256":checksum(dest)}
        if set(selected)!={"bin-slim/lean.js","bin-slim/lean.wasm"}:
            raise SystemExit("Pinned Lean archive did not contain both slim compiler assets")
        for key,expected in UPSTREAM.get("slimObjects",{}).items():
            if expected.get("bytes")!=selected[key]["bytes"] or expected.get("sha256")!=selected[key]["sha256"]:
                raise SystemExit("Unexpected slim asset digest: "+key)
        existing=json.loads((LAB.parent/"linked-assurance/compiler-assets.json").read_text())
        lib=existing["lean-lib.tar.gz"]
        if not (LAB.parent/"linked-assurance"/lib["url"]).is_file():
            # The real staging step prepares the already-pinned same-commit
            # Init library. Do not substitute some other release.
            print("Info: matching Init archive is prepared by Linked Assurance build")
        manifest={
            "sourceCommit":UPSTREAM["forkCommit"],
            "leanVersion":UPSTREAM["leanVersion"],
            "factoidalPin":UPSTREAM["factoidalPin"],
            "artifactArchiveSha256":UPSTREAM["archiveSha256"],
            "runtime":{
                "lean.js":{"url":"../company-accounts/artifacts/lean-slim.js",**selected["bin-slim/lean.js"]},
                "lean.wasm":{"url":"../company-accounts/artifacts/lean-slim.wasm",**selected["bin-slim/lean.wasm"]},
                "lean-lib.tar.gz":{"url":"./artifacts/toolchain-4.33.1/lean-lib.tar.gz",
                    "bytes":lib["bytes"],"sha256":lib["sha256"]},
            }
        }
        (OUTPUT/"slim-compiler-assets.json").write_text(json.dumps(manifest,indent=2)+"\n")
        print(json.dumps({"status":"pass","source":UPSTREAM["forkCommit"],"slim":selected},indent=2))
    finally:
        source.unlink(missing_ok=True)

if __name__ == "__main__":main()
