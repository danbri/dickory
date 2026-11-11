#!/usr/bin/env python3
"""Verify and stream-extract only the pinned runtime and Init closure. Python >=3.14."""
import hashlib
import gzip
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import zipfile

here=Path(__file__).resolve().parent
manifest=json.loads((here/'toolchain.json').read_text())
artifacts=here.parents[1]/'artifacts'
archive=artifacts/'lean-4.33.1-browser.zip'
if not archive.is_file():
    raise SystemExit('Download the pinned archive using the command in tools/hello/README.md first.')
with archive.open('rb') as f:
    digest=hashlib.file_digest(f,'sha256').hexdigest()
if archive.stat().st_size!=manifest['archiveBytes'] or digest!=manifest['archiveSha256']:
    raise SystemExit('Compiler archive checksum mismatch')
out=artifacts/'toolchain-4.33.1'
out.mkdir(exist_ok=True)
listing=[]
with zipfile.ZipFile(archive) as z:
    if z.namelist()!=['lean-4.33.1-linux_wasm32.tar.zst']:
        raise SystemExit('Unexpected artifact layout')
    with z.open(z.namelist()[0]) as compressed,tarfile.open(fileobj=compressed,mode='r|zst') as t:
        for m in t:
            if not m.isfile():continue
            parts=PurePosixPath(m.name).parts[1:]
            if '..' in parts:raise SystemExit('Unsafe archive path')
            rel='/'.join(parts)
            core=rel.startswith('lib/lean/Init/') or rel.startswith('lib/lean/Init.')
            if not (rel in ['bin/lean.js','bin/lean.wasm'] or core and rel.endswith(('.olean','.ir','.ir.sig'))):continue
            dest=out/rel
            dest.parent.mkdir(parents=True,exist_ok=True)
            with t.extractfile(m) as source,dest.open('wb') as target:shutil.copyfileobj(source,target)
            listing.append({'name':rel,'bytes':m.size})
for name,expected in manifest['objects'].items():
    p=out/'bin'/name
    with p.open('rb') as f:actual=hashlib.file_digest(f,'sha256').hexdigest()
    if p.stat().st_size!=expected['bytes'] or actual!=expected['sha256']:raise SystemExit('Wrong runtime object: '+name)
for entry in listing:
    if entry['name'].endswith('.olean'):
        with (out/entry['name']).open('rb') as f:header=f.read(88)
        if not header.startswith(b'olean') or manifest['leanCommit'].encode() not in header:
            raise SystemExit('Mismatched olean: '+entry['name'])
# Node/Deno pthreads must load the Emscripten glue as CommonJS inside this ESM lab.
(out/'bin/package.json').write_text('{"type":"commonjs"}\n')
(artifacts/'toolchain-4.33.1-files.json').write_text(json.dumps(listing,indent=2)+'\n')
# Compact transport for the app; preserve the same authenticated library bytes.
packed=out/'lean-lib.tar.gz'
with packed.open('wb') as raw,gzip.GzipFile(fileobj=raw,mode='wb',mtime=0,filename='') as gz,tarfile.open(fileobj=gz,mode='w|',format=tarfile.USTAR_FORMAT) as tar:
    for p in sorted((out/'lib/lean').rglob('*')):
        if not p.is_file():continue
        info=tarfile.TarInfo(p.relative_to(out/'lib/lean').as_posix())
        info.size=p.stat().st_size;info.mode=0o644
        with p.open('rb') as f:tar.addfile(info,f)
print(f'Verified {len(listing)} files ({sum(x["bytes"] for x in listing):,} bytes) at {out}')
