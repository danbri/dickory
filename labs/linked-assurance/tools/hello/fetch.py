#!/usr/bin/env python3
"""Fetch the pinned prepared compiler mirror; never use an unverified archive."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import urllib.request

here = Path(__file__).resolve().parent
lab = here.parents[1]
manifest = json.loads((here / 'web-bundle.json').read_text())
artifacts = lab / 'artifacts'
artifacts.mkdir(exist_ok=True)
archive = artifacts / 'lean-4.33.1-web.tar.gz'
if not archive.exists():
    partial = archive.with_suffix('.partial')
    with urllib.request.urlopen(manifest['url']) as source, partial.open('wb') as target:
        shutil.copyfileobj(source, target)
    partial.replace(archive)
with archive.open('rb') as f:
    digest = hashlib.file_digest(f, 'sha256').hexdigest()
if archive.stat().st_size != manifest['bytes'] or digest != manifest['sha256']:
    raise SystemExit('Compiler mirror archive checksum mismatch')
with tarfile.open(archive) as tar:
    members = []
    for member in tar.getmembers():
        path = Path(member.name)
        # macOS tar's AppleDouble metadata is not part of the compiler.
        if any(part.startswith('._') for part in path.parts):
            continue
        if path.is_absolute() or '..' in path.parts or not path.parts or path.parts[0] not in (
            'toolchain-4.33.1', 'toolchain-4.33.1-files.json'):
            raise SystemExit('Unexpected compiler archive path')
        if not (member.isfile() or member.isdir()):
            raise SystemExit('Unexpected compiler archive entry')
        members.append(member)
    tar.extractall(artifacts, members=members, filter='data')
for name, expected in json.loads((lab / 'compiler-assets.json').read_text()).items():
    path = lab / expected['url']
    with path.open('rb') as f:
        digest = hashlib.file_digest(f, 'sha256').hexdigest()
    if path.stat().st_size != expected['bytes'] or digest != expected['sha256']:
        raise SystemExit('Compiler asset checksum mismatch: ' + name)
print('Verified and prepared Lean 4.33.1 browser assets')
