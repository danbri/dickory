#!/usr/bin/env python3
"""Check the mathematical developer-profile model with native Lean.

No native_decide or unreviewed axioms. This does not prove the JavaScript
implementation, JSON parsing, wire protocol, or browser/runtime safety.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
out = root / 'artifacts'
out.mkdir(exist_ok=True)
source = root / 'lean/DeveloperProfile.lean'
p = subprocess.run(['lean', '--json', str(source)], cwd=root, capture_output=True,
                   text=True, timeout=120)
text = p.stdout + '\n' + p.stderr
if p.returncode:
    raise SystemExit(text)
messages = []
for line in text.splitlines():
    try:
        record = json.loads(line)
    except ValueError:
        continue
    if record.get('severity') == 'error' or record.get('kind') == 'hasSorry':
        raise SystemExit(text)
    messages.append(str(record.get('data', record.get('message', ''))))
checks = ['required_missing', 'resolve_sound', 'resolved_value_idempotent',
          'admission_sound', 'restriction_monotone', 'transport_independent_result']
for name in checks:
    findings = [m for m in messages if f"'LinkedAssurance.DeveloperProfile.{name}'" in m]
    if len(findings) != 1:
        raise SystemExit(f'Missing/ambiguous axiom audit: {name}\n{text}')
    if 'does not depend on any axioms' in findings[0]:
        continue
    deps = re.search(r'depends on axioms: \[([^\]]*)\]', findings[0])
    if not deps or set(filter(None, map(str.strip, deps[1].split(',')))) - {'propext', 'Quot.sound', 'Classical.choice'}:
        raise SystemExit(f'Unapproved axiom dependency: {findings[0]}')
files = ['lean/DeveloperProfile.lean', 'profile/core.js', 'profile/catalogue.js',
         'profile/policy-input.js', 'profile/webmcp.js', 'headless-contract.js',
         'headless-webmcp.js', 'developer-profile.json']
report = {'status': 'pass', 'compiler': subprocess.check_output(['lean', '--version'], text=True).strip(),
          'checks': checks, 'diagnostics': text,
          'sha256': {s: hashlib.sha256((root / s).read_bytes()).hexdigest() for s in files},
          'boundary': 'Kernel-checked mathematical model. JavaScript refinement and protocol/runtime conformance are separate tests and assumptions.'}
(out / 'developer-profile-checks.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'diagnostics'}, indent=2))
