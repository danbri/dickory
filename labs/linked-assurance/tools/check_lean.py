#!/usr/bin/env python3
"""Kernel checks for policy contracts, concrete outcomes and a rejected mutation."""
import json
import hashlib
import os
import re
from pathlib import Path
import subprocess
root=Path(__file__).resolve().parents[1]
out=root/'artifacts/lean'
out.mkdir(parents=True,exist_ok=True)
env={**os.environ,'LEAN_PATH':str(out)}
def lean(path,*args,success=True):
    p=subprocess.run(['lean','--json',*args,str(path)],cwd=root/'lean',env=env,capture_output=True,text=True,timeout=90)
    if (p.returncode==0)!=success: raise SystemExit(p.stdout+p.stderr+f'Unexpected exit {p.returncode}')
    if success and "declaration uses 'sorry'" in p.stdout+p.stderr: raise SystemExit('Proof placeholder rejected')
    return p.stdout+p.stderr
lean(root/'lean/Workbench.lean','-o',str(out/'Workbench.olean'))
lean(root/'lean/Policy.lean','-o',str(out/'Policy.olean'))
checks='''import Policy
open LinkedAssurance
def ctx : Context := ⟨"input", "selected", "union", "RDFS", "0.35.1"⟩
def e : Evidence := ⟨ctx, .completed, [⟨"classification", "ASK {}", true⟩, ⟨"applicationCondition", "ASK {}", true⟩]⟩
def s : OperationalState := ⟨true, 10, 20, true, true, false, false⟩
example : policy e s = .permit := by decide
example : policy e {s with credentialVerified := false} = .deny := by decide
example : policy e {s with observedTime := 20} = .deny := by decide
example : policy e {s with permissionGranted := false} = .deny := by decide
example : policy {e with execution := .timeout} s = .defer := by decide
example : knowledge {e with execution := .timeout} "classification" = .notEstablished := by decide
example : policy {e with claims := []} s = .defer := by decide
example : policy {e with context := {ctx with regime := "unsupported"}} s = .deny := by decide
def alarm : Evidence := {e with claims := ⟨"alert", "ASK {}", true⟩ :: e.claims}
example : policy alarm s = .protectiveShutdown := by decide
example : attackerOutcome (policy alarm s) {s with attackerWantsInterruption := true, legitimateSession := true} = .achieved := by decide
#print axioms LinkedAssurance.policy_contract
#print axioms LinkedAssurance.timeout_no_negative
#print axioms LinkedAssurance.shutdown_can_be_attacker_success
'''
(out/'Checks.lean').write_text(checks)
output=lean(out/'Checks.lean')
messages=[json.loads(line).get('data','') for line in output.splitlines() if line.startswith('{')]
for name in ['policy_contract','timeout_no_negative','shutdown_can_be_attacker_success']:
    audits=[m for m in messages if f"'LinkedAssurance.{name}'" in m]
    if len(audits)!=1:raise SystemExit(f'Missing or ambiguous axiom audit: {name}')
    if 'does not depend on any axioms' in audits[0]:continue
    match=re.search(r'depends on axioms: \[([^\]]*)\]',audits[0])
    if not match or set(map(str.strip,match[1].split(',')))-{'propext','Quot.sound','Classical.choice'}:
        raise SystemExit(f'Unapproved axiom dependency: {audits[0]}')
broken=(root/'lean/Policy.lean').read_text().replace('else if ready e s then .permit else .deny','else .permit')
(out/'Broken.lean').write_text(broken)
negative=lean(out/'Broken.lean',success=False)
report={'status':'pass','compiler':subprocess.check_output(['lean','--version'],text=True).strip(),
'sha256':{name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in ['lean/Workbench.lean','lean/Policy.lean']},
'checks':['Workbench and Policy compiled','10 concrete outcomes proved by kernel reduction','Axiom dependencies printed','Removing the permission gate breaks the actual contract'],
'diagnostics':output,'negativeDiagnostics':negative}
(root/'artifacts/lean-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['diagnostics','negativeDiagnostics']},indent=2))
