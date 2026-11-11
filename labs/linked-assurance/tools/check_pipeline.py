#!/usr/bin/env python3
"""Check the adapter as an actual Factoidal Stage, from the pinned git sources.

Only the transitive Lean source imports are materialised under artifacts/.
Never writes to the supplied Factoidal checkout or imports Dickory RDF11.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

p=argparse.ArgumentParser()
p.add_argument('--factoidal',type=Path,required=True)
a=p.parse_args()
root=Path(__file__).resolve().parents[1]
# Same identity as evidence.js / the npm build manifest, explicitly fixed here.
commit='6f57afba14e04ed648358e4693790edff69a6cd3'
out=root/'artifacts/pipeline-native'
out.mkdir(parents=True,exist_ok=True)
env={**os.environ,'LEAN_PATH':os.pathsep.join([str(out),str(root/'artifacts/lean')])}
hashes={}
done=set()
def compile_module(name):
    if name in done:return
    relative=name.replace('.','/')+'.lean'
    data=subprocess.check_output(['git','-C',str(a.factoidal.resolve()),'show',f'{commit}:formal/lean4/{relative}'])
    source=data.decode()
    for imports in re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)',source,re.M):
        for dep in imports.split():
            if dep.startswith('L4Factoidal.'):compile_module(dep)
    file=out/relative
    file.parent.mkdir(parents=True,exist_ok=True)
    file.write_bytes(data)
    run(['lean','--json','-o',str(file.with_suffix('.olean')),relative],out)
    hashes[relative]=hashlib.sha256(data).hexdigest()
    done.add(name)
def run(cmd,cwd):
    result=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True,timeout=180)
    if result.returncode or re.search(r"declaration uses [`']sorry[`']",result.stdout):raise SystemExit(result.stdout+result.stderr)
    return result.stdout
compile_module('L4Factoidal.Dataflow.Stage')
bridge=root/'lean/PipelineBridge.lean'
diagnostics=run(['lean','--json',str(bridge)],root/'lean')
audits=[json.loads(line).get('data','') for line in diagnostics.splitlines() if line.startswith('{')]
audits=[message for message in audits if "'LinkedAssurance.adaptedPolicyStage_sound'" in message]
if len(audits)!=1:raise SystemExit('Missing bridge axiom report: '+diagnostics)
if 'does not depend on any axioms' not in audits[0]:
    match=re.search(r'depends on axioms: \[([^\]]*)\]',audits[0])
    if not match or set(map(str.strip,match[1].split(',')))-{'propext','Quot.sound','Classical.choice'}:
        raise SystemExit('Unapproved bridge axiom dependency: '+audits[0])
hashes['PipelineBridge.lean']=hashlib.sha256(bridge.read_bytes()).hexdigest()
report={'status':'pass','factoidalCommit':commit,'nativeOnly':True,'sourceSha256':hashes,'diagnostics':diagnostics}
(root/'artifacts/pipeline-native-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'Factoidal Stage bridge checked against {commit}; {len(done)} pinned source modules compiled.')
