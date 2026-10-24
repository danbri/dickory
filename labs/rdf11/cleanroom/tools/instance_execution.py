"""Execute symbolic instance-search regressions alongside the universal proofs."""
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    program = '''import Audit.InstanceExecution
#eval do
  let checks := Spec2Lean.InstanceExecution.checks
  if checks.isEmpty then throw (IO.userError "No instance examples discovered")
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("Instance regression failed: " ++ name))
    IO.println ("PASS " ++ name)
'''
    result = subprocess.run(["lake", "env", "lean", "--stdin"], input=program,
        text=True, capture_output=True, cwd=ROOT, env=env, timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    checks = [line.removeprefix("PASS ") for line in result.stdout.splitlines() if line.startswith("PASS ")]
    if len(checks) != 18 or len(set(checks)) != len(checks):
        raise RuntimeError(f"Expected eighteen distinct executable checks, got {checks!r}")
    report = {"status": "pass", "surface": "Lean executable evaluator; symbolic instance fixtures",
        "not_w3c_fixtures": True, "package_refinement": False, "checks": checks}
    (ROOT / "artifacts" / "instance-execution.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
