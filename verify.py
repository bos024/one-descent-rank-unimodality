"""Check the paper, Lean sources and three short exact audits (standard-library Python 3.10+)."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
CHECKS = ROOT / "checks"
CASES = (
    ("audit_depth_slack_bridge.py", "depth_slack_actual_audit.json"),
    ("verify_literal_principal_ideals.py", "literal_principal_ideals_audit.json"),
    ("check_peak_boundary.py", "peak_boundary_audit.json"),
)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def check_files():
    seen = set()
    for line in (ROOT / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines():
        expected, name = line.split("  ", 1)
        path = (ROOT / name).resolve()
        if name in seen or not path.is_relative_to(ROOT) or not path.is_file():
            raise ValueError(f"Invalid inventory entry: {name}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"File digest mismatch: {name}")
        seen.add(name)
    print(f"Verified {len(seen)} file digests.", flush=True)


def replay():
    with tempfile.TemporaryDirectory() as scratch:
        directory = Path(scratch)
        for script, _ in CASES:
            shutil.copyfile(CHECKS / script, directory / script)
        for script, report in CASES:
            result = subprocess.run(
                [sys.executable, "-B", str(directory / script)],
                cwd=directory,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                capture_output=True,
            )
            if result.returncode:
                raise RuntimeError(result.stderr.decode(errors="replace"))
            if script == "check_peak_boundary.py":
                actual = json.loads(result.stdout)
            else:
                actual = read_json(directory / report)
            if actual != read_json(CHECKS / report):
                raise ValueError(f"Exact audit mismatch: {script}")
            print(f"Reproduced {report}.", flush=True)


if __name__ == "__main__":
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit("Use Python 3.10 or later with assertions enabled.")
    check_files()
    replay()
