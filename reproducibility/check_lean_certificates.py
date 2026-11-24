"""Compile the Lean source files for the finite part of the proof."""

from pathlib import Path
from tempfile import TemporaryDirectory
import os
import subprocess


def main():
    sources = Path(__file__).resolve().parent / "reduction"
    mathlib_path = os.environ.get("LEAN_PATH")
    if not mathlib_path:
        raise SystemExit("Run lake env python reproducibility/check_lean_certificates.py.")

    modules = [
        "ActualDyadicSlopeNorm",
        "ActualDyadicSourcePayment",
        "FixedTerminalFourteenSlope",
        "CoupledSourceWindowA2",
        "FixedTerminalElevenDensity",
        "FirstMissingTwelveHeadGuards",
    ]
    modules += [f"FirstMissingTwelveCriticalPart{number:02d}" for number in range(31)]
    modules.append("FirstMissingTwelveCriticalCertificate")

    with TemporaryDirectory(prefix="one_descent_lean_") as folder:
        objects = Path(folder)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(objects), mathlib_path]))
        for module in modules:
            result = subprocess.run(
                ["lean", "-o", str(objects / f"{module}.olean"), f"{module}.lean"],
                cwd=sources,
                env=env,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                encoding="utf-8",
                errors="replace",
            )
            if result.returncode:
                print(result.stdout, end="", flush=True)
                result.check_returncode()
            print(f"Type-checked {module}.lean", flush=True)


if __name__ == "__main__":
    main()
