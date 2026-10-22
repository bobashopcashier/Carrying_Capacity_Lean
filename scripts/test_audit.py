#!/usr/bin/env python3
"""Exercise the compiled-environment audit without modifying project sources.

Requires an already built project. Every fixture source and olean lives in a
temporary directory, which is removed on success or failure. This does not run
lake build or the source-policy checker: intentionally invalid proof sources
are compiled in isolation so the environment audit itself must reject them.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
COUNTS = re.compile(
    r"Proof audit passed: (\d+) theorems, (\d+) safe declarations, (\d+) modules\."
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Path to the Lake executable")
    parser.add_argument(
        "--expected-counts", type=int, nargs=3, metavar=("THEOREMS", "SAFE", "MODULES"),
        help="Require the baseline totals from a previously audited build",
    )
    parser.add_argument("--timeout", type=float, default=180, help="Seconds per Lean process")
    args = parser.parse_args()

    # Resolve only the compiler and its import path, not the whole environment.
    runtime = subprocess.run(
        [args.lake, "env", sys.executable, "-c",
         "import json, os, shutil; print(json.dumps([shutil.which('lean'), "
         "os.environ.get('LEAN_PATH', '')]))"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    )
    lean, import_path = json.loads(runtime.stdout)
    if not lean:
        raise RuntimeError("Lake did not provide a Lean executable")

    total_start = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="carrying-audit-tests-") as directory:
        temporary = Path(directory)
        # Lean resolves an entire module prefix from one search-path directory.
        # Overlay the existing compiled project so temporary CarryingCapacity.*
        # fixtures do not hide its root module or imported project dependencies.
        compiled = ROOT / ".lake" / "build" / "lib" / "lean"
        originals = [compiled / "CarryingCapacity.olean"]
        originals.extend((compiled / "CarryingCapacity").rglob("*.olean"))
        for original in originals:
            if not original.is_file():
                raise RuntimeError(f"An already built project is required: missing {original}")
            link = temporary / original.relative_to(compiled)
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(original.resolve())
        env = os.environ.copy()
        env["LEAN_PATH"] = str(temporary) + os.pathsep + import_path

        def run_lean(path: Path, *, compile_module: bool = False):
            command = [lean, f"--root={temporary}" if compile_module else f"--root={ROOT}"]
            if compile_module:
                command.extend(["-o", str(path.with_suffix(".olean"))])
            command.append(str(path))
            start = time.perf_counter()
            result = subprocess.run(
                command, cwd=ROOT, env=env, capture_output=True, text=True,
                timeout=args.timeout,
            )
            return result, time.perf_counter() - start

        def checked_counts(result: subprocess.CompletedProcess) -> tuple[int, int, int]:
            output = result.stdout + result.stderr
            match = COUNTS.search(output)
            if result.returncode != 0 or match is None:
                raise RuntimeError(f"Expected a successful audit:\n{output}")
            return tuple(map(int, match.groups()))

        baseline, elapsed = run_lean(ROOT / "Audit.lean")
        baseline_counts = checked_counts(baseline)
        if args.expected_counts is not None and baseline_counts != tuple(args.expected_counts):
            raise RuntimeError(
                f"Baseline totals changed: expected {tuple(args.expected_counts)}, "
                f"received {baseline_counts}"
            )
        print(f"PASS baseline {baseline_counts}: {elapsed:.2f}s", flush=True)
        audit_source = (ROOT / "Audit.lean").read_text()

        def compile_fixture(module: str, source: str) -> None:
            path = temporary.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            result, _ = run_lean(path, compile_module=True)
            if result.returncode != 0:
                raise RuntimeError(f"Fixture {module} did not compile:\n"
                                   f"{result.stdout}{result.stderr}")

        def audit_fixture(module: str):
            path = temporary / f"Run{module.rsplit('.', 1)[-1]}.lean"
            path.write_text(f"import {module}\n" + audit_source)
            # The command module is outside CarryingCapacity and is not audited.
            return run_lean(path, compile_module=True)

        # Unused private declarations must still be enumerated. The safe
        # noncomputable definition also checks that ordinary allowed axioms pass.
        positive = "CarryingCapacity.AuditFixtureGood"
        compile_fixture(positive, """private theorem fixturePrivateGood : ∃ n : Nat, n = n := ⟨0, rfl⟩
noncomputable def fixtureChosen : Nat := Classical.choose fixturePrivateGood
""")
        result, elapsed = audit_fixture(positive)
        positive_counts = checked_counts(result)
        if not (
            positive_counts[0] >= baseline_counts[0] + 1
            and positive_counts[1] >= baseline_counts[1] + 2
            and positive_counts[2] == baseline_counts[2] + 1
        ):
            raise RuntimeError(f"Private/safe fixture declarations were not counted: {positive_counts}")
        print(f"PASS private theorem and safe definition {positive_counts}: {elapsed:.2f}s", flush=True)

        # The foreign axiom is outside project-module selection. Only transitive
        # dependency inspection of the project definition can reject this case.
        compile_fixture("ForeignAuditFixture", """namespace ForeignAuditFixture
axiom forbidden : False
theorem intermediate : False := forbidden
end ForeignAuditFixture
""")
        negatives = [
            ("PublicSorry", "theorem fixturePublicSorry : False := by sorry\n",
             "depends on forbidden axiom sorryAx"),
            ("PrivateSorry", "private theorem fixturePrivateSorry : False := by sorry\n",
             "depends on forbidden axiom sorryAx"),
            ("ProjectAxiom", "axiom fixtureProjectAxiom : True\n",
             "Project axiom is forbidden: fixtureProjectAxiom"),
            ("ForeignDependency", "import ForeignAuditFixture\n"
             "def fixtureTransitiveProof : False := ForeignAuditFixture.intermediate\n",
             "depends on forbidden axiom ForeignAuditFixture.forbidden"),
        ]
        for suffix, source, diagnostic in negatives:
            module = "CarryingCapacity.AuditFixture" + suffix
            compile_fixture(module, source)
            result, elapsed = audit_fixture(module)
            output = result.stdout + result.stderr
            if result.returncode == 0 or diagnostic not in output or COUNTS.search(output):
                raise RuntimeError(f"Fixture {suffix} was not rejected for the expected reason:\n{output}")
            if suffix == "PrivateSorry" and "fixturePrivateSorry" not in output:
                raise RuntimeError(f"Private placeholder was not identified:\n{output}")
            if suffix == "ForeignDependency" and "fixtureTransitiveProof" not in output:
                raise RuntimeError(f"Transitive safe-definition dependency was not identified:\n{output}")
            print(f"PASS rejects {suffix}: {elapsed:.2f}s", flush=True)

    print(f"All audit tests passed in {time.perf_counter() - total_start:.2f}s; "
          "temporary fixtures removed.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
