#!/usr/bin/env python3
"""Build every project module and audit all compiled proof dependencies."""

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b"
    r"|\bdebug\.skipKernelTC\b|\bLean\.ofReduceBool\b"
)


def code_only(text: str) -> str:
    """Mask Lean strings and nested comments while preserving line numbers."""
    out = list(text)
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        pair = text[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out[i : i + 2] = "  "
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                out[i : i + 2] = "  "
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
        elif quoted:
            if text[i] == "\\":
                out[i : i + 2] = "  "
                i += 2
                continue
            if text[i] == '"':
                quoted = False
            if text[i] != "\n":
                out[i] = " "
        elif pair == "/-":
            depth = 1
            out[i : i + 2] = "  "
            i += 2
            continue
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
            continue
        elif text[i] == '"':
            quoted = True
            out[i] = " "
        i += 1
    return "".join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Path to the Lake executable")
    args = parser.parse_args()
    modules = sorted((ROOT / "CarryingCapacity").rglob("*.lean"))
    root_module = ROOT / "CarryingCapacity.lean"
    if not modules or not root_module.is_file():
        sys.exit("Project modules or CarryingCapacity.lean are missing")
    expected = {".".join(p.relative_to(ROOT).with_suffix("").parts) for p in modules}
    root_code = code_only(root_module.read_text())
    imported = set(re.findall(r"(?m)^import\s+(CarryingCapacity(?:\.[\w]+)+)\s*$", root_code))
    missing = sorted(expected - imported)
    if missing:
        sys.exit("Root import must explicitly include every module: " + ", ".join(missing))
    for path in [root_module, *modules]:
        code = code_only(path.read_text())
        match = FORBIDDEN.search(code)
        if match:
            line = code.count("\n", 0, match.start()) + 1
            sys.exit(f"{path.relative_to(ROOT)}:{line}: forbidden proof bypass {match.group()}")
    print(f"Source policy passed for {len(modules)} modules.", flush=True)
    subprocess.run([args.lake, "build"], cwd=ROOT, check=True)
    subprocess.run([args.lake, "env", "lean", "Audit.lean"], cwd=ROOT, check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
