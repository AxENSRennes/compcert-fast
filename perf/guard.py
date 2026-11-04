#!/usr/bin/env python3
"""Phase-2 gate: all upstream Coq specifications, proofs and license stay byte-identical.

This deliberately conservative source gate complements (never replaces) coqchk.
Oracle heuristics may change; extracting the compiler still uses the unchanged
proved allocation validator. A later proved pass needs an explicit gate revision.
"""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    lock = json.loads((ROOT / "perf/trust-lock.json").read_text())
    failures = []
    for name, expected in lock["files"].items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(name)
    # Catch newly tracked proof sources that the frozen corpus doesn't contain.
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")
    failures.extend(name for name in tracked if name.endswith((".v", ".vp"))
                    and name not in lock["files"])
    generated = {"backend/SelectDiv.v", "backend/SplitLong.v", "cparser/Parser.v"}
    for arch in ("aarch64", "arm", "powerpc", "riscV", "x86"):
        generated.update(f"{arch}/{name}.v" for name in ("SelectOp", "SelectLong", "ConstpropOp"))
    directories = {str(Path(name).parts[0]) for name in lock["files"] if "/" in name}
    for directory in directories:
        for path in (ROOT / directory).rglob("*"):
            name = str(path.relative_to(ROOT))
            if path.suffix in (".v", ".vp") and name not in lock["files"] and name not in generated:
                failures.append(name)
    if failures:
        raise SystemExit("Formal source gate failed: " + ", ".join(failures))
    print(f"Unchanged: {len(lock['files'])} upstream formal/license files; base {lock['upstream_commit']}")


if __name__ == "__main__":
    main()
