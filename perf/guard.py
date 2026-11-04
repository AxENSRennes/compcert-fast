#!/usr/bin/env python3
"""Freeze original statements and assumptions; gate reviewed proof and platform extensions.

This regression check complements, never replaces, coqchk and the comparison
of both principal theorems' assumptions. Original hashes are anchored to Git
objects; editing a manifest alone cannot change the trusted baseline.
"""
import hashlib
import json
from pathlib import Path
import subprocess
from integrity import UPSTREAM, REVIEWED_FORMAL, NEW_FORMAL, ORACLES, upstream_sources, sha, reviewed_change_safe, reviewed_build_safe, new_source_safe

ROOT = Path(__file__).resolve().parents[1]


def main():
    lock = json.loads((ROOT / "perf/trust-lock.json").read_text())
    original = upstream_sources(ROOT)
    expected_lock = {name: sha(data) for name, data in original.items()
                     if name.endswith((".v", ".vp")) or name == "LICENSE"}
    if lock.get("upstream_commit") != UPSTREAM or lock.get("files") != expected_lock:
        raise SystemExit("Original trust manifest differs from fixed upstream Git objects")
    reviewed = json.loads((ROOT / "perf/proved-changes.json").read_text())
    if set(reviewed) - REVIEWED_FORMAL - NEW_FORMAL:
        raise SystemExit("Unapproved formal change path")
    failures = []
    for name, data in original.items():
        if name in ORACLES:
            continue
        path = ROOT / name
        expected = reviewed.get(name, sha(data))
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(name)
        elif name in reviewed and name.endswith((".v", ".vp")) and not reviewed_change_safe(data.decode(), path.read_text(), name):
            failures.append(name + " (existing statement, assumptions, imports or unchecked commands changed)")
        elif name in reviewed and not name.endswith((".v", ".vp")) and not reviewed_build_safe(data.decode(), path.read_text(), name):
            failures.append(name + " (trusted build recipe changed)")
    for name in set(reviewed) - set(original):
        path = ROOT / name
        if not path.is_file() or sha(path.read_bytes()) != reviewed[name] or not new_source_safe(path.read_text()):
            failures.append(name + " (new formal source not reviewed or contains unsafe commands)")
    # Catch newly tracked proof sources that the frozen corpus doesn't contain.
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")
    failures.extend(name for name in tracked if name.endswith((".v", ".vp"))
                    and name not in lock["files"] and name not in reviewed)
    generated = {"backend/SelectDiv.v", "backend/SplitLong.v", "cparser/Parser.v"}
    for arch in ("aarch64", "arm", "powerpc", "riscV", "x86"):
        generated.update(f"{arch}/{name}.v" for name in ("SelectOp", "SelectLong", "ConstpropOp"))
    directories = {str(Path(name).parts[0]) for name in lock["files"] if "/" in name}
    for directory in directories:
        for path in (ROOT / directory).rglob("*"):
            name = str(path.relative_to(ROOT))
            if path.suffix in (".v", ".vp") and name not in lock["files"] and name not in generated and name not in reviewed:
                failures.append(name)
    if failures:
        raise SystemExit("Formal source gate failed: " + ", ".join(failures))
    print(f"Anchored upstream formal/license files: {len(lock['files'])}; "
          f"reviewed changes: {', '.join(sorted(reviewed)) or 'none'}; "
          "existing theorem statements and original logical assumptions preserved; "
          "explicit platform-builtin extensions reviewed separately")


if __name__ == "__main__":
    main()
