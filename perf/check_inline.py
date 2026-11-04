#!/usr/bin/env python3
"""Check real code generation, output, and the noinline/-Os/-fno-inline contracts."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = r'''
#include <stdio.h>
#ifdef KEEP_CALL
/* The upstream macOS preprocessor configuration erases __attribute__ in
   system headers. Restore the spelling here to test a retained attribute. */
#undef __attribute__
__attribute__((noinline))
#endif
int leaf(int x) { return (x * 17) ^ 123; }
int main(int argc, char **argv) { printf("%d\n", leaf(argc)); return 0; }
'''


def main():
    checks = []
    with tempfile.TemporaryDirectory(prefix="compcert-inline-") as directory:
        source = Path(directory) / "leaf.c"
        source.write_text(SOURCE)
        for label, flags, keep_call in [
            ("default", [], False), ("disabled", ["-fno-inline"], True),
            ("size", ["-Os"], True), ("attribute", ["-DKEEP_CALL"], True),
        ]:
            asm = Path(directory) / (label + ".s")
            binary = Path(directory) / label
            cmd = [str(ROOT / "ccomp"), "-stdlib", str(ROOT / "runtime"), *flags]
            subprocess.run([*cmd, "-S", str(source), "-o", str(asm)], check=True)
            call_found = bool(re.search(r"\bbl\s+_leaf\b", asm.read_text()))
            if call_found != keep_call:
                raise RuntimeError(f"{label}: unexpected call retention: {call_found}")
            subprocess.run([*cmd, str(source), "-o", str(binary)], check=True)
            for count in (0, 1, 4):
                actual = subprocess.check_output([str(binary), *(["arg"] * count)])
                expected = f"{((count + 1) * 17) ^ 123}\n".encode()
                if actual != expected:
                    raise RuntimeError(f"{label}: incorrect execution output")
            checks.append({"mode": label, "call_retained": call_found, "outputs_pass": True})
    result = {"compiler_sha256": hashlib.sha256((ROOT / "ccomp").read_bytes()).hexdigest(),
              "success": True, "checks": checks}
    (ROOT / "perf/results/inline-contracts.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
