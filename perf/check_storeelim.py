#!/usr/bin/env python3
"""Exercise the production overwritten-store elimination pass and CompCert memory operations.

Build the compiler first (make -f Makefile.fast compiler). This harness links
the same extracted transformation/value/memory modules as ccomp; it performs no
speed measurement and never replaces a compiler module with a mock.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/storeelim"
OUTPUT = ROOT / "perf/results/storeelim.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False,
              "method": "native links to production Coq-extracted overwritten-store elimination pass and memory model",
              "commands": []}

    def save():
        temporary = OUTPUT.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(OUTPUT)

    save()
    try:
        subprocess.run(["python3", str(ROOT / "perf/guard.py")], cwd=ROOT, check=True)
        dependencies = subprocess.check_output(
            [str(ROOT / "tools/modorder"), ".depend.extr",
             "extraction/StoreElim.cmx", "extraction/Memory.cmx", "lib/Camlcoq.cmx"],
            cwd=ROOT, text=True).split()
        directories = ["extraction", "lib", "common", "aarch64", "backend", "cfrontend",
                       "cparser", "driver", "export", "debug"]
        includes = [arg for directory in directories for arg in ("-I", str(ROOT / directory))]
        source = ROOT / "perf/test_storeelim.ml"
        obj = ARTIFACTS / "test_storeelim.cmx"
        binary = ARTIFACTS / "check_storeelim"
        commands = [
            [str(ROOT / "perf/in-env"), "ocamlopt", "-g", *includes,
             "-c", str(source), "-o", str(obj)],
            [str(ROOT / "perf/in-env"), "ocamlopt", "-g", *includes,
             "-o", str(binary), "str.cmxa", "unix.cmxa", *dependencies, str(obj)],
        ]
        with (ARTIFACTS / "build.log").open("w") as log:
            for command in commands:
                report["commands"].append(command)
                subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        env = os.environ.copy()
        env["COMPCERT_CONFIG"] = str(ROOT / "compcert.ini")
        report["commands"].append([str(binary)])
        result = subprocess.run([str(binary)], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        (ARTIFACTS / "native.stdout").write_text(result.stdout)
        (ARTIFACTS / "native.stderr").write_text(result.stderr)
        result.check_returncode()
        native = json.loads(result.stdout)
        if native.get("success") is not True or not native.get("checks"):
            raise RuntimeError("Native overwritten-store elimination test program did not report successful checks")
        report.update(native)
        report["check_count"] = len(native["checks"])
        report["linked_objects"] = dependencies
        report["sha256"] = {
            str(path.relative_to(ROOT)): sha256(path) for path in [
                source, ROOT / "perf/check_storeelim.py", ROOT / "extraction/StoreElim.ml",
                ROOT / "backend/StoreElim.v", ROOT / "backend/StoreElimproof.v"]}
        save()
        print(f"{report['check_count']} native extracted-overwritten-store elimination checks passed; no speed measurements")
    except Exception as error:
        report["success"] = False
        report["error"] = str(error)
        save()
        raise


if __name__ == "__main__":
    main()
