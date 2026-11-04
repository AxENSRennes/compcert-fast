#!/usr/bin/env python3
"""Check explicit packed-64 NEON builtins in the production C compiler.

The builtins specify two modulo-2^32 integer lanes carried in a scalar
unsigned long long. Their handwritten four-instruction expansion extends the
trusted builtin/printer surface. These are explicit intrinsics, not general
C-loop vectorization. Hardware comparisons are tests, not an Arm refinement
proof. This command performs no speed measurement.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/packed-neon"
OUTPUT = ROOT / "perf/results/packed-neon.json"
SOURCE = ROOT / "perf/test_packed_neon.c"


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False, "checks": [],
              "integrated_into_compcert_backend": True,
              "automatic_loop_vectorization": False,
              "hardware_equivalence_proved": False,
              "scope": "three explicit unsigned packed-64 integer builtins, two 32-bit lanes",
              "trusted_surface": "platform builtin specification and handwritten pseudo-instruction printing",
              "commands": []}

    def save():
        temporary = OUTPUT.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(OUTPUT)

    def env(flags):
        result = os.environ.copy()
        result["COMPCERT_EXPERIMENTS"] = flags
        result["COMPCERT_CONFIG"] = str(ROOT/"compcert.ini")
        result.pop("COMPCERT_EXPERIMENT_TRACE", None)
        return result

    def check(name, value):
        if not value:
            raise RuntimeError(name)
        report["checks"].append(name)

    def execute(command, flags="", **kwargs):
        command = [str(item) for item in command]
        report["commands"].append(command)
        return subprocess.run(command, cwd=ROOT, env=env(flags), check=True, **kwargs)

    def output(command, flags=""):
        return execute(command, flags, stdout=subprocess.PIPE).stdout

    save()
    try:
        check("native little-endian macOS ARM64 host",
              platform.system() == "Darwin" and platform.machine() == "arm64" and sys.byteorder == "little")
        execute(["python3", ROOT/"perf/guard.py"])
        roots = ["lib/Camlcoq.cmx", "aarch64/CBuiltins.cmx", "aarch64/Asmexpand.cmx",
                 "extraction/Builtins.cmx", "extraction/Machregs.cmx"]
        deps = subprocess.check_output([str(ROOT/"tools/modorder"), ".depend.extr", *roots],
                                       cwd=ROOT, text=True).split()
        includes = [arg for d in ["extraction", "lib", "common", "aarch64", "backend", "cfrontend",
                                 "cparser", "driver", "export", "debug"] for arg in ("-I", str(ROOT/d))]
        obj, native = ARTIFACTS/"test_packed_neon.cmx", ARTIFACTS/"check_packed_neon"
        with (ARTIFACTS/"native-build.log").open("w") as log:
            execute([ROOT/"perf/in-env", "ocamlopt", "-g", *includes, "-c",
                     ROOT/"perf/test_packed_neon.ml", "-o", obj], stdout=log, stderr=subprocess.STDOUT)
            execute([ROOT/"perf/in-env", "ocamlopt", "-g", *includes, "-o", native,
                     "str.cmxa", "unix.cmxa", *deps, obj], stdout=log, stderr=subprocess.STDOUT)
        report["native"] = {}
        for name, flags in [("default", ""), ("enabled", "neon-packed")]:
            native_result = json.loads(output([native], flags))
            check(name+" native production semantics and allocation metadata", native_result["success"])
            check(name+" builtin registration gate", native_result["enabled"] == (name == "enabled"))
            check(name+" semantic coverage", native_result["semantic_cases"] == 30243)
            report["native"][name] = native_result

        ccomp = [ROOT/"ccomp", "-stdlib", ROOT/"runtime", "-fno-inline"]
        scalar, enabled = ARTIFACTS/"scalar.exe", ARTIFACTS/"enabled.exe"
        reference = ARTIFACTS/"reference.exe"
        execute(["clang", "-O2", "-fno-inline", SOURCE, "-o", reference])
        expected = output([reference])
        check("scalar reference covers 1000081 packed input pairs",
              expected.decode().split()[0] == "1000081")
        execute([*ccomp, SOURCE, "-o", scalar])
        check("default scalar C program matches clang reference", output([scalar]) == expected)
        execute([*ccomp, "-DUSE_NEON=1", SOURCE, "-o", enabled], "neon-packed")
        check("enabled NEON C program matches scalar reference on every pair and live FP values",
              output([enabled]) == expected)
        report["combined_profiles"] = {}
        profiles = json.loads((ROOT/"perf/experiment-profiles.json").read_text())["profiles"]
        for name, scalar_flags in profiles.items():
            flags = scalar_flags + ",neon-packed"
            binary = ARTIFACTS/(name+".exe")
            execute([*ccomp, "-DUSE_NEON=1", SOURCE, "-o", binary], flags)
            check(name+" combined scalar/NEON outputs and live FP values", output([binary]) == expected)
            report["combined_profiles"][name] = {"flags": flags, "correctness_pass": True,
                                                "hardware_pairs": 1000081}

        for name, flags in [("default", ""), ("enabled", "neon-packed")]:
            asm = ARTIFACTS/(name+".s")
            execute([*ccomp, "-DUSE_NEON=1", "-S", SOURCE, "-o", asm], flags)
            text = asm.read_text()
            for op in ("add", "sub", "mul"):
                emitted = bool(re.search(r"\b"+op+r"\s+v16\.2s,\s*v16\.2s,\s*v17\.2s", text))
                check(name+" emitted "+op+" NEON gate", emitted == (name == "enabled"))
            if name == "enabled":
                check("enabled source names are fully expanded", not re.search(r"\bbl\s+_?__builtin_cc_neon_", text))
                body = text.split("_live_fp:", 1)[1].split(".cfi_endproc", 1)[0]
                check("live-FP stress function contains a directly expanded packed builtin",
                      bool(re.search(r"\badd\s+v16\.2s", body)))
                check("live-FP stress creates register pressure beyond scratch register indices",
                      bool(re.search(r"\bd(?:1[89]|2[0-9]|3[01])\b", body)))
            else:
                check("disabled intrinsic names remain external calls", "bl\t___builtin_cc_neon_add_u32x2" in text)

        # The interpreter executes the same C builtins via their mathematical
        # Builtins1 specification, rather than the hardware printer expansion.
        small = ARTIFACTS/"small-reference.exe"
        execute(["clang", "-O2", "-DTEST_ROUNDS=0", SOURCE, "-o", small])
        small_expected = output([small])
        interpreted = output([*ccomp, "-interp", "-quiet", "-DUSE_NEON=1", "-DTEST_ROUNDS=0", SOURCE], "neon-packed")
        (ARTIFACTS/"interpreter.stdout").write_bytes(interpreted)
        check("Cexec builtin semantics match scalar C for edge cases and live FP values", interpreted == small_expected)
        report["hardware_pair_count"] = 1000081
        report["hardware_builtin_results"] = 3000243
        report["source_sha256"] = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
            ["aarch64/Builtins1.v", "aarch64/CBuiltins.ml", "aarch64/Machregs.v",
             "aarch64/Asmexpand.ml", "aarch64/TargetPrinter.ml", "backend/ExperimentalOptions.ml",
             "perf/test_packed_neon.ml", "perf/test_packed_neon.c", "perf/check_packed_neon.py",
             "perf/experiment-profiles.json"]}
        report["success"] = True
        save()
        print("Packed NEON: 30243 extracted semantic cases and 3000243 hardware results checked; no speed measurement")
    except Exception as error:
        report["error"] = str(error)
        report["success"] = False
        save()
        raise


if __name__ == "__main__":
    main()
