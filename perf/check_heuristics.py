#!/usr/bin/env python3
"""Check enabled heuristic effects, validator acceptance and codegen contracts.

No timing series or speed claim: native synthetic graphs exercise the real
allocation/layout oracles, then ordinary C execution checks compiler options.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/heuristics"
OUTPUT = ROOT / "perf/results/heuristics.json"
SMALL_LEAF = r'''
#include <stdio.h>
#ifdef KEEP_CALL
/* Upstream macOS preprocessing erases attributes in system headers. */
#undef __attribute__
__attribute__((noinline))
#endif
int leaf(int x) { return (x * 17) ^ 123; }
int main(int argc, char **argv) { printf("%d\n", leaf(argc)); return 0; }
'''
RECURSIVE = r'''
#include <stdio.h>
int leaf(int x) { if (x < 1) return x + 1; return leaf(x - 1) + x; }
int main(int argc, char **argv) { printf("%d\n", leaf(argc)); return 0; }
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def environment(flags, trace):
    env = os.environ.copy()
    env["COMPCERT_EXPERIMENTS"] = flags
    env["COMPCERT_CONFIG"] = str(ROOT / "compcert.ini")
    env["COMPCERT_EXPERIMENT_TRACE"] = str(trace)
    return env


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False, "checks": [],
              "native": {}, "codegen": {}, "commands": [],
              "tested_flags": ["small-inline", "loop-spill", "trace-layout"],
              "scope": "heuristics only; scalar formal passes and NEON have separate harnesses"}

    def save():
        temporary = OUTPUT.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(OUTPUT)

    def check(name, condition):
        if not condition:
            raise RuntimeError(name)
        report["checks"].append(name)

    def execute(command, *, flags="", label, expect_success=True):
        trace = ARTIFACTS / (label + ".trace.jsonl")
        trace.unlink(missing_ok=True)
        report["commands"].append([str(arg) for arg in command])
        result = subprocess.run(command, cwd=ROOT, env=environment(flags, trace),
                                capture_output=True, text=True)
        (ARTIFACTS / (label + ".stdout")).write_text(result.stdout)
        (ARTIFACTS / (label + ".stderr")).write_text(result.stderr)
        if expect_success:
            result.check_returncode()
        records = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
        return result, records

    save()
    try:
        subprocess.run(["python3", str(ROOT / "perf/guard.py")], cwd=ROOT, check=True)
        sources = [ROOT / name for name in ["backend/ExperimentalOptions.ml", "backend/Inliningaux.ml",
                   "backend/Regalloc.ml", "backend/Linearizeaux.ml", "perf/test_heuristics.ml",
                   "perf/check_heuristics.py"]]
        snapshot = {str(path.relative_to(ROOT)): sha(path) for path in sources}
        deps = subprocess.check_output(
            [str(ROOT / "tools/modorder"), ".depend.extr", "extraction/Allocation.cmx",
             "extraction/Linearize.cmx"], cwd=ROOT, text=True).split()
        includes = [arg for directory in ["extraction", "lib", "common", "aarch64", "backend",
                    "cfrontend", "cparser", "driver", "export", "debug"]
                    for arg in ("-I", str(ROOT / directory))]
        obj, native = ARTIFACTS / "test_heuristics.cmx", ARTIFACTS / "check_heuristics"
        with (ARTIFACTS / "build.log").open("w") as log:
            for command in [
                [ROOT / "perf/in-env", "ocamlopt", "-g", *includes, "-c", ROOT / "perf/test_heuristics.ml", "-o", obj],
                [ROOT / "perf/in-env", "ocamlopt", "-g", *includes, "-o", native,
                 "str.cmxa", "unix.cmxa", *deps, obj],
            ]:
                report["commands"].append([str(arg) for arg in command])
                subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        configurations = {
            "default": "", "small-inline": "small-inline", "loop-spill": "loop-spill",
            "trace-layout": "trace-layout", "combined": "small-inline,loop-spill,trace-layout",
            "deduplicated": "loop-spill,loop-spill",
        }
        for name, flags in configurations.items():
            result, trace = execute([str(native)], flags=flags, label="native-" + name)
            actual = json.loads(result.stdout)
            check(name + " native checks pass", actual.get("success") is True and len(actual["checks"]) >= 19)
            report["native"][name] = actual
            if not flags:
                check("default has no counters or trace file", not trace and not actual["counters"])
            else:
                expected = set(flags.split(','))
                check(name + " traces only enabled experiments", all(item["pass"] in expected for item in trace))
                check(name + " enabled records are deduplicated",
                      len([item for item in trace if item["event"] == "enabled"]) == len(expected))
        original = report["native"]["default"]["allocation_fingerprint"]
        weighted = report["native"]["loop-spill"]["allocation_fingerprint"]
        check("loop weighting changes a validated high-pressure allocation", original != weighted)
        check("layout alone does not change allocation",
              original == report["native"]["trace-layout"]["allocation_fingerprint"])
        for name, flags, expected_message in [
            ("unknown", "not-implemented", "unknown experiment"),
            ("empty-token", "small-inline,,trace-layout", "unknown experiment"),
            ("incompatible", "rtl-unroll2,rtl-unroll4", "mutually exclusive"),
        ]:
            result, _ = execute([str(ROOT / "ccomp"), "-version"], flags=flags,
                                label=name, expect_success=False)
            check(name + " flags rejected before compilation",
                  result.returncode != 0 and expected_message in result.stderr)
        for name, flags, options, retain, source_text in [
            ("default", "", [], True, SMALL_LEAF),
            ("enabled", "small-inline", [], False, SMALL_LEAF),
            ("combined", configurations["combined"], [], False, SMALL_LEAF),
            ("disabled", "small-inline", ["-fno-inline"], True, SMALL_LEAF),
            ("size", "small-inline", ["-Os"], True, SMALL_LEAF),
            ("attribute", "small-inline", ["-DKEEP_CALL"], True, SMALL_LEAF),
            ("recursive", "small-inline", [], True, RECURSIVE),
        ]:
            source = ARTIFACTS / ("leaf-" + name + ".c")
            asm = source.with_suffix(".s")
            binary = source.with_suffix(".exe")
            source.write_text(source_text)
            base = [str(ROOT / "ccomp"), "-stdlib", str(ROOT / "runtime"), *options]
            _, trace = execute([*base, "-S", str(source), "-o", str(asm)], flags=flags,
                               label="asm-" + name)
            actual_call = bool(re.search(r"\bbl\s+_leaf\b", asm.read_text()))
            check(name + " call-retention contract", actual_call == retain)
            if name in ("enabled", "combined"):
                check(name + " inline selection is observable",
                      any(item["pass"] == "small-inline" and item["event"] == "selected" for item in trace))
            execute([*base, str(source), "-o", str(binary)], flags=flags, label="link-" + name)
            for count in (0, 1, 4):
                result, _ = execute([str(binary), *(["arg"] * count)], label=f"run-{name}-{count}")
                argc = count + 1
                expected = 1 + argc * (argc + 1) // 2 if name == "recursive" else (argc * 17) ^ 123
                check(f"{name} execution with argc={argc}", result.stdout == f"{expected}\n")
            report["codegen"][name] = {"call_retained": actual_call, "outputs_pass": True}
        check("heuristic source contents remain unchanged during tests",
              all(sha(ROOT / name) == expected for name, expected in snapshot.items()))
        report["source_sha256"] = snapshot
        report["compiler_sha256"] = sha(ROOT / "ccomp")
        report["success"] = True
        save()
        print(f"{len(report['checks'])} heuristic integration checks passed; no speed measurements")
    except Exception as error:
        report["success"] = False
        report["error"] = str(error)
        save()
        raise


if __name__ == "__main__":
    main()
