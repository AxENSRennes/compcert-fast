#!/usr/bin/env python3
"""Kernel-check the isolated integer vector model and compare it with real NEON.

This experimental model/vector-loop planner is not integrated in Asm.v, Values,
register allocation or the main compiler. Hardware comparisons are tests, not
proofs of the model against Arm's specification. No speed series is executed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/neon"
OUTPUT = ROOT / "perf/results/neon.json"
SOURCES = ["aarch64/Neon.v", "perf/neon/Extract.v", "perf/neon/hardware.c",
           "perf/neon/check.ml", "perf/check_neon.py"]


def fingerprint():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in SOURCES}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, default=50000,
                        help="random vectors per supported operation/width pair (23 pairs)")
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False,
              "integrated_into_compcert_backend": False,
              "scope": "integer lane semantics and a checked contiguous elementwise-loop vector/tail plan",
              "hardware_equivalence_proved": False,
              "remaining": ["Asm.v vector state/instructions", "vector Values and memory semantics",
                            "ABI/register allocation integration", "general C-loop recognition and alias proofs",
                            "floating-point vectorization", "formal Arm/Sail refinement"],
              "stage": "host check", "commands": [], "sha256": fingerprint()}

    def save():
        temporary = OUTPUT.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(OUTPUT)

    def execute(label, command, filename):
        report["stage"] = label
        report["commands"].append([str(item) for item in command])
        save()
        with (ARTIFACTS / filename).open("w") as stream:
            subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, check=True)

    save()
    try:
        if platform.system() != "Darwin" or platform.machine() != "arm64" or sys.byteorder != "little":
            raise RuntimeError("This hardware adapter requires native little-endian macOS ARM64")
        env = str(ROOT / "perf/in-env")
        coq_args = ["-Q", "aarch64", "compcert.aarch64"]
        execute("model compilation", [env, "coqc", *coq_args, "aarch64/Neon.v"], "coq-model.log")
        execute("independent kernel check", [env, "coqchk", *coq_args, "compcert.aarch64.Neon"], "kernel.log")
        assumptions = ARTIFACTS / "assumptions.v"
        assumptions.write_text("From compcert.aarch64 Require Import Neon.\n"
                               "Print Assumptions vectorize_preserves_elementwise_loop.\n"
                               "Print Assumptions compiled_loop_correct.\n"
                               "Print Assumptions checked_plan_valid.\n"
                               "Print Assumptions compile_plan_preserves_scalar.\n"
                               "Print Assumptions unsupported_instruction_uses_scalar.\n")
        execute("model proof assumptions", [env, "coqtop", "-q", "-batch", *coq_args,
                                             "-l", str(assumptions)], "assumptions.txt")
        assumptions_text = (ARTIFACTS / "assumptions.txt").read_text()
        if assumptions_text.count("Closed under the global context") != 5 or "Axioms:" in assumptions_text:
            raise RuntimeError("Expected five closed model/planner proofs")
        report["kernel_checked"] = True
        report["model_proofs_closed"] = True
        report["model_proof_count"] = 5
        execute("isolated model extraction", [env, "coqc", *coq_args, "perf/neon/Extract.v"], "extraction.log")
        model_dir = ARTIFACTS
        include = ["-I", str(model_dir)]
        ocaml = [env, "ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg", *include]
        execute("native model interface", [*ocaml, "-c", str(model_dir / "neon_model.mli")], "native-interface.log")
        execute("native model", [*ocaml, "-c", str(model_dir / "neon_model.ml")], "native-model.log")
        execute("native comparison harness", [*ocaml, "-c", str(ROOT / "perf/neon/check.ml"),
                                               "-o", str(model_dir / "check.cmx")], "native-harness.log")
        ocaml_headers = subprocess.check_output([env, "ocamlc", "-where"], cwd=ROOT, text=True).strip()
        execute("native NEON adapter", ["clang", "-O2", "-Wall", "-Wextra", "-Werror", "-I", ocaml_headers,
                                       "-c", str(ROOT / "perf/neon/hardware.c"),
                                       "-o", str(model_dir / "hardware.o")], "native-hardware.log")
        execute("link differential checker", [*ocaml, str(model_dir / "neon_model.cmx"),
                                              str(model_dir / "check.cmx"), str(model_dir / "hardware.o"),
                                              "-o", str(model_dir / "check")], "native-link.log")
        execute("instruction inspection", ["otool", "-tv", str(model_dir / "hardware.o")], "instructions.txt")
        disassembly = (model_dir / "instructions.txt").read_text()
        expected = [f"{op}.{shape}" for op in ("add", "sub") for shape in ("16b", "8h", "4s", "2d")]
        expected += [f"mul.{shape}" for shape in ("16b", "8h", "4s")]
        expected += ["and.16b", "orr.16b", "eor.16b"]
        if any(instruction not in disassembly for instruction in expected):
            raise RuntimeError("Expected actual NEON operations were not found in the adapter")
        report["inspected_neon_instructions"] = expected
        execute("hardware differential tests", [str(model_dir / "check"), str(args.rounds)], "native.json")
        native = json.loads((model_dir / "native.json").read_text())
        if native.get("success") is not True or native.get("random_vector_cases") != args.rounds * 23:
            raise RuntimeError("Native differential checker did not complete the required cases")
        report.update(native)
        if fingerprint() != report["sha256"]:
            raise RuntimeError("NEON model or harness changed during checking")
        report["generated_model_sha256"] = hashlib.sha256((model_dir / "neon_model.ml").read_bytes()).hexdigest()
        report["cpu"] = subprocess.check_output(["sysctl", "-n", "machdep.cpu.brand_string"], text=True).strip()
        report["stage"] = "complete"
        save()
        print(f"NEON/model: {native['random_vector_cases']} random vectors, "
              f"{native['boundary_vector_cases']} boundary vectors, {native['tail_loop_cases']} tail loops; "
              "kernel proofs checked; no speed measurements")
    except BaseException as error:
        report.update(success=False, error=f"{type(error).__name__}: {error}")
        save()
        raise


if __name__ == "__main__":
    main()
