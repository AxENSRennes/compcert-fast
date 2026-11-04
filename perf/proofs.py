#!/usr/bin/env python3
"""Time clean proofs, independent kernel checking, and a one-file rebuild."""
import argparse
import datetime
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time
from integrity import check_principal_assumptions, sha

ROOT = Path(__file__).resolve().parents[1]


def run(command, log):
    print(" ".join(command), flush=True)
    start = time.perf_counter()
    with log.open("w") as stream:
        subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, check=True)
    return time.perf_counter() - start


def verify(jobs):
    os.chdir(ROOT)
    logs = ROOT / "perf/artifacts/proofs"
    logs.mkdir(parents=True, exist_ok=True)
    output = ROOT / "perf/results/proofs.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {"date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "jobs": jobs, "success": False, "stage": "source gate"}

    def save():
        temporary = output.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(result, indent=2) + "\n")
        temporary.replace(output)

    def stage(name, command, filename):
        result["stage"] = name
        save()
        return run(command, logs / filename)

    # Invalidate an old success even when the first guard/tool check fails.
    save()
    try:
        stage("source gate", [sys.executable, str(ROOT / "perf/guard.py")], "guard.log")
        result["coq"] = subprocess.check_output(["coqc", "--version"], text=True).strip()
        result["revision"] = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
        lock = dict(json.loads((ROOT / "perf/trust-lock.json").read_text())["files"])
        lock.update(json.loads((ROOT / "perf/proved-changes.json").read_text()))
        result["formal_source_sha256"] = {name: sha((ROOT / name).read_bytes()) for name in lock}
        stage("clean", ["make", "clean"], "clean.log")
        stage("dependencies", ["make", "depend"], "depend.log")
        command = ["make", f"-j{jobs}", "TIMING=1", "proof"]
        result["full_proof_seconds"] = stage("proof compilation", command, "full.log")
        result["kernel_check_seconds"] = stage("kernel check", ["make", "check-proof"], "kernel.log")
        stage("admission check", ["make", "check-admitted"], "admitted.log")
        assumptions = logs / "assumptions.v"
        assumptions.write_text("Require Import compcert.driver.Compiler.\n"
                               "Print Assumptions Compiler.transf_c_program_correct.\n"
                               "Print Assumptions Compiler.separate_transf_c_program_correct.\n")
        includes = shlex.split(subprocess.check_output(["make", "-s", "print-includes"], text=True))
        stage("principal assumptions", ["coqtop", "-q", "-batch", *includes, "-l", str(assumptions)],
              "assumptions.txt")
        actual = (logs / "assumptions.txt").read_text()
        options = check_principal_assumptions(ROOT, actual)
        (ROOT / "perf/results/assumptions.txt").write_text(actual)
        result["principal_assumptions_unchanged"] = not options
        result["original_principal_assumptions_preserved"] = True
        result["new_computational_options"] = options
        source = ROOT / "driver/Compiler.v"
        before = source.read_bytes()
        source.touch()
        result["incremental_proof_seconds"] = stage("one-file rebuild", command, "incremental.log")
        if source.read_bytes() != before:
            raise ValueError("Main compiler theorem source changed during verification")
        result["incremental_source"] = "driver/Compiler.v"
        result["incremental_method"] = "mtime-only edit; rebuild Compiler and dependents, unchanged contents"
        result["incremental_recompiled_sources"] = [
            line.split(" ", 1)[1] for line in (logs / "incremental.log").read_text().splitlines()
            if line.startswith("CROCQ ")]
        result["incremental_coqc_invocations"] = len(result["incremental_recompiled_sources"])
        stage("final source gate", [sys.executable, str(ROOT / "perf/guard.py")], "guard-final.log")
        if any(sha((ROOT / name).read_bytes()) != expected
               for name, expected in result["formal_source_sha256"].items()):
            raise ValueError("Formal source contents changed during verification")
        result.update(success=True, stage="complete")
    except BaseException as error:
        result["error"] = f"{type(error).__name__}: {error}"
        save()
        raise
    save()
    print(json.dumps(result, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    verify(args.jobs)


if __name__ == "__main__":
    main()
