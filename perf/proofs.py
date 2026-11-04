#!/usr/bin/env python3
"""Time clean proofs, independent kernel checking, and a one-file rebuild."""
import argparse
import datetime
import json
import os
from pathlib import Path
import shlex
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def run(command, log):
    print(" ".join(command), flush=True)
    start = time.perf_counter()
    with log.open("w") as stream:
        subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, check=True)
    return time.perf_counter() - start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    os.chdir(ROOT)
    logs = ROOT / "perf/artifacts/proofs"
    logs.mkdir(parents=True, exist_ok=True)
    result = {"date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "jobs": args.jobs, "coq": subprocess.check_output(["coqc", "--version"], text=True).strip(),
              "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()}
    # make clean is upstream's prescribed way to eliminate stale .vo files.
    run(["make", "clean"], logs / "clean.log")
    run(["make", "depend"], logs / "depend.log")
    command = ["make", f"-j{args.jobs}", "TIMING=1", "proof"]
    result["full_proof_seconds"] = run(command, logs / "full.log")
    result["kernel_check_seconds"] = run(["make", "check-proof"], logs / "kernel.log")
    run(["make", "check-admitted"], logs / "admitted.log")
    assumptions = logs / "assumptions.v"
    assumptions.write_text("Require Import compcert.driver.Compiler.\n"
                           "Print Assumptions Compiler.transf_c_program_correct.\n"
                           "Print Assumptions Compiler.separate_transf_c_program_correct.\n")
    includes = shlex.split(subprocess.check_output(["make", "-s", "print-includes"], text=True))
    run(["coqtop", "-q", "-batch", *includes, "-l", str(assumptions)],
        ROOT / "perf/results/assumptions.txt")
    # Touch models a source edit without introducing an artificial proof change.
    source = ROOT / "driver/Compiler.v"
    before = source.read_bytes()
    source.touch()
    result["incremental_proof_seconds"] = run(command, logs / "incremental.log")
    assert source.read_bytes() == before
    result["incremental_source"] = "driver/Compiler.v"
    result["incremental_method"] = "mtime-only edit; rebuild Compiler and dependents, unchanged contents"
    result["incremental_recompiled_sources"] = [
        line.split(" ", 1)[1] for line in (logs / "incremental.log").read_text().splitlines()
        if line.startswith("CROCQ ")]
    result["incremental_coqc_invocations"] = len(result["incremental_recompiled_sources"])
    result["success"] = True
    output = ROOT / "perf/results/proofs.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()
