#!/usr/bin/env python3
"""Frozen suite, differential correctness, paired measurements and a noise gate.

Run from any directory: python3 perf/bench.py --output perf/results/latest.json
By default, exit 0 only when correctness and both noise checks pass. Use
--correctness-only to validate outputs without claiming a performance result.
The metric is the
equal-weight geometric mean of (CompCert time / clang -O2 time). Closing 75%
of a baseline gap R0-1 means R <= 1 + 0.25*(R0-1).
"""
import argparse
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import random
import re
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/bench"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def capture(command):
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def geomean(values):
    return math.exp(statistics.mean(math.log(value) for value in values))


def metrics(samples):
    med = statistics.median(samples)
    return {"median_seconds": med,
            "relative_mad": statistics.median(abs(x - med) for x in samples) / med}


def measure(binary, case):
    result = subprocess.run([str(binary), *case["args"]], cwd=ROOT, capture_output=True, timeout=180)
    if result.returncode:
        raise RuntimeError(f"{binary.name} exited {result.returncode}: {result.stderr.decode(errors='replace')}")
    expected = (ROOT / case["expected"]).read_bytes()
    if result.stdout != expected:
        (ARTIFACTS / (binary.name + ".actual")).write_bytes(result.stdout)
        raise RuntimeError(f"Incorrect stdout: {binary.name}; see perf/artifacts/bench/*.actual")
    timing = re.fullmatch(rb"COMPCERT_FAST_TIME ([0-9]+\.[0-9]+)\n", result.stderr)
    if not timing:
        raise RuntimeError(f"Unexpected stderr: {binary.name}: {result.stderr!r}")
    seconds = float(timing[1])
    if seconds <= 0:
        raise RuntimeError("Nonpositive timer reading")
    return seconds


def compile_suite(manifest, compcert, clang):
    commands = []
    with (ARTIFACTS / "compile.log").open("w") as log:
        def execute(cmd):
            commands.append([str(x) for x in cmd])
            log.write(" ".join(commands[-1]) + "\n")
            log.flush()
            subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        wrapper = ARTIFACTS / "runner.o"
        execute([clang, "-O2", "-c", ROOT / "perf/runner.c", "-o", wrapper])
        for case in manifest["benchmarks"]:
            for label, compiler, flags in [("compcert", compcert, manifest["compcert_flags"]),
                                            ("clang", clang, manifest["clang_flags"])]:
                obj = ARTIFACTS / f"{case['name']}.{label}.o"
                executable = ARTIFACTS / f"{case['name']}.{label}"
                execute([compiler, *flags, "-Dmain=benchmark_main", "-c", ROOT / case["source"], "-o", obj])
                execute([clang, obj, wrapper, "-lm", "-o", executable])
    return commands


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compcert", type=Path, default=ROOT / "ccomp")
    parser.add_argument("--clang", default="clang")
    parser.add_argument("--correctness-only", action="store_true")
    args = parser.parse_args()
    manifest_bytes = (ROOT / "perf/suite.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    for name, expected in manifest["sha256"].items():
        if digest((ROOT / name).read_bytes()) != expected:
            raise RuntimeError(f"Frozen suite changed: {name}")
    if capture(["git", "-C", "test", "rev-parse", "HEAD"]) != manifest["test_commit"]:
        raise RuntimeError("Wrong benchmark submodule revision")
    subprocess.run([sys.executable, ROOT / "perf/guard.py"], cwd=ROOT, check=True)
    compcert = args.compcert.resolve()
    output = args.output.resolve()
    baseline = ROOT / "perf/results/baseline.json"
    if args.correctness_only and output == baseline.resolve():
        raise RuntimeError("Correctness-only output must not replace the performance baseline")
    if output == baseline.resolve():
        upstream = json.loads((ROOT / "perf/trust-lock.json").read_text())["upstream_commit"]
        comparison = subprocess.run(
            ["git", "diff", "--quiet", upstream, "--", ":(glob)**/*.ml", ":(glob)**/*.mli",
             ":(glob)**/*.v", ":(glob)**/*.vp", "configure", "Makefile", "Makefile.extr", "runtime"],
            cwd=ROOT)
        if comparison.returncode:
            raise RuntimeError("Capture the initial baseline from the unchanged compiler on branch fast")
    if output == baseline.resolve() and output.exists():
        previous = json.loads(output.read_text())
        if previous.get("noise_pass") and previous.get("correctness_pass"):
            raise RuntimeError("A valid baseline is already frozen; use a different --output")
    report = {
        "schema_version": 1, "mode": "correctness" if args.correctness_only else "performance",
        "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "suite_sha256": digest(manifest_bytes),
        "revision": capture(["git", "rev-parse", "HEAD"]),
        "tracked_changes": capture(["git", "diff", "--stat", "HEAD"]),
        "machine": {"cpu": capture(["sysctl", "-n", "machdep.cpu.brand_string"]),
                    "os": capture(["sw_vers"]), "power": capture(["pmset", "-g", "batt"]),
                    "p_cores": capture(["sysctl", "-n", "hw.perflevel0.physicalcpu"]),
                    "scheduling": "QOS_CLASS_USER_INTERACTIVE; advisory, P-core placement NOT verified"},
        "compiler": {"compcert": capture([str(compcert), "-version"]),
                     "compcert_sha256": digest(compcert.read_bytes()),
                     "clang": capture([args.clang, "--version"])},
        "protocol": {key: manifest[key] for key in ("samples_per_block", "blocks", "min_sample_seconds",
                     "max_relative_mad", "max_block_drift", "target_gap_fraction")},
        "benchmarks": {}, "block_load_average": [], "correctness_pass": False, "noise_pass": False,
    }
    # Failures must never leave a stale success report at the requested path.
    output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        temporary = output.with_suffix(output.suffix + ".tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(output)

    save()
    try:
        report["compile_commands"] = compile_suite(manifest, str(compcert), args.clang)
        if args.correctness_only:
            for case in manifest["benchmarks"]:
                for label in ("compcert", "clang"):
                    measure(ARTIFACTS / f"{case['name']}.{label}", case)
                report["benchmarks"][case["name"]] = {
                    "stdout_sha256": manifest["sha256"][case["expected"]], "correctness_pass": True}
                print(f"{case['name']}: both compilers match the reference", flush=True)
            report["correctness_pass"] = True
            report["performance_measured"] = False
            save()
            return
        # Calibrate batches from the faster executable; both use identical work.
        batches = {}
        for case in manifest["benchmarks"]:
            timings = [measure(ARTIFACTS / f"{case['name']}.{label}", case)
                       for label in ("compcert", "clang")]
            batches[case["name"]] = max(1, math.ceil(manifest["min_sample_seconds"] / min(timings)))
            report["benchmarks"][case["name"]] = {
                "batch_processes": batches[case["name"]], "stdout_sha256": manifest["sha256"][case["expected"]],
                "samples": {label: [[] for _ in range(manifest["blocks"])] for label in ("compcert", "clang")}}
        rng = random.Random(20261104)
        for block in range(manifest["blocks"]):
            report["block_load_average"].append(list(os.getloadavg()))
            cases = list(manifest["benchmarks"])
            rng.shuffle(cases)
            for case in cases:
                name = case["name"]
                entry = report["benchmarks"][name]
                for label in ("compcert", "clang"):
                    measure(ARTIFACTS / f"{name}.{label}", case)  # unmeasured warm-up per block
                for sample in range(manifest["samples_per_block"]):
                    labels = ["compcert", "clang"]
                    if (block + sample) % 2:
                        labels.reverse()
                    for label in labels:
                        raw = [measure(ARTIFACTS / f"{name}.{label}", case) for _ in range(batches[name])]
                        entry["samples"][label][block].append(raw)
                print(f"block {block + 1}: {name}: stdout OK", flush=True)
                save()
        report["correctness_pass"] = True
        noise_pass = True
        ratios = []
        print("\nbenchmark        CompCert/clang    runtime gap       noise", flush=True)
        for name, entry in report["benchmarks"].items():
            entry["statistics"] = {}
            entry["noise_pass"] = True
            for label, blocks in entry["samples"].items():
                averaged = [[statistics.mean(raw) for raw in block] for block in blocks]
                stats = [metrics(block) for block in averaged]
                medians = [x["median_seconds"] for x in stats]
                drift = max(medians) / min(medians) - 1
                okay = drift <= manifest["max_block_drift"] and all(
                    s["relative_mad"] <= manifest["max_relative_mad"] for s in stats)
                entry["statistics"][label] = {
                    "blocks": stats, "block_drift": drift,
                    "median_seconds": statistics.median(medians), "noise_pass": okay}
                entry["noise_pass"] &= okay
            ratio = entry["statistics"]["compcert"]["median_seconds"] / entry["statistics"]["clang"]["median_seconds"]
            entry["time_ratio"] = ratio
            entry["runtime_gap_percent"] = 100 * (ratio - 1)
            ratios.append(ratio)
            noise_pass &= entry["noise_pass"]
            print(f"{name:16s} {ratio:12.4f}x {100 * (ratio - 1):+13.2f}%     {'PASS' if entry['noise_pass'] else 'FAIL'}")
        report["noise_pass"] = noise_pass
        report["geomean_time_ratio"] = geomean(ratios)
        report["geomean_runtime_gap_percent"] = 100 * (report["geomean_time_ratio"] - 1)
        if baseline.exists() and baseline.resolve() != output:
            original = json.loads(baseline.read_text())
            if original["suite_sha256"] != report["suite_sha256"]:
                raise RuntimeError("Baseline belongs to a different suite")
            if original["machine"]["cpu"] != report["machine"]["cpu"] or original["compiler"]["clang"] != report["compiler"]["clang"]:
                raise RuntimeError("Baseline CPU/clang differs; performance target comparison invalid")
            if original["noise_pass"] and original["correctness_pass"]:
                r0 = original["geomean_time_ratio"]
                if r0 > 1:
                    report["gap_closed_fraction"] = (r0 - report["geomean_time_ratio"]) / (r0 - 1)
                    report["target_time_ratio"] = 1 + (1 - manifest["target_gap_fraction"]) * (r0 - 1)
                    report["target_met"] = noise_pass and report["gap_closed_fraction"] >= manifest["target_gap_fraction"]
        save()
        print(f"Geometric mean: {report['geomean_time_ratio']:.4f}x; noise {'PASS' if noise_pass else 'FAIL'}")
        print(f"Report: {output}")
        if not noise_pass:
            raise SystemExit(2)
    except Exception as error:
        report["error"] = str(error)
        report["noise_pass"] = False
        save()
        raise


if __name__ == "__main__":
    main()
