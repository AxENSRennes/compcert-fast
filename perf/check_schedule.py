#!/usr/bin/env python3
"""Native checks of the extracted, proved adjacent-operation scheduler."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/schedule"
OUTPUT = ROOT / "perf/results/schedule.json"


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False,
              "scope": "one validated independent adjacent Iop pair per function", "commands": []}

    def save():
        temporary = OUTPUT.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(OUTPUT)

    save()
    try:
        subprocess.run(["python3", str(ROOT / "perf/guard.py")], cwd=ROOT, check=True)
        deps = subprocess.check_output([str(ROOT / "tools/modorder"), ".depend.extr",
                                       "lib/Camlcoq.cmx", "extraction/Schedule.cmx"], cwd=ROOT, text=True).split()
        includes = [arg for d in ["extraction", "lib", "common", "aarch64", "backend", "cfrontend",
                                 "cparser", "driver", "export", "debug"] for arg in ("-I", str(ROOT/d))]
        obj, binary = ARTIFACTS/"test_schedule.cmx", ARTIFACTS/"check_schedule"
        with (ARTIFACTS/"build.log").open("w") as log:
            for command in [
                [ROOT/"perf/in-env", "ocamlopt", "-g", *includes, "-c", ROOT/"perf/test_schedule.ml", "-o", obj],
                [ROOT/"perf/in-env", "ocamlopt", "-g", *includes, "-o", binary,
                 "str.cmxa", "unix.cmxa", *deps, obj],
            ]:
                report["commands"].append([str(arg) for arg in command])
                subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        env = os.environ.copy()
        env["COMPCERT_CONFIG"] = str(ROOT/"compcert.ini")
        env["COMPCERT_EXPERIMENTS"] = ""
        env.pop("COMPCERT_EXPERIMENT_TRACE", None)
        result = subprocess.run([str(binary)], cwd=ROOT, env=env, capture_output=True, text=True)
        (ARTIFACTS/"native.stdout").write_text(result.stdout)
        (ARTIFACTS/"native.stderr").write_text(result.stderr)
        result.check_returncode()
        actual = json.loads(result.stdout)
        if not actual.get("success") or not actual.get("checks"):
            raise RuntimeError("Native scheduling tests did not report success")
        report.update(actual)
        report["check_count"] = len(actual["checks"])
        report["source_sha256"] = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
            ["backend/Schedule.v", "backend/Scheduleproof.v", "extraction/Schedule.ml",
             "perf/test_schedule.ml", "perf/check_schedule.py"]}
        save()
        print(f"{report['check_count']} scheduling checks and {report['execution_cases']} execution cases passed")
    except Exception as error:
        report["error"] = str(error)
        report["success"] = False
        save()
        raise


if __name__ == "__main__":
    main()
