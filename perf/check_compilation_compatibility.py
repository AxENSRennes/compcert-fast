#!/usr/bin/env python3
"""Check raw compilation regressions, automatic retry, and mixed linkage."""

from concurrent.futures import ThreadPoolExecutor
import errno
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/compilation-compatibility"
OUTPUT = ROOT / "perf/results/compilation-compatibility.json"
INVENTORY = ROOT / "perf/compilation-compatibility.json"
FALLBACK = "COMPCERT_EXPERIMENT_FALLBACK"
RETRY = "experimental compilation failed; retrying with experiments disabled"
ALIAS = "input and output alias; compiling with experiments disabled"
NONREGULAR = "input is not a regular file; compiling with experiments disabled"
PACKED_ADD = "__builtin_cc_neon_add_u32x2"
NEON_ADD = re.compile(r"^\s*add\s+v\d+\.2s,\s*v\d+\.2s,", re.M)

PACKED_NAME = "int __builtin_cc_neon_add_u32x2(void) { return 0; }\n"
PACKED_DECLARATION = """extern unsigned long long __builtin_cc_neon_add_u32x2(
    unsigned long long, unsigned long long);
unsigned long long call_external(void)
{
    return __builtin_cc_neon_add_u32x2(0, 0);
}
"""
STACK_LIMIT = """/* Compile only. These arrays total 2^64 - 64 bytes. */
extern void use_arrays(char *, char *, char *, char *);
extern void observe(int, int);
int frame_limit(int n, int x, int d)
{
    char a[4611686018427387888UL], b[4611686018427387888UL];
    char c[4611686018427387888UL], e[4611686018427387888UL];
    int sum = 0;
    use_arrays(a, b, c, e);
    while (n > 0) {
        observe(x, d);
        sum += x / d;
        --n;
    }
    return x + sum;
}
"""
PURE_LICM_LIMIT = STACK_LIMIT.replace("sum += x / d;", "sum ^= x * d;")
HOIST_LIMIT = STACK_LIMIT.replace("extern void observe(int, int);",
                                 "extern void observe(int, int);\nextern int hash(int, int);")
HOIST_LIMIT = HOIST_LIMIT.replace("sum += x / d;", "sum += hash(0x12634921, x);")
STRENGTH_LIMIT = """/* Compile only. The induction cache adds values live across observe. */
extern void use_arrays(char *, char *, char *, char *);
extern void observe(unsigned, unsigned);
unsigned strength_limit(unsigned n, unsigned step)
{
    char a[4611686018427387888UL], b[4611686018427387888UL];
    char c[4611686018427387888UL], e[4611686018427387888UL];
    unsigned sum = 0;
    use_arrays(a, b, c, e);
    for (unsigned i = 0; i < n; ++i) {
        observe(i, step);
        sum ^= i * step;
    }
    return sum;
}
"""
INLINE_LIMIT = """/* Compile only. Each frame fits before leaf inlining. */
extern void use_arrays(char *, char *, char *);
int leaf(unsigned n)
{
    volatile char a[4611686018427387903UL];
    return a[n] = 1;
}
int frame(unsigned n)
{
    char a[4611686018427387903UL], b[4611686018427387903UL];
    char c[4611686018427387903UL];
    use_arrays(a, b, c);
    return leaf(n) + 1;
}
"""
TILE_LIMIT = """/* Compile only. Tiling adds a counter live across observe. */
extern void use_arrays(char *, char *, char *, char *);
extern void observe(unsigned, unsigned);
unsigned tile_limit(unsigned n, unsigned x)
{
    char a[4611686018427387888UL], b[4611686018427387888UL];
    char c[4611686018427387888UL], d[4611686018427387888UL];
    unsigned sum = 0;
    use_arrays(a, b, c, d);
    for (unsigned i = 0; i < n; ++i) {
        observe(i, x);
        sum ^= x;
    }
    return sum;
}
"""
MIXED_WORKER = """_Alignas(8) unsigned cells[8];
void bump(unsigned n)
{
    for (unsigned i = 0; i < n; ++i) cells[i] += 7u;
}
"""
PACKED_WORKER = """typedef unsigned long long u64;
u64 packed_probe(u64 a, u64 b)
{
    return __builtin_cc_neon_add_u32x2(a, b);
}
static u64 ordinary_product(u64 a, u64 b)
{
    return a * b;
}
u64 shadow_probe(u64 a, u64 b)
{
    u64 (*__builtin_cc_neon_add_u32x2)(u64, u64) = ordinary_product;
    return __builtin_cc_neon_add_u32x2(a, b);
}
"""
MIXED_MAIN = """_Alignas(8) extern unsigned cells[8];
extern void bump(unsigned);
extern unsigned long long call_external(void);
extern unsigned long long packed_probe(unsigned long long, unsigned long long);
extern unsigned long long shadow_probe(unsigned long long, unsigned long long);
int main(void)
{
    cells[0] = ~0u;
    cells[1] = 4;
    cells[2] = 8;
    cells[3] = 11;
    bump(3);
    return call_external() != 99
        || packed_probe(0x00000001ffffffffULL, 0x0000000200000001ULL) != 0x0000000300000000ULL
        || shadow_probe(3, 5) != 15
        || cells[0] != 6 || cells[1] != 11 || cells[2] != 15 || cells[3] != 11;
}
"""
MIXED_CALLEE = """unsigned long long __builtin_cc_neon_add_u32x2(
    unsigned long long a, unsigned long long b)
{
    return 99;
}
"""
LINK_MAIN = """_Alignas(8) extern unsigned cells[8];
extern void bump(unsigned);
int main(void)
{
    bump(1);
    return cells[0] != 7 || cells[1] != 0;
}
"""


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def save(report):
    temporary = OUTPUT.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2) + "\n")
    temporary.replace(OUTPUT)


def feed_fifo(path, content):
    deadline = time.monotonic() + 30
    while True:
        try:
            fd = os.open(path, os.O_WRONLY | os.O_NONBLOCK)
            break
        except OSError as error:
            if error.errno != errno.ENXIO or time.monotonic() >= deadline:
                raise
            time.sleep(0.01)
    with os.fdopen(fd, "wb") as stream:
        stream.write(content)


def check_inventory(report):
    inventory = json.loads(INVENTORY.read_text())
    options = (ROOT / "backend/ExperimentalOptions.ml").read_text()
    declaration = re.search(r"^let known_flags = \[([^\]]*)\]", options, re.M)
    require(declaration is not None, "Missing ExperimentalOptions.known_flags list")
    flags = re.findall(r'"([^"]+)"', declaration[1])
    optimizations = inventory["optimizations"]
    require(len(set(flags)) == len(flags) and set(optimizations) == set(flags),
            "Compatibility inventory must cover each known experiment exactly once")
    strict_cases = report["strict_regressions"]
    covered = set()
    for flag, item in optimizations.items():
        require(item["category"] in ("fallback", "proved"), f"{flag}: invalid category")
        require(item["paths"], f"{flag}: missing optimization paths")
        evidence = item["proofs"] + item["tests"]
        require(evidence and all((ROOT / path).is_file() for path in evidence),
                f"{flag}: missing proof or test files")
        for case in item["strict_regressions"]:
            require(case in strict_cases and flag in strict_cases[case]["outcomes"]["strict"]["flags"].split(","),
                    f"{flag}: wrong strict regression {case}")
            covered.add(case)
    require(covered == set(strict_cases), "Compatibility inventory omitted a known strict regression")
    require("open_cases" in inventory, "Compatibility inventory must report any open cases")
    report["inventory"] = {"checked_optimizations": len(flags), "sha256": sha(INVENTORY)}


class Harness:
    def __init__(self, run_directory):
        self.run_directory = run_directory
        self.compiler = [str(ROOT / "ccomp"), "-stdlib", str(ROOT / "runtime")]
        self.config = ROOT / "compcert.ini"

    def directory(self, name):
        directory = self.run_directory / name
        directory.mkdir()
        return directory

    def run(self, command, directory, label, *, flags="", fallback=False, config=None,
            trace=None, tempdir=None):
        environment = os.environ.copy()
        environment.update(COMPCERT_EXPERIMENTS=flags, COMPCERT_CONFIG=str(config or self.config))
        environment.pop("COMPCERT_EXPERIMENT_TRACE", None)
        if trace is not None:
            environment["COMPCERT_EXPERIMENT_TRACE"] = str(trace)
        if tempdir is not None:
            environment["TMPDIR"] = str(tempdir)
        environment.pop(FALLBACK, None)
        if not fallback:
            environment[FALLBACK] = "0"
        with subprocess.Popen(command, cwd=directory, env=environment, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
            try:
                stdout, stderr = process.communicate(timeout=120)
            except subprocess.TimeoutExpired:
                # The compiler supervisor forwards TERM to its attempt.
                process.terminate()
                try:
                    process.communicate(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.communicate()
                raise
        (directory / (label + ".stdout")).write_text(stdout)
        (directory / (label + ".stderr")).write_text(stderr)
        return {
            "exit": process.returncode, "diagnostic": stderr.strip(),
            "flags": flags, "automatic_fallback": fallback,
        }

    def run_fifo(self, fifo, content, *args, **kwargs):
        os.mkfifo(fifo)
        try:
            with ThreadPoolExecutor(max_workers=1) as executor:
                writer = executor.submit(feed_fifo, fifo, content)
                result = self.run(*args, **kwargs)
                writer.result()
            return result
        finally:
            fifo.unlink()

    def natural_regression(self, name, source, flags, stage, expected, options, report):
        directory = self.directory(name)
        input_file = directory / "input.c"
        input_file.write_text(source)
        output = directory / "output.o"
        command = [*self.compiler, *options, "input.c", "-o", output.name]
        evidence = {"stage": stage, "source": source, "source_sha256": sha(input_file),
                    "working_directory": str(directory), "command": command,
                    "compcert_config": str(self.config), "outcomes": {}}
        report["strict_regressions"][name] = evidence
        trace = directory / "trace.jsonl"
        for label, active_flags, fallback in [
            ("reference", "", False), ("strict", flags, False), ("fallback", flags, True)
        ]:
            result = self.run(command, directory, label, flags=active_flags, fallback=fallback,
                              trace=trace)
            evidence["outcomes"][label] = result
            events = []
            if trace.exists():
                events = [json.loads(line) for line in trace.read_text().splitlines()]
                trace.rename(directory / f"{label}-trace.jsonl")
            if label == "strict":
                require(result["exit"] == 2 and expected in result["diagnostic"],
                        f"{name}: strict attempt did not report {expected!r}")
                require(RETRY not in result["diagnostic"], f"{name}: strict attempt retried")
                require(not output.exists(), f"{name}: failed strict attempt produced output")
                event = {"Inlining.transf_function": "selected",
                         "Stacking.transf_function": "changed-functions"}.get(stage, "enabled")
                result["optimization_events"] = [
                    entry for entry in events if entry["pass"] == flags
                    and entry["event"] == event and entry["count"] > 0
                ]
                require(result["optimization_events"], f"{name}: missing experiment activity")
            else:
                require(result["exit"] == 0 and output.is_file(), f"{name}: {label} did not compile")
                require(result["diagnostic"].count(RETRY) == int(fallback),
                        f"{name}: unexpected retry diagnostic in {label}")
                result["output_sha256"] = sha(output)
                output.rename(directory / f"{label}-{output.name}")
            if "-dmach" in options:
                # The raw Stacking failure has LTL but no Mach. The
                # earlier raw Inlining failure has neither.
                ltl, mach = directory / "input.ltl", directory / "input.mach"
                result["ltl_dump"] = ltl.is_file()
                result["mach_dump"] = mach.is_file()
                require(result["ltl_dump"] == (label != "strict" or stage == "Stacking.transf_function")
                        and result["mach_dump"] == (label != "strict"),
                        f"{name}: unexpected pass dumps in {label}")
                for dump in (ltl, mach):
                    if dump.exists():
                        result[f"{dump.suffix[1:]}_sha256"] = sha(dump)
                        dump.rename(directory / f"{label}-{dump.name}")
        require(evidence["outcomes"]["reference"]["output_sha256"] ==
                evidence["outcomes"]["fallback"]["output_sha256"],
                f"{name}: retry output differs from the reference")
        return directory / f"fallback-{output.name}"

    def mixed_link(self, caller, report):
        directory = self.directory("mixed-link")
        worker = directory / "worker.c"
        worker.write_text(MIXED_WORKER)
        packed = directory / "packed.c"
        packed.write_text(PACKED_WORKER)
        callee = directory / "callee.c"
        callee.write_text(MIXED_CALLEE)
        main = directory / "main.c"
        main.write_text(MIXED_MAIN)
        commands = {
            "worker_assembly": [*self.compiler, "-S", "worker.c", "-o", "worker.s"],
            "worker": [*self.compiler, "-c", "worker.c", "-o", "worker.o"],
            "packed_assembly": [*self.compiler, "-S", "-drtl", "packed.c", "-o", "packed.s"],
            "packed": [*self.compiler, "-c", "packed.c", "-o", "packed.o"],
            "callee": [*self.compiler, "-c", "callee.c", "-o", "callee.o"],
            "main": [*self.compiler, "-c", "main.c", "-o", "main.o"],
            "link": [*self.compiler, "main.o", str(caller), "worker.o", "packed.o",
                     "callee.o", "-o", "mixed"],
            "execute": [str(directory / "mixed")],
        }
        evidence = {
            "working_directory": str(directory),
            "source_sha256": {file.name: sha(file) for file in (worker, packed, callee, main)},
            "fallback_inputs": ["packed-builtin-declaration fallback object", "callee.o"],
            "commands": commands, "outcomes": {},
        }
        report["mixed_link"] = evidence
        for label, command in commands.items():
            if label.startswith("worker"):
                flags = "memory-neon,neon-packed"
            elif label.startswith("packed") or label == "callee":
                flags = "neon-packed"
            else:
                flags = ""
            result = self.run(command, directory, label, flags=flags, fallback=(label == "callee"))
            evidence["outcomes"][label] = result
            require(result["exit"] == 0, f"Mixed link: {label} failed")
            require((RETRY in result["diagnostic"]) == (label == "callee"),
                    f"Mixed link: unexpected retry state for {label}")
        require(NEON_ADD.search((directory / "worker.s").read_text()) is not None,
                "Mixed link: optimized unit did not emit NEON")
        packed_assembly = (directory / "packed.s").read_text()
        packed_rtl = (directory / "packed.rtl.0").read_text()
        require(NEON_ADD.search(packed_assembly) is not None and PACKED_ADD not in packed_assembly,
                "Mixed link: packed intrinsic did not lower locally to NEON")
        require(f'builtin "{PACKED_ADD}"(' in packed_rtl,
                "Mixed link: packed intrinsic is not a direct RTL builtin")
        evidence["optimized_worker_neon"] = True
        evidence["packed_intrinsic_lowered"] = True
        evidence["ordinary_symbol_and_local_shadow_preserved"] = True

    def injected_tool_failure(self, tool, report):
        assembling = tool == "asm"
        stage = "assembler" if assembling else "linker"
        directory = self.directory("injected-" + stage)
        input_file = directory / "worker.c"
        input_file.write_text(MIXED_WORKER)
        if assembling:
            condition = f"re.search({NEON_ADD.pattern!r}, Path(sys.argv[-1]).read_text(), re.M)"
            output = directory / "worker.o"
            command = [*self.compiler, "-c", "worker.c", "-o", output.name]
        else:
            (directory / "main.c").write_text(LINK_MAIN)
            condition = "'memory-neon' in os.environ.get('COMPCERT_EXPERIMENTS', '').split(',')"
            output = directory / "linked"
            command = [*self.compiler, "worker.c", "main.c", "-o", output.name]
        config = directory / "compcert.ini"
        lines = self.config.read_text().splitlines()
        key = tool + "="
        original_tool = next(shlex.split(line.removeprefix(key)) for line in lines
                             if line.startswith(key))
        wrapper = directory / ("reject-optimized-" + stage)
        wrapper.write_text(f"""#!/usr/bin/env python3
import os
from pathlib import Path
import re
import sys

reject = {condition}
with Path(__file__).with_name("attempts.log").open("a") as attempts:
    attempts.write("reject\\n" if reject else "accept\\n")
if reject:
    sys.exit("injected {stage} rejection of optimized attempt")
os.execvp({original_tool[0]!r}, {original_tool!r} + sys.argv[1:])
""")
        wrapper.chmod(0o755)
        config.write_text("\n".join(key + "./" + wrapper.name if line.startswith(key) else line
                                    for line in lines) + "\n")
        evidence = {
            "stage": "native " + stage, "injected": True,
            "source_sha256": {source.name: sha(source) for source in directory.glob("*.c")},
            "working_directory": str(directory), "compcert_config": str(config),
            "command": command, "outcomes": {},
        }
        report["injected_" + stage + "_failure"] = evidence
        for label, flags, fallback, expected_attempts in [
            ("reference", "", False, ["accept"]),
            ("strict", "memory-neon", False, ["reject"]),
            ("fallback", "memory-neon", True, ["reject", "accept"]),
        ]:
            result = self.run(command, directory, label, flags=flags, fallback=fallback, config=config)
            evidence["outcomes"][label] = result
            attempts = directory / "attempts.log"
            result[stage + "_attempts"] = attempts.read_text().splitlines()
            attempts.rename(directory / (label + "-attempts.log"))
            require(result[stage + "_attempts"] == expected_attempts,
                    f"{stage}: unexpected attempts in {label}")
            require((RETRY in result["diagnostic"]) == fallback,
                    f"{stage}: unexpected retry in {label}")
            if label == "strict":
                require(result["exit"] != 0 and not output.exists()
                        and f"injected {stage} rejection" in result["diagnostic"],
                        f"{stage}: strict compile did not fail in the injected tool")
            else:
                require(result["exit"] == 0 and output.is_file(),
                        f"{stage}: {label} produced no output")
                result["output_sha256"] = sha(output)
                if not assembling:
                    execution = self.run([str(output)], directory, label + "-run")
                    result["execution_exit"] = execution["exit"]
                    require(execution["exit"] == 0, f"{stage}: {label} output behaved incorrectly")
                output.rename(directory / f"{label}-{output.name}")
        if assembling:
            require(evidence["outcomes"]["reference"]["output_sha256"] ==
                    evidence["outcomes"]["fallback"]["output_sha256"],
                    "Assembler injection: retry object differs from the reference")
            self.aliased_output(config, directory, report)
            self.stream_inputs(config, directory, report)

    def aliased_output(self, config, directory, report):
        evidence = {}
        report["aliased_output"] = evidence
        source = directory / "worker.c"
        for case, output, options in [
            ("explicit", source, ["-o", source.name]),
            ("default_hardlink", directory / "worker.o", []),
        ]:
            command = [*self.compiler, "-c", source.name, *options]
            results = {}
            evidence[case] = {"command": command, "outcomes": results}
            for label, flags, fallback in [("reference", "", False), ("fallback", "memory-neon", True)]:
                source.write_text(MIXED_WORKER)
                if output != source:
                    output.hardlink_to(source)
                attempt = f"alias-{case}-{label}"
                result = self.run(command, directory, attempt, flags=flags, fallback=fallback,
                                  config=config)
                results[label] = result
                attempts = directory / "attempts.log"
                result["assembler_attempts"] = attempts.read_text().splitlines()
                attempts.rename(directory / (attempt + "-attempts.log"))
                require(result["exit"] == 0 and output.is_file(),
                        f"Aliased output: {case} {label} did not compile")
                require(result["assembler_attempts"] == ["accept"],
                        f"Aliased output: {case} {label} made an optimized attempt")
                require((ALIAS in result["diagnostic"]) == fallback and RETRY not in result["diagnostic"],
                        f"Aliased output: {case} {label} did not choose the expected path")
                result["output_sha256"] = sha(output)
                output.rename(directory / (attempt + ".o"))
                if output != source:
                    source.unlink()
            require(results["reference"]["output_sha256"] == results["fallback"]["output_sha256"],
                    f"Aliased output: {case} reference and fallback objects differ")

    def stream_inputs(self, config, directory, report):
        source = directory / "worker.c"
        response = directory / "compile.rsp"
        fifo_source = [*self.compiler, "-c", source.name, "-o", "stream.o"]
        fifo_response = [*self.compiler, "@" + response.name]
        evidence = {}
        report["stream_inputs"] = evidence
        for case, fifo, content, command, expected_attempts, marker, output in [
            ("source_fifo", source, MIXED_WORKER.encode(), fifo_source,
             ["accept"], NONREGULAR, "stream.o"),
            ("response_fifo", response, b"-c worker.c -o response.o\n", fifo_response,
             ["reject", "accept"], RETRY, "response.o"),
        ]:
            if fifo == response:
                source.write_text(MIXED_WORKER)
            result = self.run_fifo(fifo, content, command, directory, case, flags="memory-neon",
                                   fallback=True, config=config)
            evidence[case] = {"command": command, "outcome": result}
            attempts = directory / "attempts.log"
            result["assembler_attempts"] = attempts.read_text().splitlines()
            attempts.rename(directory / (case + "-attempts.log"))
            artifact = directory / output
            require(result["exit"] == 0 and artifact.is_file(),
                    f"Stream input: {case} did not compile")
            require(result["assembler_attempts"] == expected_attempts and marker in result["diagnostic"],
                    f"Stream input: {case} did not choose the expected path")
            result["output_sha256"] = sha(artifact)
            require(result["output_sha256"] == sha(directory / "reference-worker.o"),
                    f"Stream input: {case} object differs from the reference")

    def trace_paths(self, report):
        directory = self.directory("trace-paths")
        source = directory / "worker.c"
        source.write_text(MIXED_WORKER)
        invalid = directory / "invalid-trace"
        invalid.mkdir()
        valid = directory / "valid.jsonl"
        command = [*self.compiler, "-S", "worker.c", "-o", "worker.s"]
        evidence = {"command": command, "outcomes": {}}
        report["trace_paths"] = evidence
        for label, trace in [("valid", valid), ("invalid_destination", invalid)]:
            result = self.run(command, directory, label, flags="memory-neon", fallback=True,
                              trace=trace)
            evidence["outcomes"][label] = result
            require(result["exit"] == 0 and RETRY not in result["diagnostic"],
                    f"Trace path: {label} did not compile on the optimized path")
            assembly = directory / "worker.s"
            require(NEON_ADD.search(assembly.read_text()) is not None,
                    f"Trace path: {label} lost the optimization")
            result["output_sha256"] = sha(assembly)
            assembly.rename(directory / (label + ".s"))
        require(evidence["outcomes"]["valid"]["output_sha256"] ==
                evidence["outcomes"]["invalid_destination"]["output_sha256"],
                "Trace path changed the compiled output")
        events = [json.loads(line) for line in valid.read_text().splitlines()]
        evidence["startup_events"] = [
            entry for entry in events if entry["pass"] == "memory-neon" and entry["event"] == "enabled"
        ]
        require(evidence["startup_events"] == [{"pass": "memory-neon", "event": "enabled", "count": 1}],
                "Expected exactly one enabled event from the compilation child")
        result = self.run(command, directory, "aliases_input", flags="memory-neon",
                          fallback=True, trace=source)
        evidence["outcomes"]["aliases_input"] = result
        require(result["exit"] == 0 and ALIAS in result["diagnostic"],
                "Trace path alias did not choose the reference path")
        require(source.read_text() == MIXED_WORKER, "Trace path alias changed the source")
        require(NEON_ADD.search((directory / "worker.s").read_text()) is None,
                "Trace path alias still used the optimization")

    def transitive_trace_input(self, report):
        directory = self.directory("transitive-trace-input")
        (directory / "worker.c").write_text('#include "trace.h"\n' + MIXED_WORKER)
        header = directory / "trace.h"
        initial = "#define UNUSED_HEADER 1\n"
        output = directory / "worker.s"
        command = [*self.compiler, "-S", "worker.c", "-o", output.name]
        outcomes = {}
        report["transitive_trace_input"] = {"command": command, "outcomes": outcomes}
        for label, flags, fallback in [
            ("reference", "", False), ("strict", "memory-neon", False),
            ("fallback", "memory-neon", True),
        ]:
            header.write_text(initial)
            result = self.run(command, directory, label, flags=flags, fallback=fallback,
                              trace=header)
            outcomes[label] = result
            if label == "strict":
                require(result["exit"] == 2 and not output.exists()
                        and header.read_text() != initial,
                        "Transitive trace input did not reproduce the strict failure")
            else:
                require(result["exit"] == 0 and header.read_text() == initial,
                        f"Transitive trace input failed in {label}")
                result["output_sha256"] = sha(output)
                output.rename(directory / (label + ".s"))
            require((RETRY in result["diagnostic"]) == fallback,
                    f"Transitive trace input used an unexpected path in {label}")
        require(outcomes["reference"]["output_sha256"] == outcomes["fallback"]["output_sha256"],
                "Transitive trace input retry differs from reference")

    def large_response_file(self, report):
        directory = self.directory("large-response-file")
        (directory / "input.i").write_text("int example(void) { return 0; }\n")
        response = directory / "compile.rsp"
        response.write_text("-S input.i -o output.s\n" +
                            ("-DUNUSED=" + "x" * 250 + "\n") * 5000)
        command = [*self.compiler, "@" + response.name]
        output = directory / "output.s"
        outcomes = {}
        report["large_response_file"] = {
            "command": command, "response_bytes": response.stat().st_size, "outcomes": outcomes,
        }
        for label, flags, fallback in [("reference", "", False), ("fallback", "small-inline", True)]:
            result = self.run(command, directory, label, flags=flags, fallback=fallback,
                              tempdir=directory / "missing-temp")
            outcomes[label] = result
            require(result["exit"] == 0 and output.is_file(),
                    f"Large response file failed in {label}")
            result["output_sha256"] = sha(output)
            output.rename(directory / (label + ".s"))
        require(outcomes["reference"]["output_sha256"] == outcomes["fallback"]["output_sha256"],
                "Large response file retry differs from reference")

    def transitive_dump_inputs(self, report):
        evidence = {}
        report["transitive_dump_inputs"] = evidence
        for case, prefix, header_text in [
            ("overwritten_include", '#include "input.rtl.0"\n', "#define UNUSED_HEADER 1\n"),
            ("new_include", '#if __has_include("input.rtl.0")\n'
             '#error unexpected dump from failed attempt\n#endif\n', None),
        ]:
            directory = self.directory(case)
            source = directory / "input.c"
            source.write_text(prefix + STACK_LIMIT)
            header = directory / "input.rtl.0"
            output = directory / "output.o"
            command = [*self.compiler, "-c", "-drtl", "-fno-inline", "-O2",
                       source.name, "-o", output.name]
            outcomes = {}
            evidence[case] = {
                "stage": "Stacking.transf_function",
                "working_directory": str(directory),
                "source_sha256": sha(source),
                "header_seed": header_text,
                "command": command,
                "outcomes": outcomes,
            }
            for label, flags, fallback in [
                ("reference", "", False),
                ("strict", "licm-preheader", False),
                ("fallback", "licm-preheader", True),
            ]:
                # Restore the initial preprocessor input before each invocation.
                # Within the fallback invocation, the compiler must do this itself.
                if header_text is None:
                    header.unlink(missing_ok=True)
                else:
                    header.write_text(header_text)
                result = self.run(command, directory, label, flags=flags, fallback=fallback)
                outcomes[label] = result
                require(header.is_file() and header.read_text() != header_text,
                        f"{case}: {label} did not produce an RTL dump")
                result["dump_sha256"] = sha(header)
                if label == "strict":
                    require(result["exit"] == 2 and not output.exists()
                            and "Too many spilled variables, stack size exceeded" in result["diagnostic"],
                            f"{case}: strict attempt did not fail at Stacking")
                else:
                    require(result["exit"] == 0 and output.is_file(),
                            f"{case}: {label} did not compile")
                    result["output_sha256"] = sha(output)
                    output.rename(directory / (label + ".o"))
                require((RETRY in result["diagnostic"]) == fallback,
                        f"{case}: unexpected retry state for {label}")
            for artifact in ("output_sha256", "dump_sha256"):
                require(outcomes["reference"][artifact] == outcomes["fallback"][artifact],
                        f"{case}: retry output differs from reference")


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False, "strict_regressions": {}}
    save(report)
    try:
        compiler_sha256 = sha(ROOT / "ccomp")
        harness = Harness(Path(tempfile.mkdtemp(prefix="check-", dir=ARTIFACTS)))
        harness.natural_regression(
            "packed-builtin-name", PACKED_NAME, "neon-packed", "C frontend elaboration",
            "definition of builtin function '__builtin_cc_neon_add_u32x2'", ["-c"], report,
        )
        for name, source, flags in [
            ("preheader-stack-limit", STACK_LIMIT, "licm-preheader"),
            ("pure-licm-stack-limit", PURE_LICM_LIMIT, "licm-pure"),
            ("hoist-constant-stack-limit", HOIST_LIMIT, "hoist-constant"),
            ("strength-reduce-stack-limit", STRENGTH_LIMIT, "strength-reduce"),
            ("loop-tile-stack-limit", TILE_LIMIT, "loop-tile"),
        ]:
            harness.natural_regression(
                name, source, flags, "Stacking.transf_function",
                "Too many spilled variables, stack size exceeded",
                ["-c", "-dltl", "-dmach", "-fno-inline", "-O2"], report,
            )
        harness.natural_regression(
            "small-inline-stack-limit", INLINE_LIMIT, "small-inline", "Inlining.transf_function",
            "Inlining: stack too big", ["-c", "-dltl", "-dmach", "-O2"], report,
        )
        caller = harness.natural_regression(
            "packed-builtin-declaration", PACKED_DECLARATION, "neon-packed", "C2C.convertProgram",
            "explicit declaration of experimental builtin '__builtin_cc_neon_add_u32x2'",
            ["-c"], report,
        )
        harness.mixed_link(caller, report)
        harness.injected_tool_failure("asm", report)
        harness.injected_tool_failure("linker", report)
        harness.trace_paths(report)
        harness.transitive_trace_input(report)
        harness.large_response_file(report)
        harness.transitive_dump_inputs(report)
        check_inventory(report)
        report["source_sha256"] = {
            "perf/check_compilation_compatibility.py": sha(Path(__file__)),
            "perf/compilation-compatibility.json": sha(INVENTORY),
        }
        require(compiler_sha256 == sha(ROOT / "ccomp"), "Compiler changed while running compatibility checks")
        report["compiler_sha256"] = compiler_sha256
        report["success"] = True
        save(report)
        print("Compilation regressions, automatic retry, and mixed linkage passed")
    except BaseException as error:
        report["error"] = str(error)
        save(report)
        raise


if __name__ == "__main__":
    main()
