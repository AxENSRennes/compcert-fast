#!/usr/bin/env python3
"""Validate alternate ARM64 combinations with existing modeled instructions.

This checks constructor changes, actual generated MSUB-family instructions,
and exact unsigned C outputs. It claims neither fewer instructions nor speed.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/select"
OUTPUT = ROOT / "perf/results/select.json"
SOURCE = r'''
#include <stdio.h>
unsigned negmul32(unsigned x, unsigned y) { return -(x * y); }
unsigned long long negmul64(unsigned long long x, unsigned long long y) { return -(x * y); }
int main(void) {
  static const unsigned long long inputs[] = {
    0ULL, 1ULL, 2ULL, 0x7fffffffULL, 0x80000000ULL, 0xffffffffULL,
    0x7fffffffffffffffULL, 0x8000000000000000ULL, 0xffffffffffffffffULL
  };
  unsigned i, j;
  for (i=0; i<sizeof(inputs)/sizeof(inputs[0]); i++)
    for (j=0; j<sizeof(inputs)/sizeof(inputs[0]); j++)
      printf("%u %llu\n", negmul32((unsigned)inputs[i], (unsigned)inputs[j]),
             negmul64(inputs[i], inputs[j]));
  return 0;
}
'''


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False, "checks": [],
              "scope": "alternate 32/64-bit multiply-negate combinations; no cost claim"}

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

    save()
    try:
        subprocess.run(["python3",str(ROOT/"perf/guard.py")],cwd=ROOT,check=True)
        deps = subprocess.check_output([str(ROOT/"tools/modorder"),".depend.extr",
            "lib/Camlcoq.cmx","extraction/SelectOp.cmx","extraction/SelectLong.cmx"],cwd=ROOT,text=True).split()
        includes = [arg for d in ["extraction","lib","common","aarch64","backend","cfrontend",
                                 "cparser","driver","export","debug"] for arg in ("-I",str(ROOT/d))]
        obj, native = ARTIFACTS/"test_select.cmx", ARTIFACTS/"check_select"
        with (ARTIFACTS/"build.log").open("w") as log:
            for command in [
                [ROOT/"perf/in-env","ocamlopt","-g",*includes,"-c",ROOT/"perf/test_select.ml","-o",obj],
                [ROOT/"perf/in-env","ocamlopt","-g",*includes,"-o",native,
                 "str.cmxa","unix.cmxa",*deps,obj],
            ]:
                subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
        source = ARTIFACTS/"negmul.c"
        source.write_text(SOURCE)
        clang = ARTIFACTS/"negmul.clang"
        subprocess.run(["clang","-O2",str(source),"-o",str(clang)],cwd=ROOT,check=True)
        reference = subprocess.check_output([str(clang)],env=env(""))
        check("reference covers all 81 edge-input pairs",len(reference.splitlines())==81)
        report["native"] = {}
        for name, flags in [("default",""),("enabled","arm64-combine")]:
            result = subprocess.run([str(native)],cwd=ROOT,env=env(flags),capture_output=True,text=True)
            (ARTIFACTS/(name+".stdout")).write_text(result.stdout)
            (ARTIFACTS/(name+".stderr")).write_text(result.stderr)
            result.check_returncode()
            actual = json.loads(result.stdout)
            check(name+" production constructor checks",actual["success"] and len(actual["checks"])==6)
            check(name+" gate state",actual["enabled"]==(name=="enabled"))
            report["native"][name]=actual
            asm, binary = ARTIFACTS/(name+".s"), ARTIFACTS/(name+".exe")
            command = [str(ROOT/"ccomp"),"-stdlib",str(ROOT/"runtime")]
            subprocess.run([*command,"-S",str(source),"-o",str(asm)],cwd=ROOT,env=env(flags),check=True)
            fused = bool(re.search(r"\b(?:msub|mneg)\s",asm.read_text()))
            check(name+" generated fused-family gate",fused==(name=="enabled"))
            subprocess.run([*command,str(source),"-o",str(binary)],cwd=ROOT,env=env(flags),check=True)
            output = subprocess.check_output([str(binary)],env=env(""))
            check(name+" exact defined unsigned outputs",output==reference)
        report["source_sha256"] = {name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
            ["aarch64/SelectOp.vp","aarch64/SelectOpproof.v","aarch64/SelectLong.vp",
             "aarch64/SelectLongproof.v","extraction/SelectOp.ml","extraction/SelectLong.ml",
             "perf/check_select.py","perf/test_select.ml"]}
        report["compiler_sha256"]=hashlib.sha256((ROOT/"ccomp").read_bytes()).hexdigest()
        report["success"]=True
        save()
        print(f"{len(report['checks'])} ARM64 selection checks passed; no instruction-count or speed claim")
    except Exception as error:
        report["success"]=False
        report["error"]=str(error)
        save()
        raise


if __name__ == "__main__":
    main()
