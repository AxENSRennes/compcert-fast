#!/usr/bin/env python3
"""Check automatic pairs and scalar cleanup from a step-one C lookahead loop.

The scalar source already reads its neighbour: n iterations need n+1 cells.
This is not a new precondition introduced by the transformation. No timings.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / 'perf/artifacts/autopair'
OUTPUT = ROOT / 'perf/results/autopair.json'
TRUST_BASE = '57a2221d'
TRUSTED = ['aarch64/Asm.v', 'aarch64/Builtins1.v', 'aarch64/Asmexpand.ml',
           'aarch64/TargetPrinter.ml', 'aarch64/Machregs.v', 'aarch64/CBuiltins.ml',
           'common/Values.v', 'common/Memory.v', 'common/Memdata.v',
           'common/AST.v', 'common/Events.v', 'common/Builtins.v']
C_SOURCE = r'''
#include <stdio.h>
unsigned autopair_buffer[44];
/* n is a number of comparisons. This scalar source already reads n+1 cells. */
void scalar_lookahead(unsigned *p,unsigned n) {
  while(n) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) p[0]=x+3u;
    ++p;--n;
  }
}
void scalar_decrement(unsigned *p,unsigned n) {
  while(n) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) p[0]=x+0xffffffffu;
    ++p;--n;
  }
}
void scalar_for(unsigned *p,unsigned n) {
  for(;n;++p,--n) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) p[0]=x+3u;
  }
}
void scalar_unsigned_guard(unsigned *p,unsigned n) {
  while(n) {
    unsigned x=p[0],y=p[1];
    if(x<y) p[0]=x+3u;
    ++p;--n;
  }
}
void scalar_volatile(volatile unsigned *p,unsigned n) {
  while(n) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) p[0]=x+3u;
    ++p;--n;
  }
}
static void autopair_reset(unsigned seed) {
  static const unsigned edges[]={0u,1u,2u,3u,0x7fffffffu,0x80000000u,
                                0xffffffffu,0xaaaaaaaau,0x55555555u};
  unsigned i,x=seed+1u;
  for(i=0;i<44u;++i) {
    x=x*1664525u+1013904223u;
    autopair_buffer[i]=edges[(seed+i)%9u]^x;
  }
}
static void autopair_print(void) {
  unsigned i;
  for(i=0;i<44u;++i) printf("%u ",autopair_buffer[i]);
  printf("\n");
}
int main(void) {
  unsigned n,offset,seed;
  for(n=0;n<34u;++n) for(offset=0;offset<4u;++offset) for(seed=0;seed<9u;++seed) {
    autopair_reset(seed);scalar_lookahead(autopair_buffer+offset,n);autopair_print();
    autopair_reset(seed);scalar_decrement(autopair_buffer+offset,n);autopair_print();
    autopair_reset(seed);scalar_for(autopair_buffer+offset,n);autopair_print();
    autopair_reset(seed);scalar_unsigned_guard(autopair_buffer+offset,n);autopair_print();
    autopair_reset(seed);scalar_volatile(autopair_buffer+offset,n);autopair_print();
  }
  scalar_lookahead((unsigned *)0,0u);scalar_decrement((unsigned *)0,0u);
  scalar_for((unsigned *)0,0u);
  scalar_unsigned_guard((unsigned *)0,0u);scalar_volatile((volatile unsigned *)0,0u);
  printf("zero length does not dereference null\n");
  return 0;
}
'''


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {'success': False, 'performance_measured': False, 'commands': [], 'c_configurations': {}}

    def save():
        temporary = OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(OUTPUT)

    def snapshot(names):
        return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in names}

    def run(command, label, env=None):
        command = [str(item) for item in command]
        report['commands'].append(command)
        result = subprocess.run(command, cwd=ARTIFACTS, env=env, capture_output=True, timeout=180)
        (ARTIFACTS / (label + '.stdout')).write_bytes(result.stdout)
        (ARTIFACTS / (label + '.stderr')).write_bytes(result.stderr)
        result.check_returncode()
        return result.stdout

    def body(text, function):
        return text.split(function + '(', 1)[1].split('\n}\n', 1)[0]

    save()
    try:
        sources = sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'backend').glob('AutoPair*.v'))
        sources.extend(['perf/test_autopair.ml', 'perf/check_autopair.py', 'perf/experiment-profiles.json'])
        before = snapshot(sources)
        compiler_before = hashlib.sha256((ROOT / 'ccomp').read_bytes()).hexdigest()
        trusted_before = snapshot(TRUSTED)
        baseline = {name: hashlib.sha256(subprocess.check_output(
            ['git', 'show', TRUST_BASE + ':' + name], cwd=ROOT)).hexdigest() for name in TRUSTED}
        if trusted_before != baseline:
            raise RuntimeError('Existing trusted semantics or hardware expansion changed')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-before')
        deps = subprocess.check_output([str(ROOT / 'tools/modorder'), '.depend.extr',
                                       'lib/Camlcoq.cmx', 'extraction/AutoPair.cmx',
                                       'extraction/LowerLong.cmx'], cwd=ROOT, text=True).split()
        if 'lib/Camlcoq.cmx' not in deps:
            deps.append('lib/Camlcoq.cmx')
        extraction = sorted({str(Path(dep).with_suffix(suffix)) for dep in deps
                             for suffix in ('.ml', '.mli', '.cmx', '.cmi', '.o')
                             if (ROOT / Path(dep).with_suffix(suffix)).is_file()})
        extraction_before = snapshot(extraction)
        directories = ['extraction', 'lib', 'common', 'aarch64', 'backend',
                       'cfrontend', 'cparser', 'driver', 'export', 'debug']
        includes = [item for directory in directories for item in ['-I', str(ROOT / directory)]]
        obj = ARTIFACTS / 'test_autopair.cmx'
        executable = ARTIFACTS / 'check_autopair'
        run([ROOT / 'perf/in-env', 'ocamlopt', '-g', *includes, '-c',
             ROOT / 'perf/test_autopair.ml', '-o', obj], 'native-compile')
        run([ROOT / 'perf/in-env', 'ocamlopt', '-g', *includes, '-o', executable,
             'str.cmxa', 'unix.cmxa', *[ROOT / dep for dep in deps], obj], 'native-link')
        env = os.environ.copy()
        env['COMPCERT_CONFIG'] = str(ROOT / 'compcert.ini')
        native = run([executable], 'native-run', env)
        report.update(json.loads(native))
        report['check_count'] = len(report['checks'])
        if report.get('success') is not True or not report['check_count']:
            raise RuntimeError('Extracted automatic-pair checker did not report success')
        report['success'] = False
        source = ARTIFACTS / 'auto_pair.c'
        source.write_text(C_SOURCE)
        if '__builtin_cc_neon_' in C_SOURCE:
            raise RuntimeError('Scalar C fixture must not request a vector intrinsic')
        reference = ARTIFACTS / 'clang.exe'
        run(['clang', '-O2', '-fno-inline', source, '-o', reference], 'clang-build')
        expected = run([reference], 'clang-run')
        expected_lines = 34 * 4 * 9 * 5 + 1
        if len(expected.splitlines()) != expected_lines:
            raise RuntimeError('Incomplete scalar-loop input/count C fixture')
        catalog = json.loads((ROOT / 'perf/experiment-profiles.json').read_text())
        profiles = [('default', ''), ('enabled', 'memory-neon')]
        profiles.extend((name, flags) for name, flags in catalog['profiles'].items()
                        if 'memory-neon' in flags.split(','))
        for name, flags in profiles:
            trace = ARTIFACTS / (name + '.jsonl')
            trace.unlink(missing_ok=True)
            environment = os.environ.copy()
            environment.update(COMPCERT_CONFIG=str(ROOT / 'compcert.ini'), COMPCERT_EXPERIMENTS=flags,
                               COMPCERT_EXPERIMENT_TRACE=str(trace))
            compiler = [ROOT / 'ccomp', '-stdlib', ROOT / 'runtime', '-fno-inline']
            assembly = ARTIFACTS / (name + '.s')
            executable = ARTIFACTS / (name + '.exe')
            run([*compiler, '-drtl', '-S', source, '-o', assembly], name + '-assembly', environment)
            original = (ARTIFACTS / 'auto_pair.rtl.50').read_text()
            paired = (ARTIFACTS / 'auto_pair.rtl.80').read_text()
            lowered = (ARTIFACTS / 'auto_pair.rtl.79').read_text()
            (ARTIFACTS / (name + '.rtl')).write_text(paired)
            (ARTIFACTS / (name + '.lowered.rtl')).write_text(lowered)
            run([*compiler, source, '-o', executable], name + '-build', environment)
            actual = run([executable], name + '-run', environment)
            if actual != expected:
                raise RuntimeError(name + ': scalar-loop C output differs from clang')
            records = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            effects = {}
            for record in records:
                key = record['pass'] + ':' + record['event']
                effects[key] = effects.get(key, 0) + record['count']
            if not flags and records:
                raise RuntimeError('Default compiler emitted experimental trace')
            if 'memory-neon' in flags.split(','):
                if effects.get('auto-pairs:changed-functions', 0) < 1:
                    raise RuntimeError('Automatic pair formation was not observed in production trace')
                for function in ['scalar_lookahead', 'scalar_decrement', 'scalar_for']:
                    source_body = body(original, function)
                    target_body = body(paired, function)
                    if '__builtin_cc_neon_' in source_body:
                        raise RuntimeError(function + ': input was already vectorized')
                    if '__builtin_cc_neon_add_u32x2' not in target_body:
                        raise RuntimeError(function + ': scalar step-one source was not automatically paired')
                    if not re.search(r'>=u\s+2', target_body):
                        raise RuntimeError(function + ': target lacks the automatic two-iteration dispatch')
                    if 'int64[' in target_body:
                        raise RuntimeError(function + ': automatic pair introduced a wide memory access')
                    # The original scalar add remains available only in the cleanup loop.
                    increment = '-1' if function == 'scalar_decrement' else '3'
                    if len(re.findall(r'\bx6\s*=\s*x4\s*\+\s*' + increment + r'\s*$', target_body, re.M)) != 1:
                        raise RuntimeError(function + ': scalar increment is duplicated in the paired body')
                    assembly_body = assembly.read_text().split('_' + function + ':', 1)[1].split('.cfi_endproc', 1)[0]
                    if not re.search(r'\badd\s+v16\.2s,\s*v16\.2s,\s*v17\.2s', assembly_body):
                        raise RuntimeError(function + ': automatic pair lacks a real NEON instruction')
                    if 'makelong' in body(lowered, function) or 'highlong' in body(lowered, function):
                        raise RuntimeError(function + ': packing was not lowered before ARM64 allocation')
                if name == 'enabled':
                    for function in ['scalar_unsigned_guard', 'scalar_volatile']:
                        if '__builtin_cc_neon_' in body(paired, function):
                            raise RuntimeError(function + ': unsupported scalar loop was paired')
            report['c_configurations'][name] = {'flags': flags, 'correctness_pass': True,
                'output_lines': expected_lines, 'stdout_sha256': hashlib.sha256(actual).hexdigest(),
                'trace_effects': effects}
            save()
        if snapshot(sources) != before or snapshot(extraction) != extraction_before:
            raise RuntimeError('Automatic pair sources or extraction changed during verification')
        if snapshot(TRUSTED) != trusted_before or hashlib.sha256((ROOT / 'ccomp').read_bytes()).hexdigest() != compiler_before:
            raise RuntimeError('Compiler or trusted semantics changed during verification')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-after')
        report.update(success=True, compiler_sha256=compiler_before, source_sha256=before,
                      production_extraction_sha256=extraction_before, trusted_source_sha256=trusted_before,
                      trusted_baseline_commit=TRUST_BASE, trusted_semantics_unchanged=True,
                      verification_snapshot_unchanged=True, new_neon_semantics=False,
                      source_memory_requirement='The scalar lookahead already reads n+1 cells for n iterations.',
                      memory_access_policy='Retain original scalar read/write order and fault prefixes.')
        save()
        print(f"{report['check_count']} automatic-pair controls and scalar-loop C outputs pass; no speed series")
    except BaseException as error:
        report.update(success=False, error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
