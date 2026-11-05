#!/usr/bin/env python3
"""Check production two-lane memory NEON and ordinary C correctness, without timing."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / 'perf/artifacts/memoryneon'
OUTPUT = ROOT / 'perf/results/memoryneon.json'
TRUST_BASE = '7bb08b94'
TRUSTED = ['aarch64/Asm.v', 'aarch64/Builtins1.v', 'aarch64/Asmexpand.ml',
           'aarch64/TargetPrinter.ml', 'aarch64/Machregs.v', 'aarch64/CBuiltins.ml',
           'common/Values.v', 'common/Memory.v', 'common/Memdata.v',
           'common/AST.v', 'common/Events.v', 'common/Builtins.v']
C_SOURCE = r'''
#include <stdio.h>
unsigned a[4];
volatile unsigned observed_neon[2];
void guarded_pair(void) {
  unsigned x=a[0],y=a[1],i;
  if ((int)x < (int)y) for(i=0;i<2u;++i) a[i]+=3u+4u*i;
}
void guarded_same(void) {
  unsigned x=a[0],y=a[1],i;
  if ((int)x < (int)y) for(i=0;i<2u;++i) a[i]+=3u;
}
void explicit_pair(void) {
  unsigned x=a[0],y=a[1];
  if ((int)x < (int)y) { a[0]=x+3u; a[1]=y+7u; }
}
void no_guard(void) { unsigned i; for(i=0;i<2u;++i) a[i]+=3u+4u*i; }
void volatile_pair(void) {
  unsigned x=observed_neon[0],y=observed_neon[1],i;
  if ((int)x < (int)y) for(i=0;i<2u;++i) observed_neon[i]+=3u+4u*i;
}
void pointer_pair(unsigned *p) {
  unsigned x=p[0],y=p[1],i;
  if ((int)x < (int)y) for(i=0;i<2u;++i) p[i]+=3u+4u*i;
}
void zero_trip(unsigned n) {
  unsigned x=a[0],y=a[1],i;
  if ((int)x < (int)y) for(i=0;i<n;++i) a[i]+=3u+4u*i;
}
static void reset_neon(unsigned x,unsigned y) {
  a[0]=x;a[1]=y;a[2]=0x13579bdfu;a[3]=0x2468ace0u;
  observed_neon[0]=x;observed_neon[1]=y;
}
static void print_neon(void) {
  printf("%u %u %u %u %u %u\n",a[0],a[1],a[2],a[3],observed_neon[0],observed_neon[1]);
}
static void one_neon_case(unsigned x,unsigned y) {
  reset_neon(x,y);guarded_pair();print_neon();
  reset_neon(x,y);guarded_same();print_neon();
  reset_neon(x,y);explicit_pair();print_neon();
  reset_neon(x,y);no_guard();print_neon();
  reset_neon(x,y);volatile_pair();print_neon();
  reset_neon(x,y);pointer_pair(a+1);print_neon();
  reset_neon(x,y);zero_trip(0u);print_neon();
}
int main(void) {
  static const unsigned edges[]={0u,1u,2u,3u,0x7fffffffu,0x80000000u,
                               0xffffffffu,0xaaaaaaaau,0x55555555u};
  unsigned i,j,x=1u,y=0x87654321u;
  for(i=0;i<9u;++i) for(j=0;j<9u;++j) one_neon_case(edges[i],edges[j]);
  for(i=0;i<1024u;++i) {
    x=x*1664525u+1013904223u;y=y*22695477u+1u;one_neon_case(x,y);
  }
  return 0;
}
'''


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    result = {'success': False, 'performance_measured': False, 'commands': [], 'c_configurations': {}}

    def save():
        temporary = OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(result, indent=2) + '\n')
        temporary.replace(OUTPUT)

    def snapshot(names):
        return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in names}

    def run(command, label, env=None, timeout=180):
        command = [str(item) for item in command]
        result['commands'].append(command)
        actual = subprocess.run(command, cwd=ARTIFACTS, env=env, capture_output=True, timeout=timeout)
        (ARTIFACTS / (label + '.stdout')).write_bytes(actual.stdout)
        (ARTIFACTS / (label + '.stderr')).write_bytes(actual.stderr)
        actual.check_returncode()
        return actual.stdout

    def body(text, function):
        return text.split(function + '(', 1)[1].split('\n}\n', 1)[0]

    save()
    try:
        sources = ['backend/MemoryNeon.v', 'backend/MemoryNeonproof.v', 'backend/MemoryNeonReplay.v',
                   'backend/MemoryLaneFacts.v', 'backend/MemoryNeonBounds.v',
                   'perf/test_memoryneon.ml', 'perf/check_memoryneon.py', 'perf/experiment-profiles.json']
        initial_sources = snapshot(sources)
        initial_compiler = hashlib.sha256((ROOT / 'ccomp').read_bytes()).hexdigest()
        initial_trusted = snapshot(TRUSTED)
        baseline_trusted = {name: hashlib.sha256(subprocess.check_output(
            ['git', 'show', TRUST_BASE + ':' + name], cwd=ROOT)).hexdigest() for name in TRUSTED}
        if initial_trusted != baseline_trusted:
            raise RuntimeError('Existing trusted semantics or NEON expansion changed')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-before')
        deps = subprocess.check_output([str(ROOT / 'tools/modorder'), '.depend.extr',
                                      'lib/Camlcoq.cmx', 'extraction/MemoryNeon.cmx'], cwd=ROOT, text=True).split()
        if 'lib/Camlcoq.cmx' not in deps:
            deps.append('lib/Camlcoq.cmx')
        extraction = sorted({str(Path(dep).with_suffix(suffix)) for dep in deps
                             for suffix in ('.ml', '.mli', '.cmx', '.cmi', '.o')
                             if (ROOT / Path(dep).with_suffix(suffix)).is_file()})
        initial_extraction = snapshot(extraction)
        directories = ['extraction', 'lib', 'common', 'aarch64', 'backend',
                       'cfrontend', 'cparser', 'driver', 'export', 'debug']
        includes = [item for directory in directories for item in ['-I', str(ROOT / directory)]]
        obj = ARTIFACTS / 'test_memoryneon.cmx'
        binary = ARTIFACTS / 'check_memoryneon'
        run([ROOT / 'perf/in-env', 'ocamlopt', '-g', *includes, '-c',
             ROOT / 'perf/test_memoryneon.ml', '-o', obj], 'native-compile')
        run([ROOT / 'perf/in-env', 'ocamlopt', '-g', *includes, '-o', binary,
             'str.cmxa', 'unix.cmxa', *[ROOT / dep for dep in deps], obj], 'native-link')
        env = os.environ.copy()
        env['COMPCERT_CONFIG'] = str(ROOT / 'compcert.ini')
        native = run([binary], 'native-run', env)
        result.update(json.loads(native))
        result['check_count'] = len(result['checks'])
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native memory NEON checks did not report success')
        # Native completion alone does not mark the aggregate C check complete.
        result['success'] = False
        source = ARTIFACTS / 'memory_neon.c'
        source.write_text(C_SOURCE)
        if '__builtin_cc_neon_' in C_SOURCE:
            raise RuntimeError('Ordinary C integration fixture must not request an intrinsic')
        reference = ARTIFACTS / 'clang.exe'
        run(['clang', '-O2', '-fno-inline', source, '-o', reference], 'clang-build')
        expected = run([reference], 'clang-run')
        if len(expected.splitlines()) != 7735:
            raise RuntimeError('Incomplete independent-lane C fixture')
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
            rtl = (ARTIFACTS / 'memory_neon.rtl.76').read_text()
            (ARTIFACTS / (name + '.rtl')).write_text(rtl)
            run([*compiler, source, '-o', executable], name + '-build', environment)
            actual = run([executable], name + '-run', environment)
            if actual != expected:
                raise RuntimeError(name + ': ordinary C output differs from clang -O2')
            records = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            effects = {}
            for record in records:
                key = record['pass'] + ':' + record['event']
                effects[key] = effects.get(key, 0) + record['count']
            if not flags and records:
                raise RuntimeError('Default compiler emitted experiment trace')
            if 'memory-neon' in flags.split(','):
                function = body(rtl, 'guarded_pair')
                if (not re.search(r'= int64\[', function)
                        or not re.search(r'int64\[[^\n]*\] =', function)
                        or '__builtin_cc_neon_add_u32x2' not in function):
                    raise RuntimeError('Ordinary two-iteration C loop did not produce wide memory NEON RTL')
                assembly_body = assembly.read_text().split('_guarded_pair:', 1)[1].split('.cfi_endproc', 1)[0]
                if not re.search(r'\badd\s+v16\.2s,\s*v16\.2s,\s*v17\.2s', assembly_body):
                    raise RuntimeError('Ordinary memory loop did not emit a real NEON addition')
                if not re.search(r'\bldr\s+x[0-9]+,', assembly_body) or not re.search(r'\bstr\s+x[0-9]+,', assembly_body):
                    raise RuntimeError('Memory NEON output lacks native wide load/store')
                if effects.get('memory-neon:changed-functions', 0) < 1:
                    raise RuntimeError('Memory NEON transformation was not observed in production trace')
                if name == 'enabled':
                    for function in ['no_guard', 'volatile_pair', 'pointer_pair', 'zero_trip']:
                        if '__builtin_cc_neon_' in body(rtl, function):
                            raise RuntimeError(function + ': unsupported memory region was vectorized')
            result['c_configurations'][name] = {'flags': flags, 'correctness_pass': True, 'output_lines': 7735,
                'stdout_sha256': hashlib.sha256(actual).hexdigest(), 'trace_effects': effects}
            save()
        if snapshot(sources) != initial_sources or snapshot(extraction) != initial_extraction:
            raise RuntimeError('Memory NEON sources or extraction changed during verification')
        if snapshot(TRUSTED) != initial_trusted:
            raise RuntimeError('Trusted semantics changed during verification')
        if hashlib.sha256((ROOT / 'ccomp').read_bytes()).hexdigest() != initial_compiler:
            raise RuntimeError('Compiler changed during verification')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-after')
        result.update(success=True, compiler_sha256=initial_compiler, source_sha256=initial_sources,
                      production_extraction_sha256=initial_extraction,
                      trusted_source_sha256=initial_trusted, trusted_baseline_commit=TRUST_BASE,
                      trusted_semantics_unchanged=True, verification_snapshot_unchanged=True,
                      new_neon_semantics=False)
        save()
        print(f"{result['check_count']} memory NEON controls and ordinary C outputs pass; no speed series")
    except BaseException as error:
        result.update(success=False, error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
