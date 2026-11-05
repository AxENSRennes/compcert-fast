#!/usr/bin/env python3
"""Check local NEON in variable pointer loops, preserving scalar memory accesses."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / 'perf/artifacts/pointerneon'
OUTPUT = ROOT / 'perf/results/pointerneon.json'
TRUST_BASE = '57564e2c'
TRUSTED = ['aarch64/Asm.v', 'aarch64/Builtins1.v', 'aarch64/Asmexpand.ml',
           'aarch64/TargetPrinter.ml', 'aarch64/Machregs.v', 'aarch64/CBuiltins.ml',
           'common/Values.v', 'common/Memory.v', 'common/Memdata.v',
           'common/AST.v', 'common/Events.v', 'common/Builtins.v']
C_SOURCE = r'''
#include <stdio.h>
unsigned pointer_buffer[40];
void vector_ptr(unsigned *p,unsigned n) {
  unsigned i=0;
  for(;n-i>=2u;i+=2u) {
    unsigned x=p[i],y=p[i+1];
    if((int)x<(int)y) {
      unsigned a=x+3u,b=y+7u;
      p[i]=a;p[i+1]=b;
    }
  }
  if(i<n) p[i]+=3u;
}
void vector_down(unsigned *p,unsigned n) {
  while(n>=2u) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) {
      unsigned a=x+3u,b=y+7u;
      p[0]=a;p[1]=b;
    }
    p+=2;n-=2;
  }
  if(n) p[0]+=3u;
}
void vector_alias(unsigned *p,unsigned *q,unsigned n) {
  while(n>=2u) {
    unsigned x=p[0],y=q[0];
    if((int)x<(int)y) {
      unsigned a=x+3u,b=y+7u;
      p[0]=a;q[0]=b;
    }
    p+=2;q+=2;n-=2;
  }
  if(n) p[0]+=3u;
}
unsigned vector_live(unsigned *p,unsigned n) {
  unsigned sum=0;
  while(n>=2u) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) {
      unsigned a=x+3u,b=y+7u;
      p[0]=a;p[1]=b;sum^=a+b;
    }
    p+=2;n-=2;
  }
  if(n) { p[0]+=3u;sum^=p[0]; }
  return sum;
}
void pointer_unguarded(unsigned *p,unsigned n) {
  while(n>=2u) {
    unsigned x=p[0],y=p[1],a=x+3u,b=y+7u;
    p[0]=a;p[1]=b;p+=2;n-=2;
  }
  if(n) p[0]+=3u;
}
void pointer_volatile(volatile unsigned *p,unsigned n) {
  while(n>=2u) {
    unsigned x=p[0],y=p[1];
    if((int)x<(int)y) { p[0]=x+3u;p[1]=y+7u; }
    p+=2;n-=2;
  }
  if(n) p[0]+=3u;
}
static void pointer_reset(unsigned seed) {
  static const unsigned edge[]={0u,1u,2u,3u,0x7fffffffu,0x80000000u,
                                0xffffffffu,0xaaaaaaaau,0x55555555u};
  unsigned i,x=seed+1u;
  for(i=0;i<40u;++i) {
    x=x*1664525u+1013904223u;
    pointer_buffer[i]=edge[(seed+i)%9u]^x;
  }
}
static void pointer_print(unsigned result) {
  unsigned i;
  printf("%u",result);
  for(i=0;i<40u;++i) printf(" %u",pointer_buffer[i]);
  printf("\n");
}
int main(void) {
  unsigned n,offset,seed;
  for(n=0;n<34u;++n) for(offset=0;offset<4u;++offset) for(seed=0;seed<9u;++seed) {
    pointer_reset(seed);vector_ptr(pointer_buffer+offset,n);pointer_print(0u);
    pointer_reset(seed);vector_down(pointer_buffer+offset,n);pointer_print(0u);
    pointer_reset(seed);vector_alias(pointer_buffer+offset,pointer_buffer+offset,n);pointer_print(0u);
    pointer_reset(seed);vector_alias(pointer_buffer+offset,pointer_buffer+offset+1,n);pointer_print(0u);
    pointer_reset(seed);vector_alias(pointer_buffer+offset,pointer_buffer+offset+2,n);pointer_print(0u);
    pointer_reset(seed);pointer_print(vector_live(pointer_buffer+offset,n));
    pointer_reset(seed);pointer_unguarded(pointer_buffer+offset,n);pointer_print(0u);
    pointer_reset(seed);pointer_volatile(pointer_buffer+offset,n);pointer_print(0u);
  }
  vector_ptr((unsigned *)0,0u);vector_down((unsigned *)0,0u);
  vector_alias((unsigned *)0,(unsigned *)0,0u);
  pointer_unguarded((unsigned *)0,0u);pointer_volatile((volatile unsigned *)0,0u);
  printf("%u\n",vector_live((unsigned *)0,0u));
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

    def memory_sites(text):
        return [line.strip() for line in text.splitlines() if re.search(r'int(?:8|16|32|64)\[', line)]

    save()
    try:
        sources = ['backend/PointerNeon.v', 'backend/PointerNeonproof.v', 'backend/PointerNeonFacts.v',
                   'perf/test_pointerneon.ml', 'perf/check_pointerneon.py', 'perf/experiment-profiles.json']
        before = snapshot(sources)
        compiler_before = hashlib.sha256((ROOT / 'ccomp').read_bytes()).hexdigest()
        trusted_before = snapshot(TRUSTED)
        baseline = {name: hashlib.sha256(subprocess.check_output(
            ['git', 'show', TRUST_BASE + ':' + name], cwd=ROOT)).hexdigest() for name in TRUSTED}
        if trusted_before != baseline:
            raise RuntimeError('Existing trusted semantics or hardware expansion changed')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-before')
        deps = subprocess.check_output([str(ROOT / 'tools/modorder'), '.depend.extr',
                                       'lib/Camlcoq.cmx', 'extraction/PointerNeon.cmx',
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
        obj = ARTIFACTS / 'test_pointerneon.cmx'
        executable = ARTIFACTS / 'check_pointerneon'
        run([ROOT / 'perf/in-env', 'ocamlopt', '-g', *includes, '-c',
             ROOT / 'perf/test_pointerneon.ml', '-o', obj], 'native-compile')
        run([ROOT / 'perf/in-env', 'ocamlopt', '-g', *includes, '-o', executable,
             'str.cmxa', 'unix.cmxa', *[ROOT / dep for dep in deps], obj], 'native-link')
        env = os.environ.copy()
        env['COMPCERT_CONFIG'] = str(ROOT / 'compcert.ini')
        native = run([executable], 'native-run', env)
        report.update(json.loads(native))
        report['check_count'] = len(report['checks'])
        if report.get('success') is not True or not report['check_count']:
            raise RuntimeError('Extracted pointer NEON checker did not report success')
        report['success'] = False
        source = ARTIFACTS / 'pointer_neon.c'
        source.write_text(C_SOURCE)
        if '__builtin_cc_neon_' in C_SOURCE:
            raise RuntimeError('C fixture must not request a vector intrinsic')
        reference = ARTIFACTS / 'clang.exe'
        run(['clang', '-O2', '-fno-inline', source, '-o', reference], 'clang-build')
        expected = run([reference], 'clang-run')
        expected_lines = 34 * 4 * 9 * 8 + 1
        if len(expected.splitlines()) != expected_lines:
            raise RuntimeError('Incomplete pointer/count/tail C fixture')
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
            original = (ARTIFACTS / 'pointer_neon.rtl.50').read_text()
            vectorized = (ARTIFACTS / 'pointer_neon.rtl.78').read_text()
            lowered = (ARTIFACTS / 'pointer_neon.rtl.79').read_text()
            (ARTIFACTS / (name + '.rtl')).write_text(vectorized)
            (ARTIFACTS / (name + '.lowered.rtl')).write_text(lowered)
            run([*compiler, source, '-o', executable], name + '-build', environment)
            actual = run([executable], name + '-run', environment)
            if actual != expected:
                raise RuntimeError(name + ': pointer/count/tail C output differs from clang')
            records = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            effects = {}
            for record in records:
                key = record['pass'] + ':' + record['event']
                effects[key] = effects.get(key, 0) + record['count']
            if not flags and records:
                raise RuntimeError('Default compiler emitted experimental trace')
            if 'memory-neon' in flags.split(','):
                if effects.get('pointer-neon:changed-functions', 0) < 1:
                    raise RuntimeError('Local pointer NEON changes were not observed in production trace')
                for function in ['vector_ptr', 'vector_down', 'vector_alias']:
                    target_body = body(vectorized, function)
                    if '__builtin_cc_neon_add_u32x2' not in target_body:
                        raise RuntimeError(function + ': ordinary variable pointer loop was not vectorized')
                    if memory_sites(body(original, function)) != memory_sites(target_body):
                        raise RuntimeError(function + ': pointer pass changed scalar memory accesses or their order')
                    if 'int64[' in target_body:
                        raise RuntimeError(function + ': pointer pass introduced an unjustified wide memory access')
                    assembly_body = assembly.read_text().split('_' + function + ':', 1)[1].split('.cfi_endproc', 1)[0]
                    if not re.search(r'\badd\s+v16\.2s,\s*v16\.2s,\s*v17\.2s', assembly_body):
                        raise RuntimeError(function + ': variable pointer loop lacks actual NEON addition')
                    if 'makelong' in body(lowered, function) or 'highlong' in body(lowered, function):
                        raise RuntimeError(function + ': packing was not lowered before ARM64 allocation')
                if name == 'enabled':
                    for function in ['pointer_unguarded', 'pointer_volatile']:
                        if '__builtin_cc_neon_' in body(vectorized, function):
                            raise RuntimeError(function + ': unsupported local window was accepted')
            report['c_configurations'][name] = {'flags': flags, 'correctness_pass': True,
                'output_lines': expected_lines, 'stdout_sha256': hashlib.sha256(actual).hexdigest(),
                'trace_effects': effects}
            save()
        if snapshot(sources) != before or snapshot(extraction) != extraction_before:
            raise RuntimeError('Pointer NEON sources or extraction changed during verification')
        if snapshot(TRUSTED) != trusted_before or hashlib.sha256((ROOT / 'ccomp').read_bytes()).hexdigest() != compiler_before:
            raise RuntimeError('Compiler or trusted semantics changed during verification')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-after')
        report.update(success=True, compiler_sha256=compiler_before, source_sha256=before,
                      production_extraction_sha256=extraction_before, trusted_source_sha256=trusted_before,
                      trusted_baseline_commit=TRUST_BASE, trusted_semantics_unchanged=True,
                      verification_snapshot_unchanged=True, new_neon_semantics=False,
                      memory_access_policy='Retain scalar loads/stores and their order; no alignment-8 assumption.')
        save()
        print(f"{report['check_count']} pointer NEON controls and variable-loop C outputs pass; no speed series")
    except BaseException as error:
        report.update(success=False, error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
