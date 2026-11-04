#!/usr/bin/env python3
"""Check real cross-iteration store widening on ordinary C; no timing series."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / 'perf/artifacts/memory-loops'
OUTPUT = ROOT / 'perf/results/memory-loops.json'
SOURCE = r'''
#include <stdio.h>
unsigned output[4];
volatile unsigned observed[2];
void fill2(unsigned x) { unsigned i; for(i=0;i<2u;++i) output[i]=x; }
void fill4(unsigned x) { unsigned i; for(i=0;i<4u;++i) output[i]=x; }
void different(unsigned x) { unsigned i; for(i=0;i<2u;++i) output[i]=x+3u*i; }
void volatile2(unsigned x) { unsigned i; for(i=0;i<2u;++i) observed[i]=x; }
void pointer2(unsigned *p,unsigned x) { unsigned i; for(i=0;i<2u;++i) p[i]=x; }
void alias2(unsigned *p,const unsigned *q) { unsigned i; for(i=0;i<2u;++i) p[i]=q[i]; }
int main(void) {
  unsigned i,x=1u;
  for(i=0;i<1024u;++i) {
    x=x*1664525u+1013904223u;
    output[0]=11u;output[1]=13u;output[2]=17u;output[3]=19u;
    fill2(x); printf("%u %u %u %u\n",output[0],output[1],output[2],output[3]);
    fill4(x); printf("%u %u %u %u\n",output[0],output[1],output[2],output[3]);
    different(x); printf("%u %u\n",output[0],output[1]);
    volatile2(x); printf("%u %u\n",observed[0],observed[1]);
    pointer2(output+1,x); printf("%u %u %u %u\n",output[0],output[1],output[2],output[3]);
    alias2(output+1,output); printf("%u %u %u %u\n",output[0],output[1],output[2],output[3]);
  }
  return 0;
}
'''


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {'success': False, 'performance_measured': False, 'profiles': {}, 'checks': [], 'commands': []}

    def save():
        temporary = OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(OUTPUT)

    def check(name, value):
        if not value:
            raise RuntimeError(name)
        report['checks'].append(name)

    def run(command, name, env=None):
        command = [str(item) for item in command]
        report['commands'].append(command)
        result = subprocess.run(command, cwd=ARTIFACTS, env=env, capture_output=True, timeout=180)
        (ARTIFACTS / (name + '.stdout')).write_bytes(result.stdout)
        (ARTIFACTS / (name + '.stderr')).write_bytes(result.stderr)
        result.check_returncode()
        return result.stdout

    save()
    try:
        inputs = ['perf/check_memory_loops.py', 'perf/experiment-profiles.json',
                  'backend/MemVector.v', 'backend/MemVectorproof.v',
                  'backend/PeelTwo.v', 'backend/PeelTwoproof.v', 'ccomp']
        initial = {name: digest(ROOT / name) for name in inputs}
        run(['python3', ROOT / 'perf/guard.py'], 'guard-before')
        source = ARTIFACTS / 'memory.c'
        source.write_text(SOURCE)
        reference = ARTIFACTS / 'clang.exe'
        run(['clang', '-O2', '-fno-inline', source, '-o', reference], 'clang-build')
        expected = run([reference], 'clang-run')
        check('6144 output lines cover stores, guards, volatile and overlapping copies', len(expected.splitlines()) == 6144)
        profiles = [('default', ''), ('memory', 'memory-vector')]
        profiles.extend(json.loads((ROOT / 'perf/experiment-profiles.json').read_text())['profiles'].items())
        for name, flags in profiles:
            trace = ARTIFACTS / (name + '.jsonl')
            trace.unlink(missing_ok=True)
            env = os.environ.copy()
            env.update(COMPCERT_EXPERIMENTS=flags, COMPCERT_CONFIG=str(ROOT / 'compcert.ini'),
                       COMPCERT_EXPERIMENT_TRACE=str(trace))
            compiler = [ROOT / 'ccomp', '-stdlib', ROOT / 'runtime', '-fno-inline']
            assembly = ARTIFACTS / (name + '.s')
            executable = ARTIFACTS / (name + '.exe')
            run([*compiler, '-drtl', '-S', source, '-o', assembly], name + '-asm', env)
            rtl = ARTIFACTS / 'memory.rtl.74'
            archived = ARTIFACTS / (name + '.rtl')
            archived.write_bytes(rtl.read_bytes())
            run([*compiler, source, '-o', executable], name + '-build', env)
            actual = run([executable], name + '-run', env)
            check(name + ': exact defined C outputs', actual == expected)
            records = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            if not flags:
                check('default has no experimental trace', not records)
            effects = {}
            for record in records:
                key = record['pass'] + ':' + record['event']
                effects[key] = effects.get(key, 0) + record['count']
            if name == 'memory':
                body = archived.read_text().split('fill2(', 1)[1].split('\n}\n', 1)[0]
                check('two original loop iterations become one wide store', body.count('int64[') == 1 and 'int32[' not in body)
                check('widening changes production RTL', effects.get('memory-vector:changed-functions', 0) > 0)
                body_asm = assembly.read_text().split('_fill2:', 1)[1].split('.cfi_endproc', 1)[0]
                check('native fill2 emits a 64-bit store', bool(re.search(r'\bstr\s+x[0-9]+,', body_asm)))
                for function in ['different', 'volatile2', 'pointer2', 'alias2']:
                    body = archived.read_text().split(function + '(', 1)[1].split('\n}\n', 1)[0]
                    check(function + ': no unsupported wide memory rewrite', 'int64[' not in body)
            report['profiles'][name] = {'flags': flags, 'success': True, 'output_lines': 6144,
                'stdout_sha256': hashlib.sha256(actual).hexdigest(), 'effects': effects,
                'assembly_sha256': digest(assembly)}
            save()
            print(name + ': memory-loop outputs pass', flush=True)
        check('verification inputs unchanged', initial == {name: digest(ROOT / name) for name in inputs})
        run(['python3', ROOT / 'perf/guard.py'], 'guard-after')
        report['compiler_sha256'] = initial.pop('ccomp')
        report['source_sha256'] = initial
        report['scope'] = 'Correlated Mint32 store widening across peeled first two iterations; no general memory SIMD.'
        report['success'] = True
        save()
    except BaseException as error:
        report.update(success=False, error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
