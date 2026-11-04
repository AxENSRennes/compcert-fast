#!/usr/bin/env python3
"""Differential C execution for independent and combined experimental options.

Only deterministic correctness execution; no timing, sampling or promotion.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/experiments"
OUTPUT = ROOT / "perf/results/experiments.json"
SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
extern unsigned mix(unsigned, unsigned);
unsigned recur(unsigned n) { return n ? recur(n-1) + n*17u : 9u; }
unsigned duplicate_load(const unsigned *p) { unsigned x=*p, y=*p; return x+y; }
unsigned overwritten_store(unsigned *p, unsigned x, unsigned y) { *p=x; *p=y; return *p; }
unsigned compute(unsigned seed, unsigned flag) {
  unsigned a[81], b[81], i, j, s = seed;
  unsigned long long wide = 0xfeedface12345678ULL ^ seed;
  for(i=0; i<81; ++i) { a[i] = mix(seed+i, i+1u); b[i]=0u; }
  for(i=0; i<80; ++i) {
    unsigned x=a[i], y=a[i+1];
    if(flag) s += -(x*y); else s ^= x + 7u;
    b[i] = (x ^ y) + (x / (y | 1u));
    wide = wide*6364136223846793005ULL + x;
  }
  for(i=0; i<8; ++i)
    for(j=0; j<8; ++j) s += a[i*8+j] * b[j*8+i];
  /* Defined overlapping accesses, loop-carried dependence, and zero trip. */
  for(i=1; i<81; ++i) a[i]=a[i-1]+b[i-1];
  for(i=0; i<(seed&15u); ++i) s = (s<<1) ^ (s>>31) ^ a[i];
  s += (unsigned)wide ^ (unsigned)(wide>>32) ^ recur(seed%8u);
  s ^= duplicate_load(a);
  s += overwritten_store(&a[80], seed, s);
  return s ^ a[80];
}
int main(int argc, char **argv) {
  unsigned seed = argc>1 ? (unsigned)strtoul(argv[1], 0, 0) : 0u;
  unsigned i, h=0u;
  for(i=0; i<97; ++i) h = h*33u ^ compute(seed+i, i&1u);
  printf("%u\n", h);
  return 0;
}
'''
HELPER = r'''
unsigned mix(unsigned x, unsigned y) {
  x ^= y*0x9e3779b9u; x ^= x>>16; x *= 0x85ebca6bu;
  return x ^ (x>>13);
}
'''


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {"success": False, "performance_measured": False, "profiles": {}, "commands": []}

    def save():
        temporary = OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2)+'\n')
        temporary.replace(OUTPUT)

    def env(flags, trace):
        result=os.environ.copy()
        result['COMPCERT_EXPERIMENTS']=flags
        result['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
        result['COMPCERT_EXPERIMENT_TRACE']=str(trace)
        return result

    def run(command, environment, label):
        command=[str(x) for x in command]
        report['commands'].append(command)
        result=subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, timeout=180)
        (ARTIFACTS/(label+'.stdout')).write_bytes(result.stdout)
        (ARTIFACTS/(label+'.stderr')).write_bytes(result.stderr)
        result.check_returncode()
        return result.stdout

    save()
    try:
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        source=ARTIFACTS/'program.c';source.write_text(SOURCE)
        helper=ARTIFACTS/'helper.c';helper.write_text(HELPER)
        reference=ARTIFACTS/'clang'
        run(['clang','-O2',source,helper,'-o',reference],env('',ARTIFACTS/'unused'), 'clang-build')
        inputs=['0','1','2','7','15','16','31','2147483647','2147483648','4294967295']
        expected=[run([reference,n],env('',ARTIFACTS/'unused'),'clang-'+n) for n in inputs]
        manifest=json.loads((ROOT/'perf/experiment-profiles.json').read_text())
        single_flags=manifest['profiles']['scalar2'].split(',')+['rtl-unroll4']
        profiles=[('default','',[])]+[(flag,flag,[]) for flag in single_flags]
        profiles += [(name, flags, []) for name,flags in manifest['profiles'].items()]
        profiles += [('scalar2-pic',manifest['profiles']['scalar2'],['-fPIC']),
                     ('scalar4-size',manifest['profiles']['scalar4'],['-Os']),
                     ('scalar2-minimal',manifest['profiles']['scalar2'],
                      ['-fno-inline','-fno-cse','-fno-redundancy','-fno-const-prop'])]
        for name,flags,options in profiles:
            trace=ARTIFACTS/(name+'.trace.jsonl');trace.unlink(missing_ok=True)
            environment=env(flags,trace)
            compiler=[ROOT/'ccomp','-stdlib',ROOT/'runtime',*options]
            objects=[]
            # Separate translation units exercise linking as well as the pass composition.
            for unit in [source,helper]:
                obj=ARTIFACTS/(name+'-'+unit.stem+'.o');objects.append(obj)
                run([*compiler,'-c',unit,'-o',obj],environment,name+'-build-'+unit.stem)
            binary=ARTIFACTS/(name+'.exe')
            run([*compiler,*objects,'-o',binary],environment,name+'-link')
            actual=[run([binary,n],environment,name+'-'+n) for n in inputs]
            if actual != expected:
                raise RuntimeError('Incorrect defined C output: '+name)
            records=[json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            if not flags and records:
                raise RuntimeError('Default configuration emitted experiment events')
            if flags and not set(flags.split(',')).issubset({r['pass'] for r in records}):
                raise RuntimeError('An enabled experiment was not observable: '+name)
            effects={}
            for record in records:
                key=record['pass']+':'+record['event']
                effects[key]=effects.get(key,0)+record['count']
            if name=='scalar2-minimal':
                for flag in ['hoist-constant','schedule-pure','load-forward','store-elim',
                             'loop-unswitch','rtl-unroll2','memory-cleanup']:
                    if effects.get(flag+':changed-functions',0)<1:
                        raise RuntimeError('C fixture did not exercise an actual '+flag+' transformation')
            report['profiles'][name]={'flags':flags,'options':options,'correctness_pass':True,
                'executions':len(inputs),'stdout_sha256':hashlib.sha256(b''.join(actual)).hexdigest(),
                'effects':effects}
            save()
            print(name+': defined outputs match clang -O2',flush=True)
        report['source_sha256']={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in
            ['perf/check_experiments.py','perf/experiment-profiles.json']}
        report['compiler_sha256']=hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        # The fixed public suite keeps its original inputs and expected outputs.
        # Run once per compiler: these are correctness checks, not timing series.
        report['frozen_suite']={}
        for name,flags in manifest['profiles'].items():
            output=ROOT/('perf/results/correctness-'+name+'.json')
            run(['python3', ROOT/'perf/bench.py','--correctness-only','--output',output],
                env(flags,ARTIFACTS/(name+'-suite.trace.jsonl')),name+'-suite')
            suite=json.loads(output.read_text())
            if not suite.get('correctness_pass') or suite.get('performance_measured') is not False:
                raise RuntimeError('Fixed-suite correctness incomplete: '+name)
            report['frozen_suite'][name]={'correctness_pass':True,'cases':len(suite['benchmarks'])}
            save()
        report['success']=True;save()
        print(f"{len(profiles)} profiles, {len(profiles)*len(inputs)} executions; no speed measurements")
    except BaseException as error:
        report.update(success=False,error=str(error));save();raise


if __name__=='__main__':
    main()
