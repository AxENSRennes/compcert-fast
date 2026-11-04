#!/usr/bin/env python3
"""Exercise new loop passes on ordinary C, including automatically emitted NEON.

Compare defined outputs and inspect actual transformation counters/assembly.
No speed samples, ratios, or promotion decisions are produced.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
ARTIFACTS=ROOT/'perf/artifacts/loop-optimizations'
OUTPUT=ROOT/'perf/results/loop-optimizations.json'
SOURCE=r'''
#include <stdio.h>
extern unsigned touch(unsigned *, unsigned);
unsigned induction(unsigned n, unsigned k) {
  unsigned count, i=0, s=0;
  for(count=0; count<n; ++count) { s ^= i*k; i+=3u; }
  return s;
}
unsigned invariant(unsigned n, unsigned a, unsigned b) {
  unsigned i,s=0,cell=9u;
  for(i=0; i<n; ++i) { s ^= a*b; s += touch(&cell,i); }
  return s ^ cell;
}
unsigned preheader(unsigned n, unsigned a, unsigned b) {
  unsigned c=(a^b)+9u, d=(a+b)^0x12345u, i,s=0;
  for(i=0; i<n; ++i) s ^= c*d;
  return s;
}
unsigned preheader_load(unsigned n, const unsigned *p, unsigned b) {
  unsigned c=*p, i,s=0;
  for(i=0; i<n; ++i) s ^= c*b;
  return s;
}
unsigned branching_preheader(unsigned n, unsigned a, unsigned b) {
  unsigned c,d,i,s=0;
  if(a&1u) { c=a+b; d=a^9u; } else { c=a-b; d=a+17u; }
  for(i=0; i<n; ++i) s ^= c*d;
  return s;
}
unsigned lazy_division(unsigned n, unsigned a, unsigned b) {
  unsigned i,s=0;
  for(i=0;i<n;++i) s ^= a/b;
  return s;
}
unsigned auto_pair(unsigned x) { unsigned a=x+3u, b=x+7u; return a*b; }
unsigned auto_loop(unsigned n, unsigned x) {
  unsigned i,s=0;
  for(i=0; i<n; ++i) { unsigned t=x+i; s ^= (t+3u)*(t+7u); }
  return s;
}
double invariant_fp(unsigned n, double a, double b) {
  unsigned i; double s=0;
  for(i=0; i<n; ++i) s+=a*b;
  return s;
}
int main(void) {
  static const unsigned inputs[]={0u,1u,7u,0x7fffffffu,0x80000000u,0xffffffffu};
  unsigned i,j,n;
  for(n=0;n<19;++n) for(i=0;i<6;++i) for(j=0;j<6;++j)
    printf("%u %u %u %u %u %u %u %u %u %.17g\n",induction(n,inputs[j]),
           invariant(n,inputs[i],inputs[j]),preheader(n,inputs[i],inputs[j]),
           preheader_load(n,&inputs[i],inputs[j]),branching_preheader(n,inputs[i],inputs[j]),
           lazy_division(n,inputs[i],inputs[j]|1u),lazy_division(0,inputs[i],0),
           auto_pair(inputs[i]),auto_loop(n,inputs[i]),
           invariant_fp(n,(double)i/16.0,(double)j/8.0));
  return 0;
}
'''
HELPER='unsigned touch(unsigned *p, unsigned x) { *p = (*p * 17u) ^ x; return *p; }\n'


def main():
    ARTIFACTS.mkdir(parents=True,exist_ok=True)
    OUTPUT.parent.mkdir(parents=True,exist_ok=True)
    report={'success':False,'performance_measured':False,'profiles':{},'checks':[],'commands':[]}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(OUTPUT)

    def check(name,value):
        if not value:raise RuntimeError(name)
        report['checks'].append(name)

    def environment(flags,trace):
        env=os.environ.copy();env['COMPCERT_EXPERIMENTS']=flags
        env['COMPCERT_CONFIG']=str(ROOT/'compcert.ini');env['COMPCERT_EXPERIMENT_TRACE']=str(trace)
        return env

    def run(command,env,label):
        command=[str(x) for x in command];report['commands'].append(command)
        result=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,timeout=180)
        (ARTIFACTS/(label+'.stdout')).write_bytes(result.stdout)
        (ARTIFACTS/(label+'.stderr')).write_bytes(result.stderr)
        result.check_returncode();return result.stdout

    save()
    try:
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        source=ARTIFACTS/'loops.c';source.write_text(SOURCE)
        helper=ARTIFACTS/'helper.c';helper.write_text(HELPER)
        trace=ARTIFACTS/'unused.trace'
        reference=ARTIFACTS/'reference'
        run(['clang','-O2','-fno-inline',source,helper,'-o',reference],environment('',trace),'clang-build')
        expected=run([reference],environment('',trace),'clang-run')
        check('reference covers 684 boundary-input/trip-count combinations',len(expected.splitlines())==684)
        catalog=json.loads((ROOT/'perf/experiment-profiles.json').read_text())
        profiles=[('default',''),('licm','licm-pure'),('preheader','licm-preheader'),('strength','strength-reduce'),
                  ('peel','loop-peel'),('vector','auto-neon')]
        profiles.extend((name,flags) for name,flags in catalog['profiles'].items() if name.startswith('loops'))
        for name,flags in profiles:
            trace=ARTIFACTS/(name+'.jsonl');trace.unlink(missing_ok=True)
            env=environment(flags,trace)
            compiler=[ROOT/'ccomp','-stdlib',ROOT/'runtime','-fno-inline']
            asm=ARTIFACTS/(name+'.s');binary=ARTIFACTS/(name+'.exe')
            run([*compiler,'-S',source,'-o',asm],env,name+'-asm')
            run([*compiler,source,helper,'-o',binary],env,name+'-build')
            actual=run([binary],env,name+'-run')
            check(name+' exact defined C/FP outputs including zero trip',actual==expected)
            records=[json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            effects={}
            for item in records:
                key=item['pass']+':'+item['event'];effects[key]=effects.get(key,0)+item['count']
            if flags:
                for flag in flags.split(','):
                    check(name+' observes '+flag,any(item['pass']==flag for item in records))
            else:check('default emits no experiment trace',not records)
            assembly=asm.read_text()
            vectorized=bool(re.search(r'\badd\s+v16\.2s,\s*v16\.2s,\s*v17\.2s',assembly))
            if name=='vector':
                check('ordinary C automatically emits real NEON',vectorized)
                check('ordinary C requires no explicit intrinsic', '__builtin_cc_neon_' not in SOURCE)
                check('vectorizer creates a builtin in production RTL',effects.get('auto-neon:packed-builtins-after',0)>0)
                body=assembly.split('_auto_loop:',1)[1].split('.cfi_endproc',1)[0]
                check('NEON is emitted inside an ordinary C loop',bool(re.search(r'\badd\s+v16\.2s',body)))
            if name=='default':check('default scalar program contains no packed NEON',not vectorized)
            for flag in ['licm-pure','licm-preheader','strength-reduce','loop-peel']:
                if flags==flag:check(flag+' really changes production RTL',effects.get(flag+':changed-functions',0)>0)
            if name=='strength':
                check('strength reduction removes multiplications from RTL loops',
                      effects.get('strength-reduce:loop-multiplies-after',0)<effects.get('strength-reduce:loop-multiplies-before',0))
            report['profiles'][name]={'flags':flags,'success':True,'effects':effects,
                'stdout_sha256':hashlib.sha256(actual).hexdigest(),'neon_emitted':vectorized}
            save();print(name+': ordinary C outputs and transformation checks pass',flush=True)
        report['compiler_sha256']=hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        report['source_sha256']={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in
                                ['perf/check_loop_optimizations.py','perf/experiment-profiles.json']}
        report['success']=True;save()
    except BaseException as error:
        report.update(success=False,error=str(error));save();raise


if __name__=='__main__':main()
