#!/usr/bin/env python3
"""Check proved automatic correlated-input SLP and ordinary-C NEON emission.

No source intrinsics, speed measurement or promotion. This is a narrow SLP
pass; it does not combine memory accesses or vectorize across iterations.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
ARTIFACTS=ROOT/'perf/artifacts/vectorize'
OUTPUT=ROOT/'perf/results/vectorize.json'
SOURCE=r'''
#include <stdio.h>
unsigned affine(unsigned x) { unsigned a=x+3u, b=x+7u; return a*b; }
unsigned loop(unsigned seed, unsigned count) {
  unsigned i, sum=0;
  for(i=0; i<count; ++i) { unsigned t=seed+i; sum ^= (t+3u)*(t+7u); }
  return sum;
}
int main(void) {
  static const unsigned edges[]={0u,1u,2u,0x7fffffffu,0x80000000u,0xffffffffu};
  unsigned i, j, x=0x3f6a15c7u, hash=0;
  for(i=0; i<6; ++i) for(j=0; j<18; ++j)
    hash=hash*33u ^ affine(edges[i]) ^ loop(edges[i],j);
  for(i=0; i<10000; ++i) { x=x*1664525u+1013904223u; hash=hash*33u ^ affine(x) ^ loop(x,i%18u); }
  printf("%u\n",hash); return 0;
}
'''


def main():
    ARTIFACTS.mkdir(parents=True,exist_ok=True)
    OUTPUT.parent.mkdir(parents=True,exist_ok=True)
    result={'success':False,'performance_measured':False,'source_intrinsics_required':False,
        'scope':'one same-input adjacent 32-bit affine-operation pair per function; correlated-input SLP',
        'memory_loop_vectorization':False,'cross_iteration_vectorization':False,'commands':[],'checks':[]}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(result,indent=2)+'\n');temporary.replace(OUTPUT)

    def check(name,value):
        if not value:raise RuntimeError(name)
        result['checks'].append(name)

    def env(flags):
        environment=os.environ.copy();environment['COMPCERT_EXPERIMENTS']=flags
        environment['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
        environment.pop('COMPCERT_EXPERIMENT_TRACE',None)
        return environment

    def run(command,*,flags='',label):
        command=[str(item) for item in command];result['commands'].append(command)
        actual=subprocess.run(command,cwd=ROOT,env=env(flags),capture_output=True,timeout=180)
        (ARTIFACTS/(label+'.stdout')).write_bytes(actual.stdout)
        (ARTIFACTS/(label+'.stderr')).write_bytes(actual.stderr)
        actual.check_returncode();return actual.stdout

    save()
    try:
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        deps=subprocess.check_output([str(ROOT/'tools/modorder'),'.depend.extr','lib/Camlcoq.cmx',
            'extraction/Vectorize.cmx','extraction/LowerLong.cmx','extraction/Builtins.cmx',
            'extraction/Op.cmx'],cwd=ROOT,text=True).split()
        includes=[arg for directory in ['extraction','lib','common','aarch64','backend','cfrontend',
            'cparser','driver','export','debug'] for arg in ['-I',str(ROOT/directory)]]
        obj=ARTIFACTS/'test_vectorize.cmx';native=ARTIFACTS/'check_vectorize'
        run([ROOT/'perf/in-env','ocamlopt','-g',*includes,'-c',ROOT/'perf/test_vectorize.ml','-o',obj],label='native-compile')
        run([ROOT/'perf/in-env','ocamlopt','-g',*includes,'-o',native,'str.cmxa','unix.cmxa',*deps,obj],label='native-link')
        actual=json.loads(run([native],label='native-execute'))
        check('production-extracted semantic checks passed',actual['success'] and actual['semantic_cases']>=10000)
        result['native']=actual
        source=ARTIFACTS/'ordinary.c';source.write_text(SOURCE)
        check('ordinary C source contains no vector intrinsic or asm',
              '__builtin' not in SOURCE and 'asm' not in SOURCE and 'neon' not in SOURCE)
        reference=ARTIFACTS/'clang.exe'
        run(['clang','-O2',source,'-o',reference],label='clang-build')
        expected=run([reference],label='clang-execute')
        result['configurations']={}
        configurations=[('default','',[]),('automatic','auto-neon',[]),
            ('automatic-pic','auto-neon',['-fPIC']),('automatic-size','auto-neon',['-Os'])]
        profiles=json.loads((ROOT/'perf/experiment-profiles.json').read_text())['profiles']
        configurations += [(name,','.join(dict.fromkeys((flags+',auto-neon').split(','))),[]) for name,flags in profiles.items()]
        for name,flags,options in configurations:
            ccomp=[ROOT/'ccomp','-stdlib',ROOT/'runtime','-fno-inline',*options]
            asm=ARTIFACTS/(name+'.s');binary=ARTIFACTS/(name+'.exe')
            run([*ccomp,'-S',source,'-o',asm],flags=flags,label=name+'-assembly')
            text=asm.read_text()
            emitted=bool(re.search(r'\badd\s+v16\.2s,\s*v16\.2s,\s*v17\.2s',text))
            check(name+' automatic NEON code-generation gate',emitted==('auto-neon' in flags.split(',')))
            if 'auto-neon' in flags.split(','):
                for function in ['affine','loop']:
                    body=text.split('_'+function+':',1)[1].split('.cfi_endproc',1)[0]
                    check(name+' ordinary '+function+' function contains automatic NEON arithmetic',
                          bool(re.search(r'\badd\s+v16\.2s,\s*v16\.2s,\s*v17\.2s',body)))
            run([*ccomp,source,'-o',binary],flags=flags,label=name+'-build')
            check(name+' defined C outputs match clang',run([binary],label=name+'-execute')==expected)
            result['configurations'][name]={'flags':flags,'options':options,'neon_emitted':emitted,'correctness_pass':True}
        result['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
            ['backend/Vectorize.v','backend/Vectorizeproof.v','backend/LowerLong.v','backend/LowerLongproof.v',
             'perf/test_vectorize.ml','perf/check_vectorize.py',
             'perf/experiment-profiles.json']}
        result['compiler_sha256']=hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        result['success']=True;save()
        print(f"Automatic SLP: {actual['semantic_cases']} extracted semantic cases, ordinary-C NEON emission and defined outputs checked; no speed measurement")
    except BaseException as error:
        result.update(success=False,error=str(error));save();raise


if __name__=='__main__':
    main()
