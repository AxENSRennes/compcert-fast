#!/usr/bin/env python3
"""Native structural and differential checks of production induction strength reduction."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/strengthreduce"
OUTPUT = ROOT / "perf/results/strengthreduce.json"
C_SOURCE = r'''
#include <stdio.h>
unsigned products(unsigned start, unsigned k, unsigned n) {
  unsigned result=0;
  while(n) { result ^= start*k; start+=7u; --n; }
  return result;
}
int main(void) {
  unsigned i,k,n;
  for(i=0;i<9u;i++) for(k=0;k<9u;k++) for(n=0;n<17u;n++)
    printf("%u\n", products(i*0x7fffffffu,k*0x80000001u,n));
  return 0;
}
'''



def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    result = {"success": False, "performance_measured": False, "commands": []}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(result, indent=2)+'\n')
        temporary.replace(OUTPUT)

    save()
    try:
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        deps=subprocess.check_output([str(ROOT/'tools/modorder'),'.depend.extr',
                                      'extraction/StrengthReduce.cmx'],
                                     cwd=ROOT,text=True).split()
        if 'lib/Camlcoq.cmx' not in deps:
            deps.append('lib/Camlcoq.cmx')
        dirs=['extraction','lib','common','aarch64','backend','cfrontend','cparser','driver','export','debug']
        includes=[arg for directory in dirs for arg in ['-I',str(ROOT/directory)]]
        obj=ARTIFACTS/'test_strengthreduce.cmx'; binary=ARTIFACTS/'check_strengthreduce'
        commands=[
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-c',str(ROOT/'perf/test_strengthreduce.ml'),'-o',str(obj)],
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-o',str(binary),'str.cmxa','unix.cmxa',*deps,str(obj)],
        ]
        with (ARTIFACTS/'build.log').open('w') as log:
            for command in commands:
                result['commands'].append(command)
                subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
        env=os.environ.copy();env['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
        native=subprocess.run([str(binary)],cwd=ROOT,env=env,text=True,capture_output=True)
        (ARTIFACTS/'native.stdout').write_text(native.stdout)
        (ARTIFACTS/'native.stderr').write_text(native.stderr)
        native.check_returncode()
        result.update(json.loads(native.stdout))
        result['check_count']=len(result['checks'])
        source=ARTIFACTS/'loop.c'; source.write_text(C_SOURCE)
        clang=ARTIFACTS/'loop.clang'
        subprocess.run(['clang','-O2',str(source),'-o',str(clang)],cwd=ROOT,check=True)
        reference=subprocess.check_output([str(clang)],cwd=ROOT)
        if len(reference.splitlines()) != 1377:
            raise RuntimeError('Incomplete unsigned C reference')
        result['c_configurations']={}
        for name,flags in [('default',''),('enabled','strength-reduce')]:
            trace=ARTIFACTS/(name+'.trace.jsonl'); trace.unlink(missing_ok=True)
            environment=os.environ.copy()
            environment['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
            environment['COMPCERT_EXPERIMENTS']=flags
            environment['COMPCERT_EXPERIMENT_TRACE']=str(trace)
            executable=ARTIFACTS/(name+'.exe')
            command=[str(ROOT/'ccomp'),'-stdlib',str(ROOT/'runtime'),str(source),'-o',str(executable)]
            result['commands'].append(command)
            subprocess.run(command,cwd=ROOT,env=environment,check=True)
            output=subprocess.check_output([str(executable)],cwd=ROOT)
            if output!=reference:
                raise RuntimeError(name+' unsigned C output mismatch')
            records=[json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            if flags:
                count=lambda event:sum(r['count'] for r in records if r['pass']==flags and r['event']==event)
                if count('changed-functions')<1 or count('loop-multiplies-after')>=count('loop-multiplies-before'):
                    raise RuntimeError('C integration did not actually remove a loop multiplication')
            elif records:
                raise RuntimeError('Default compiler emitted experiment trace')
            result['c_configurations'][name]={'correctness_pass':True,'outputs':1377,
                'stdout_sha256':hashlib.sha256(output).hexdigest(),'trace':records}
        result['compiler_sha256']=hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        result['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
                                ['backend/StrengthReduce.v','backend/StrengthReduceproof.v',
                                 'perf/test_strengthreduce.ml','perf/check_strengthreduce.py']}
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native strengthreduce checker did not report success')
        save()
        print(f"{result['check_count']} extracted induction-strength-reduction checks passed; no speed series")
    except BaseException as error:
        result['success']=False;result['error']=str(error);save();raise


if __name__=='__main__':
    main()
