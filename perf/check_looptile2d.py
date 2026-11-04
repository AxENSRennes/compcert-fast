#!/usr/bin/env python3
"""Native structural and differential checks of production pure two-dimensional rectangular loop tiling."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/looptile2d"
OUTPUT = ROOT / "perf/results/looptile2d.json"
C_SOURCE = r'''
#include <stdio.h>
unsigned rect(unsigned x,unsigned y,unsigned a,unsigned b) {
  unsigned i,j;
  for(i=0;i<2u;++i) for(j=0;j<3u;++j)
    if(i==0u) a=a*x+j; else b=b*y+j;
  return a^b;
}
int main(void) {
  unsigned x,y,a,b;
  for(x=0;x<5;++x) for(y=0;y<5;++y) for(a=0;a<5;++a) for(b=0;b<5;++b)
    printf("%u\n",rect(x*0x80000001u,y*0x7fffffffu,a*17u,b*23u));
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

    sources = ['backend/LoopTile2D.v', 'backend/LoopTile2Dproof.v', 'perf/test_looptile2d.ml', 'perf/check_looptile2d.py', 'backend/LoopFusion.v', 'backend/LoopFusionproof.v', 'backend/LoopInterchange.v', 'backend/LoopInterchangeproof.v']

    def snapshot(names):
        return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                for name in names}

    save()
    try:
        initial_sources = snapshot(sources)
        initial_compiler = hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        deps=subprocess.check_output([str(ROOT/'tools/modorder'),'.depend.extr',
                                      'extraction/LoopTile2D.cmx'],
                                     cwd=ROOT,text=True).split()
        if 'lib/Camlcoq.cmx' not in deps:
            deps.append('lib/Camlcoq.cmx')
        extraction = sorted({str(Path(dep).with_suffix(suffix))
                             for dep in deps
                             for suffix in ('.ml', '.mli', '.cmx', '.cmi', '.o')
                             if (ROOT/Path(dep).with_suffix(suffix)).is_file()})
        initial_extraction = snapshot(extraction)
        result['source_sha256'] = initial_sources
        result['production_extraction_sha256'] = initial_extraction
        result['compiler_sha256'] = initial_compiler
        save()
        dirs=['extraction','lib','common','aarch64','backend','cfrontend','cparser','driver','export','debug']
        includes=[arg for directory in dirs for arg in ['-I',str(ROOT/directory)]]
        obj=ARTIFACTS/'test_looptile2d.cmx'; binary=ARTIFACTS/'check_looptile2d'
        commands=[
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-c',str(ROOT/'perf/test_looptile2d.ml'),'-o',str(obj)],
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
        if len(reference.splitlines()) != 625:
            raise RuntimeError('Incomplete unsigned C reference')
        result['c_configurations']={}
        for name,flags in [('default',''),('enabled','loop-tile2d')]:
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
                if count('changed-functions')<1:
                    raise RuntimeError('C integration did not actually change the coordinate order through 2D tiles')
            elif records:
                raise RuntimeError('Default compiler emitted experiment trace')
            result['c_configurations'][name]={'correctness_pass':True,'outputs':625,
                'stdout_sha256':hashlib.sha256(output).hexdigest(),'trace':records}
        if snapshot(sources) != initial_sources:
            raise RuntimeError('Loop transformation sources changed during verification')
        if snapshot(extraction) != initial_extraction:
            raise RuntimeError('Production extraction changed during verification')
        if hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest() != initial_compiler:
            raise RuntimeError('Production compiler changed during verification')
        subprocess.run(['python3', str(ROOT/'perf/guard.py')], cwd=ROOT, check=True)
        result['verification_snapshot_unchanged'] = True
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native looptile2d checker did not report success')
        save()
        print(f"{result['check_count']} extracted pure-rectangular-2D-tiling checks passed; no speed series")
    except BaseException as error:
        result['success']=False;result['error']=str(error);save();raise


if __name__=='__main__':
    main()
