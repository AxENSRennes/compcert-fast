#!/usr/bin/env python3
"""Native structural and differential checks of production constant hoisting."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/hoist"
OUTPUT = ROOT / "perf/results/hoist.json"


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
                                      'lib/Camlcoq.cmx','extraction/HoistConst.cmx'],
                                     cwd=ROOT,text=True).split()
        dirs=['extraction','lib','common','aarch64','backend','cfrontend','cparser','driver','export','debug']
        includes=[arg for directory in dirs for arg in ['-I',str(ROOT/directory)]]
        obj=ARTIFACTS/'test_hoist.cmx'; binary=ARTIFACTS/'check_hoist'
        commands=[
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-c',str(ROOT/'perf/test_hoist.ml'),'-o',str(obj)],
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
        # This large constant-heavy function exposed repeated candidate
        # discovery inside the executable instruction map. A generous compile
        # timeout guards that regression; generated-code speed is not timed.
        command=[str(ROOT/'ccomp'),'-stdlib',str(ROOT/'runtime'),'-fstruct-passing',
                 '-c',str(ROOT/'test/spass/flags.c'),'-o',str(ARTIFACTS/'flags.o')]
        environment=os.environ.copy()
        environment['COMPCERT_EXPERIMENTS']='hoist-constant'
        environment['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
        environment.pop('COMPCERT_EXPERIMENT_TRACE',None)
        result['commands'].append(command)
        with (ARTIFACTS/'large-function.log').open('w') as log:
            subprocess.run(command,cwd=ROOT,env=environment,stdout=log,stderr=subprocess.STDOUT,
                           check=True,timeout=60)
        result['large_constant_function_compiles']=True
        result['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
                                ['backend/HoistConst.v','backend/HoistConstproof.v',
                                 'perf/test_hoist.ml','perf/check_hoist.py']}
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native constant-hoisting checker did not report success')
        save()
        print(f"{result['check_count']} extracted constant-hoisting checks passed; no speed series")
    except BaseException as error:
        result['success']=False;result['error']=str(error);save();raise


if __name__=='__main__':
    main()
