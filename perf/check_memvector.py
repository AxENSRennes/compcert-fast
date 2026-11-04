#!/usr/bin/env python3
"""Native structural and differential checks of production correlated-lane store widening."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/memvector"
OUTPUT = ROOT / "perf/results/memvector.json"


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    result = {"success": False, "performance_measured": False, "commands": []}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(result, indent=2)+'\n')
        temporary.replace(OUTPUT)

    sources = ['backend/MemVector.v', 'backend/MemVectorproof.v',
               'perf/test_memvector.ml', 'perf/check_memvector.py']
    extraction = ['extraction/MemVector.ml', 'extraction/MemVector.cmx',
                  'extraction/LowerLong.ml', 'extraction/LowerLong.cmx']
    save()
    try:
        initial_sources = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                           for name in sources}
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        initial_extraction = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                              for name in extraction}
        deps=subprocess.check_output([str(ROOT/'tools/modorder'),'.depend.extr',
                                      'lib/Camlcoq.cmx','extraction/MemVector.cmx','extraction/LowerLong.cmx'],
                                     cwd=ROOT,text=True).split()
        if 'lib/Camlcoq.cmx' not in deps:
            deps.append('lib/Camlcoq.cmx')
        dirs=['extraction','lib','common','aarch64','backend','cfrontend','cparser','driver','export','debug']
        includes=[arg for directory in dirs for arg in ['-I',str(ROOT/directory)]]
        obj=ARTIFACTS/'test_memvector.cmx'; binary=ARTIFACTS/'check_memvector'
        commands=[
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-c',str(ROOT/'perf/test_memvector.ml'),'-o',str(obj)],
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
        result['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                                 for name in sources}
        if result['source_sha256'] != initial_sources:
            raise RuntimeError('Memory widening sources changed during verification')
        result['production_extraction_sha256'] = {
            name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in extraction}
        if result['production_extraction_sha256'] != initial_extraction:
            raise RuntimeError('Production extraction changed during verification')
        result['transformation'] = 'correlated adjacent Mint32 stores to one Mint64 store'
        result['indirect_address_witness'] = 'executed zero-offset global producer'
        result['indirect_output_addressing'] = 'native Aindexed zero with preserved base register'
        result['new_neon_semantics'] = False
        subprocess.run(['python3', str(ROOT/'perf/guard.py')], cwd=ROOT, check=True)
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native memvector checker did not report success')
        save()
        print(f"{result['check_count']} extracted store-widening/lowering checks passed; no speed series")
    except BaseException as error:
        result['success']=False;result['error']=str(error);save();raise


if __name__=='__main__':
    main()
