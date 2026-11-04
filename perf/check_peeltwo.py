#!/usr/bin/env python3
"""Native structural and differential checks of production two-traversal CFG peeling."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/peeltwo"
OUTPUT = ROOT / "perf/results/peeltwo.json"


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    result = {"success": False, "performance_measured": False, "commands": []}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(result, indent=2)+'\n')
        temporary.replace(OUTPUT)

    sources = ['backend/PeelTwo.v', 'backend/PeelTwoproof.v',
               'perf/test_peeltwo.ml', 'perf/check_peeltwo.py']
    extraction = ['extraction/PeelTwo.ml', 'extraction/PeelTwo.cmx']
    save()
    try:
        initial_sources = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                           for name in sources}
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        initial_extraction = {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                              for name in extraction}
        deps=subprocess.check_output([str(ROOT/'tools/modorder'),'.depend.extr',
                                      'lib/Camlcoq.cmx','extraction/PeelTwo.cmx'],
                                     cwd=ROOT,text=True).split()
        if 'lib/Camlcoq.cmx' not in deps:
            deps.append('lib/Camlcoq.cmx')
        dirs=['extraction','lib','common','aarch64','backend','cfrontend','cparser','driver','export','debug']
        includes=[arg for directory in dirs for arg in ['-I',str(ROOT/directory)]]
        obj=ARTIFACTS/'test_peeltwo.cmx'; binary=ARTIFACTS/'check_peeltwo'
        commands=[
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-c',str(ROOT/'perf/test_peeltwo.ml'),'-o',str(obj)],
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
            raise RuntimeError('Two-traversal peeling sources changed during verification')
        result['production_extraction_sha256'] = {
            name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in extraction}
        if result['production_extraction_sha256'] != initial_extraction:
            raise RuntimeError('Production extraction changed during verification')
        result['transformation'] = 'validated first/second/stable CFG copies'
        subprocess.run(['python3', str(ROOT/'perf/guard.py')], cwd=ROOT, check=True)
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native two-traversal checker did not report success')
        save()
        print(f"{result['check_count']} extracted two-traversal peeling checks passed; no speed series")
    except BaseException as error:
        result['success']=False;result['error']=str(error);save();raise


if __name__=='__main__':
    main()
