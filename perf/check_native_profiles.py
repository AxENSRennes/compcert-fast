#!/usr/bin/env python3
"""Run the upstream native/ABI/PIC suite with defaults and every frozen profile."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
OUTPUT=ROOT/'perf/results/native-experiments.json'
ARTIFACTS=ROOT/'perf/artifacts/native-experiments'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs',type=int,default=4)
    args=parser.parse_args()
    if args.jobs<1:parser.error('--jobs must be positive')
    ARTIFACTS.mkdir(parents=True,exist_ok=True)
    OUTPUT.parent.mkdir(parents=True,exist_ok=True)
    report={'success':False,'performance_measured':False,'profiles':{},'commands':[]}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report,indent=2)+'\n')
        temporary.replace(OUTPUT)

    save()
    try:
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        manifest=json.loads((ROOT/'perf/experiment-profiles.json').read_text())
        for name,flags in [('default',''),*manifest['profiles'].items()]:
            environment=os.environ.copy()
            environment['COMPCERT_EXPERIMENTS']=flags
            environment['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
            environment.pop('COMPCERT_EXPERIMENT_TRACE',None)
            for stage,options in [('clean',['clean']),('build',[f'-j{args.jobs}','all']),('test',['test'])]:
                command=[str(ROOT/'perf/in-env'),'make','-C','test',*options]
                report['commands'].append(command)
                with (ARTIFACTS/(name+'-'+stage+'.log')).open('w') as log:
                    subprocess.run(command,cwd=ROOT,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True)
            text=(ARTIFACTS/(name+'-test.log')).read_text()
            if re.search(r'\b(?:FAILED|DISAGREE|FAILURE)\b|: failed',text):
                raise RuntimeError('Upstream native failure: '+name)
            checks=[line for line in text.splitlines() if re.search(r': passed$|: skipped|compiler and interpreter agree',line)]
            passed=sum(line.endswith(': passed') for line in checks)
            if passed<150:raise RuntimeError('Incomplete native suite: '+name)
            report['profiles'][name]={'flags':flags,'passed':passed,
                'skipped':sum(': skipped' in line for line in checks),
                'interpreter_agreements':sum('compiler and interpreter agree' in line for line in checks),
                'checks':checks,'success':True}
            save()
            print(f'{name}: {passed} upstream native tests passed',flush=True)
        report['compiler_sha256']=hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        report['source_sha256']={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in
            ['perf/check_native_profiles.py','perf/experiment-profiles.json']}
        report['success']=True;save()
    except BaseException as error:
        report.update(success=False,error=str(error));save();raise


if __name__=='__main__':
    main()
