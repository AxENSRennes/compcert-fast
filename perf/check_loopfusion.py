#!/usr/bin/env python3
"""Native checks of extracted bounded pure loop fusion and its production symbolic validator."""
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "perf/artifacts/loopfusion"
OUTPUT = ROOT / "perf/results/loopfusion.json"

C_SOURCE = r'''
#include <stdio.h>
unsigned fused(unsigned a,unsigned b) {
  unsigned i,j,s=0,t=0;
  for(i=0;i<4u;++i) s+=a+i;
  for(j=0;j<4u;++j) t+=b+j;
  return s^t;
}
unsigned fused_shared(unsigned a,unsigned b) {
  unsigned i,s=0,t=0;
  for(i=0;i<4u;++i) s+=a+i;
  for(i=0;i<4u;++i) t+=b+i;
  return s^t;
}
int main(void) {
  unsigned a,b;
  for(a=0;a<17;++a) for(b=0;b<17;++b)
    printf("%u %u\n",fused(a*0x80000001u,b*0x7fffffffu),fused_shared(a*0x80000001u,b*0x7fffffffu));
  return 0;
}
'''


def assembly_stats(path):
    text=path.read_text()
    body=re.split(r"(?m)^_fused_shared:[^\n]*\n",text,maxsplit=1)[1].split(".cfi_endproc",1)[0]
    instructions=[line.strip() for line in body.splitlines() if line.startswith("\t") and re.match(r"[a-z]",line.lstrip())]
    return {"instructions":len(instructions), "conditional_branches":sum(bool(re.match(r"b\.[a-z]+\s",line)) for line in instructions)}


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    result = {"success": False, "performance_measured": False, "commands": []}

    def save():
        temporary=OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(result, indent=2)+'\n')
        temporary.replace(OUTPUT)

    sources = ['backend/LoopFusion.v', 'backend/LoopFusionproof.v',
               'perf/test_loopfusion.ml', 'perf/check_loopfusion.py']

    def snapshot(names):
        return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                for name in names}

    save()
    try:
        initial_sources = snapshot(sources)
        initial_compiler = hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest()
        subprocess.run(['python3',str(ROOT/'perf/guard.py')],cwd=ROOT,check=True)
        deps=subprocess.check_output([str(ROOT/'tools/modorder'),'.depend.extr',
                                      'extraction/LoopFusion.cmx'],
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
        obj=ARTIFACTS/'test_loopfusion.cmx'; binary=ARTIFACTS/'check_loopfusion'
        commands=[
            [str(ROOT/'perf/in-env'),'ocamlopt','-g',*includes,'-c',str(ROOT/'perf/test_loopfusion.ml'),'-o',str(obj)],
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
        source=ARTIFACTS/'loop.c';source.write_text(C_SOURCE)
        clang=ARTIFACTS/'loop.clang'
        clang_asm=ARTIFACTS/'clang.s'
        for command in [['clang','-O2','-fno-inline',str(source),'-o',str(clang)],
                        ['clang','-O2','-fno-inline','-S',str(source),'-o',str(clang_asm)]]:
            result['commands'].append(command)
            subprocess.run(command,cwd=ROOT,check=True)
        reference=subprocess.check_output([str(clang)],cwd=ROOT)
        if len(reference.splitlines())!=289:
            raise RuntimeError('Incomplete unsigned C reference')
        result['c_configurations']={}
        result['assembly']={'clang-O2':assembly_stats(clang_asm)}
        for name,flags in [('default',''),('enabled','loop-fusion')]:
            trace=ARTIFACTS/(name+'.trace.jsonl');trace.unlink(missing_ok=True)
            environment=os.environ.copy()
            environment['COMPCERT_CONFIG']=str(ROOT/'compcert.ini')
            environment['COMPCERT_EXPERIMENTS']=flags
            environment['COMPCERT_EXPERIMENT_TRACE']=str(trace)
            executable=ARTIFACTS/(name+'.exe');assembly=ARTIFACTS/(name+'.s')
            commands=[[str(ROOT/'ccomp'),'-stdlib',str(ROOT/'runtime'),'-fno-inline',str(source),'-o',str(executable)],
                      [str(ROOT/'ccomp'),'-stdlib',str(ROOT/'runtime'),'-fno-inline','-S',str(source),'-o',str(assembly)]]
            for command in commands:
                result['commands'].append(command)
                subprocess.run(command,cwd=ROOT,env=environment,check=True)
            output=subprocess.check_output([str(executable)],cwd=ROOT)
            if output!=reference:
                raise RuntimeError(name+' unsigned C output mismatch')
            records=[json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
            if flags:
                changes=sum(r['count'] for r in records if r['pass']==flags and r['event']=='changed-functions')
                if changes<1:
                    raise RuntimeError('C integration did not actually fuse the shared-counter loops')
            elif records:
                raise RuntimeError('Default compiler emitted experiment trace')
            result['c_configurations'][name]={'correctness_pass':True,'outputs':289,
                'stdout_sha256':hashlib.sha256(output).hexdigest(),'trace':records}
            result['assembly'][name]=assembly_stats(assembly)
        if result['assembly']['default']['conditional_branches']!=2 or result['assembly']['enabled']['conditional_branches']!=1:
            raise RuntimeError('Generated assembly does not show two loops reduced to one')
        if snapshot(sources) != initial_sources:
            raise RuntimeError('Loop fusion sources changed during verification')
        if snapshot(extraction) != initial_extraction:
            raise RuntimeError('Production extraction changed during verification')
        if hashlib.sha256((ROOT/'ccomp').read_bytes()).hexdigest() != initial_compiler:
            raise RuntimeError('Production compiler changed during verification')
        subprocess.run(['python3', str(ROOT/'perf/guard.py')], cwd=ROOT, check=True)
        result['verification_snapshot_unchanged'] = True
        if result.get('success') is not True or not result['check_count']:
            raise RuntimeError('Native loopfusion checker did not report success')
        save()
        print(f"{result['check_count']} extracted loopfusion optimization checks passed; no speed series")
    except BaseException as error:
        result['success']=False;result['error']=str(error);save();raise


if __name__=='__main__':
    main()
