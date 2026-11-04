#!/usr/bin/env python3
"""Compare static ARM64 assembly for the same C unit, without running it.

Default input is SOURCE from check_loop_optimizations.py. CompCert -O and
clang -O2 both use -fno-inline on macOS ARM64. Counts describe printed assembly
sites, not executions, machine cycles, throughput, correctness, or speed.

Examples:
  python3 perf/compare_assembly.py
  python3 perf/compare_assembly.py --function auto_pair --function auto_loop
  python3 perf/compare_assembly.py --source example.c --profile loops2 --profile loops4
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]
LABEL=re.compile(r'^([A-Za-z_.$][\w.$]*|[0-9]+):(?:\s|$)')
GPR=re.compile(r'\b([wx](?:[12]?[0-9]|30)|[wx]zr|wsp|sp|fp|lr)\b',re.I)
SIMD=re.compile(r'\b([vqdshb](?:[12]?[0-9]|3[01]))(?:\.[0-9]*[bhsd])?(?:\[[0-9]+\])?\b',re.I)
LANES=re.compile(r'\bv(?:[12]?[0-9]|3[01])\.(?:2|4|8|16)[bhsd]\b',re.I)
CALLS={'bl','blr','blraa','blrab','blraaz','blrabz'}
RETURNS={'ret','retaa','retab','eret','eretaa','eretab'}
INDIRECT={'br','braa','brab','braaz','brabz'}
COND={'cbz','cbnz','tbz','tbnz'}
VECTOR_ARITHMETIC={
    'add','sub','mul','mla','mls','neg','abs','and','orr','eor','bic','orn','not',
    'shl','sshr','ushr','sshl','ushl','sli','sri','addp','addv','saddlp','uaddlp','eor3','bcax','rax1','xar',
    'smax','smin','umax','umin','smaxv','sminv','umaxv','uminv','sqadd','uqadd',
    'sqsub','uqsub','sqdmulh','sqrdmulh','smull','umull','smlal','umlal','smlsl','umlsl',
    'cmeq','cmge','cmgt','cmhi','cmhs','cmtst','fadd','fsub','fmul','fdiv','fmla','fmls',
    'fneg','fabs','fmax','fmin','fmaxnm','fminnm','faddp','fcmeq','fcmge','fcmgt',
}
LIMITATIONS=[
    'Counts are static printed instruction sites, not executions, cycles, or a speed estimate.',
    'Assembler aliases, directives, alignment padding and inline-assembly macros are not expanded into machine code.',
    'A pair or vector load/store counts as one instruction site; atomic read-modify-write sites can count in both categories.',
    'Backward branches mean direct targets at or before the textual instruction position; this is not a loop or trip-count proof.',
    'Explicit SP memory counts omit stack accesses through frame-pointer or other pointer aliases.',
    'Register sets are textual mentions, not simultaneous liveness, register pressure, or spill counts.',
    'SIMD register names can hold scalar floating-point values; only vector-shaped arithmetic is counted as packed arithmetic.',
    'Compiler defaults other than the recorded flags remain distinct; this comparison proves neither semantic equivalence nor profitability.',
    'Source hashes cover the translation-unit text, not included system or user headers.',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def instruction_metrics(instructions,labels):
    mnemonics=Counter(item['mnemonic'] for item in instructions)
    spellings=Counter(item['spelling'] for item in instructions)
    packed_arrangements=Counter()
    registers=set();simd=set();raw=set();branches=[]
    counts=Counter()
    for index,item in enumerate(instructions):
        mnemonic,operands=item['mnemonic'],item['operands']
        gprs=[m.lower() for m in GPR.findall(operands)]
        fprs=[m.lower() for m in SIMD.findall(operands)]
        raw.update(gprs);raw.update(fprs)
        for register in gprs:
            if re.fullmatch(r'[wx][0-9]+',register):register='x'+register[1:]
            register={'fp':'x29','lr':'x30','wsp':'sp','wzr':'xzr'}.get(register,register)
            registers.add(register)
        simd.update('v'+register[1:] for register in fprs)
        atomic=mnemonic.startswith(('ldadd','ldclr','ldeor','ldset','ldsmax','ldsmin','ldumax','ldumin','swp','cas'))
        load=mnemonic.startswith('ld') or atomic
        store=mnemonic.startswith('st') or atomic
        counts['load_sites']+=load;counts['store_sites']+=store
        counts['pair_load_sites']+=mnemonic in {'ldp','ldnp','ldpsw'}
        counts['pair_store_sites']+=mnemonic in {'stp','stnp'}
        counts['atomic_read_modify_write_sites']+=atomic
        counts['call_sites']+=mnemonic in CALLS
        counts['return_sites']+=mnemonic in RETURNS
        conditional=mnemonic in COND or mnemonic.startswith('b.') or mnemonic in {
            'beq','bne','blt','ble','bgt','bge','bhi','bhs','blo','bls','bmi','bpl','bvs','bvc'}
        direct=conditional or mnemonic=='b'
        counts['conditional_branch_sites']+=conditional
        counts['unconditional_branch_sites']+=mnemonic=='b' or mnemonic in INDIRECT
        counts['indirect_branch_sites']+=mnemonic in INDIRECT
        counts['explicit_sp_memory_sites']+=(load or store) and bool(re.search(r'\[\s*(?:sp|wsp)\b',operands,re.I))
        counts['x29_memory_sites']+=(load or store) and bool(re.search(r'\[\s*(?:x29|fp)\b',operands,re.I))
        counts['sp_reference_sites']+=any(register in {'sp','wsp'} for register in gprs)
        vector_operand=LANES.search(operands)
        arrangement=item['arrangement'] or (vector_operand[0].split('.')[-1] if vector_operand else '')
        shaped=bool(re.fullmatch(r'(?:2|4|8|16)[bhsd]',arrangement))
        counts['vector_shaped_instruction_sites']+=shaped
        counts['packed_vector_arithmetic_sites']+=shaped and mnemonic in VECTOR_ARITHMETIC
        if shaped and mnemonic in VECTOR_ARITHMETIC:packed_arrangements[arrangement]+=1
        counts['gpr_simd_fmov_sites']+=mnemonic=='fmov' and bool(gprs) and bool(fprs)
        if direct:
            target=operands.split(',')[-1].strip().split()[0] if operands.strip() else ''
            destination=labels.get(target)
            if destination is not None and destination<=index:
                branches.append({'instruction_index':index,'mnemonic':mnemonic,
                                 'target':target,'target_instruction_index':destination})
    counts['branch_sites']=counts['conditional_branch_sites']+counts['unconditional_branch_sites']
    counts['backward_direct_branch_sites']=len(branches)
    return {'instruction_sites':len(instructions),'mnemonic_counts':dict(sorted(mnemonics.items())),
        'mnemonic_spellings':dict(sorted(spellings.items())),
        'packed_arithmetic_arrangements':dict(sorted(packed_arrangements.items())),
        'counts':dict(sorted(counts.items())),'gpr_registers':sorted(registers),
        'simd_registers':sorted(simd),'register_tokens':sorted(raw),'backward_direct_branches':branches,
        'mnemonic_sequence':[item['mnemonic'] for item in instructions]}


def parse_assembly(text):
    """Parse Darwin compiler function ranges; cfi_startproc/endproc bound them."""
    functions={};globals_=set();in_text=False;current=None;pending=None
    instructions=[];labels={}

    def finish():
        nonlocal current,instructions,labels
        if current is not None:
            name=current[1:] if current.startswith('_') else current
            if name in functions:raise ValueError('Repeated function symbol: '+current)
            functions[name]={'symbol':current,**instruction_metrics(instructions,labels)}
        current=None;instructions=[];labels={}

    for original in text.splitlines():
        line=re.split(r'//|;',original,maxsplit=1)[0].strip()
        if not line:continue
        if line.startswith(('.globl ','.global ')):
            globals_.add(line.split(None,1)[1].strip());continue
        if line=='.text' or line.startswith('.section'):
            if line=='.text' or '__text' in line:in_text=True
            else:in_text=False
        elif line.startswith(('.data','.const','.cstring','.literal','.bss')):
            in_text=False
        label=LABEL.match(line)
        if label:
            symbol=label[1]
            if current is not None:
                if symbol in globals_:
                    finish();pending=symbol
                else:labels[symbol]=len(instructions)
            elif in_text:pending=symbol
            continue
        if line.startswith('.cfi_startproc'):
            if pending is None:raise ValueError('CFI function lacks a preceding named label')
            finish();current=pending;labels[current]=0;pending=None;continue
        if line.startswith('.cfi_endproc'):
            finish();pending=None;continue
        if line.startswith('.'):continue
        match=re.match(r'^([A-Za-z][A-Za-z0-9_.]*)\s*(.*)$',line)
        if match and in_text:
            if current is None:
                if pending is None:raise ValueError('Instruction outside a recognized function: '+line)
                current=pending;labels[current]=0;pending=None
            spelling=match[1].lower()
            # Darwin clang emits add.4s v0,v1,v2, while CompCert emits
            # add v0.2s,v1.2s,v2.2s. Normalize both; keep b.hs untouched.
            suffix=re.search(r'\.((?:2|4|8|16)?[bhsd])$',spelling)
            mnemonic=spelling[:suffix.start()] if suffix else spelling
            instructions.append({'mnemonic':mnemonic,'spelling':spelling,
                                 'arrangement':suffix[1] if suffix else '', 'operands':match[2]})
    finish()
    if not functions:raise ValueError('No ARM64 function instruction ranges found')
    return functions


def observations(variants):
    clang=variants.get('clang-O2');result=[]
    if clang is None:return result
    for name,version in variants.items():
        if name=='clang-O2':continue
        ours=version['counts'];theirs=clang['counts']
        if ours['packed_vector_arithmetic_sites'] and not theirs['packed_vector_arithmetic_sites']:
            result.append({'variant':name,'kind':'packed_arithmetic_present_only_in_compcert',
                'evidence':{'compcert_packed_sites':ours['packed_vector_arithmetic_sites'],
                            'clang_packed_sites':0,'compcert_gpr_simd_fmov_sites':ours['gpr_simd_fmov_sites']},
                'review_target':'Inspect pack, unpack and cross-register-file moves around the packed arithmetic.'})
        if ours['backward_direct_branch_sites'] and not theirs['backward_direct_branch_sites']:
            result.append({'variant':name,'kind':'backward_sites_present_only_in_compcert',
                'evidence':{'compcert_backward_sites':ours['backward_direct_branch_sites'],'clang_backward_sites':0},
                'review_target':'Inspect whether clang eliminated or reorganized the loop and identify the semantic transformation.'})
        if version['instruction_sites']!=clang['instruction_sites']:
            result.append({'variant':name,'kind':'different_static_instruction_site_counts',
                'evidence':{'compcert_sites':version['instruction_sites'],'clang_sites':clang['instruction_sites']},
                'review_target':'Inspect the instruction sequences and control flow; these totals alone do not establish a runtime difference.'})
    return result


def parser_self_check():
    """Cross-syntax regression: Darwin suffixes and operand shapes must agree."""
    template='''.text
.globl _fixture
_fixture:
.cfi_startproc
Lagain:
VECTOR
ldr x0, [sp, #8]
stp x29, x30, [sp, #-16]!
bl _callee
b.ne Lagain
ret
.cfi_endproc
.const
_data:
.long 17
'''
    operand=parse_assembly(template.replace('VECTOR','add v0.4s, v1.4s, v2.4s'))
    darwin=parse_assembly(template.replace('VECTOR','add.4s v0, v1, v2'))
    if set(operand)!={'fixture'} or set(darwin)!={'fixture'}:
        raise AssertionError('Parser included data as a function')
    a,b=operand['fixture'],darwin['fixture']
    if a['mnemonic_counts']!=b['mnemonic_counts'] or a['counts']!=b['counts']:
        raise AssertionError('Darwin and operand-arrangement instruction counts differ')
    expected={'load_sites':1,'store_sites':1,'call_sites':1,'backward_direct_branch_sites':1,
              'packed_vector_arithmetic_sites':1,'explicit_sp_memory_sites':2}
    if a['instruction_sites']!=6 or any(a['counts'][key]!=value for key,value in expected.items()):
        raise AssertionError('Parser category or branch-direction regression')


def main():
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--source',type=Path,help='C unit; defaults to the ordinary-C loop-correctness fixture')
    parser.add_argument('--function',action='append',default=[],help='source C function name to include; repeatable')
    parser.add_argument('--profile',action='append',help='CompCert experiment profile; repeatable, default loops4')
    parser.add_argument('--experiments',action='append',default=[],metavar='NAME=FLAGS',
                        help='named explicit experiment selection; repeatable')
    parser.add_argument('--clang',default='clang')
    parser.add_argument('--output',type=Path,default=ROOT/'perf/results/assembly-comparison.json')
    parser.add_argument('--artifacts',type=Path,default=ROOT/'perf/artifacts/assembly-comparison')
    args=parser.parse_args()
    artifacts=args.artifacts.resolve();artifacts.mkdir(parents=True,exist_ok=True)
    output=args.output.resolve();output.parent.mkdir(parents=True,exist_ok=True)
    report={'schema_version':1,'success':False,'analysis_kind':'static_assembly_source',
        'performance_measured':False,'compiled_programs_executed':False,'promotion_decision':False,
        'limitations':LIMITATIONS,
        'mnemonic_normalization':'Vector arrangement suffixes are normalized across Darwin and operand-suffix spellings; conditional branch suffixes are retained.',
        'commands':[],'compilers':{},'functions':{}}

    def save():
        temporary=output.with_suffix(output.suffix+'.tmp')
        temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(output)

    def run(command,label,flags=''):
        command=[str(item) for item in command]
        env=os.environ.copy();env['COMPCERT_EXPERIMENTS']=flags
        env['COMPCERT_CONFIG']=str(ROOT/'compcert.ini');env.pop('COMPCERT_EXPERIMENT_TRACE',None)
        report['commands'].append({'label':label,'argv':command,'experiments':flags})
        actual=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,text=True,timeout=180)
        (artifacts/(label+'.stdout')).write_text(actual.stdout)
        (artifacts/(label+'.stderr')).write_text(actual.stderr)
        actual.check_returncode();return actual.stdout.strip()

    save()
    try:
        parser_self_check();report['parser_cross_syntax_check']=True
        if platform.system()!='Darwin' or platform.machine()!='arm64':
            raise RuntimeError('This comparison requires the configured native macOS ARM64 checkout')
        config=(ROOT/'Makefile.config').read_text()
        if not re.search(r'^ARCH=aarch64$',config,re.M) or not re.search(r'^SYSTEM=macos$',config,re.M):
            raise RuntimeError('CompCert must be configured for aarch64-macos')
        if not (ROOT/'ccomp').is_file():raise RuntimeError('Build ccomp before comparing assembly')
        run(['python3',ROOT/'perf/guard.py'],'source-guard')
        catalog=json.loads((ROOT/'perf/experiment-profiles.json').read_text())['profiles']
        profiles=list(dict.fromkeys(args.profile or ([] if args.experiments else ['loops4'])))
        unknown=set(profiles)-set(catalog)
        if unknown:raise ValueError('Unknown experiment profiles: '+','.join(sorted(unknown)))
        if any(not re.fullmatch(r'[a-z][a-z0-9_-]*',name) for name in profiles):
            raise ValueError('Profile names must be simple identifiers')
        selections=[(name,catalog[name]) for name in profiles]
        for item in args.experiments:
            name,separator,flags=item.partition('=')
            if not separator or not flags or not re.fullmatch(r'[a-z][a-z0-9_-]*',name):
                raise ValueError('Explicit experiments require NAME=FLAGS with a simple name')
            if name=='default' or any(name==existing for existing,_ in selections):
                raise ValueError('Repeated or reserved experiment name: '+name)
            selections.append((name,flags))
        if args.source is None:
            from check_loop_optimizations import SOURCE
            source=artifacts/'source.c';source.write_text(SOURCE)
            origin='perf/check_loop_optimizations.py:SOURCE'
        else:
            source=args.source.resolve()
            if not source.is_file():raise ValueError('C source file does not exist: '+str(source))
            origin=str(source)
            (artifacts/'source.c').write_bytes(source.read_bytes())
        report['source']={'path':str(source),'origin':origin,'sha256':sha(source),
                          'archived_path':str(artifacts/'source.c')}
        clang_path=Path(shutil.which(args.clang) or args.clang).resolve()
        report['target']={'isa':'AArch64','os':'macOS','assembly_format':'Darwin/Mach-O',
                          'host':platform.platform(),'inlining':'disabled in both compilers'}
        report['compiler_versions']={'compcert':run([ROOT/'ccomp','-version'],'compcert-version'),
                                     'clang':run([args.clang,'--version'],'clang-version')}
        report['source_sha256']={name:sha(ROOT/name) for name in
            ['perf/compare_assembly.py','perf/check_loop_optimizations.py','perf/experiment-profiles.json']}
        report['configuration_sha256']={name:sha(ROOT/name) for name in ['Makefile.config','compcert.ini']}
        variants=[('compcert-default','',ROOT/'ccomp',['-O','-fno-inline','-stdlib',ROOT/'runtime'])]
        variants += [('compcert-'+name,flags,ROOT/'ccomp',['-O','-fno-inline','-stdlib',ROOT/'runtime']) for name,flags in selections]
        variants += [('clang-O2','',args.clang,['-O2','-fno-inline','-arch','arm64'])]
        parsed={}
        for name,flags,compiler,options in variants:
            assembly=artifacts/(name+'.s')
            run([compiler,*options,'-S',source,'-o',assembly],name,flags)
            parsed[name]=parse_assembly(assembly.read_text())
            report['compilers'][name]={'experiments':flags,'flags':[str(item) for item in options],
                'compiler_path':str(clang_path if name=='clang-O2' else ROOT/'ccomp'),
                'compiler_sha256':sha(clang_path if name=='clang-O2' else ROOT/'ccomp'),
                'assembly_path':str(assembly),'assembly_sha256':sha(assembly),
                'parsed_functions':sorted(parsed[name])}
        available=set().union(*(set(functions) for functions in parsed.values()))
        selected=set(args.function) if args.function else available
        missing=selected-available
        if missing:raise ValueError('Requested functions absent from all assembly: '+','.join(sorted(missing)))
        for function in sorted(selected):
            versions={name:functions[function] for name,functions in parsed.items() if function in functions}
            reference=versions.get('clang-O2')
            comparisons={}
            if reference:
                for name,version in versions.items():
                    if name=='clang-O2':continue
                    comparisons[name]={'instruction_sites_delta':version['instruction_sites']-reference['instruction_sites'],
                        'count_deltas':{key:version['counts'][key]-reference['counts'][key] for key in reference['counts']}}
            report['functions'][function]={'variants':versions,'missing_variants':sorted(set(parsed)-set(versions)),
                'deltas_to_clang_O2':comparisons,'observations':observations(versions)}
        report['common_functions']=sorted(set.intersection(*(set(functions) for functions in parsed.values())) & selected)
        if not report['common_functions']:raise RuntimeError('No functions common to all compiler variants')
        if sha(source)!=report['source']['sha256']:raise RuntimeError('Source changed during comparison')
        for field in ['source_sha256','configuration_sha256']:
            if any(sha(ROOT/name)!=digest for name,digest in report[field].items()):
                raise RuntimeError('Comparison inputs or configuration changed during analysis')
        for variant in report['compilers'].values():
            if sha(Path(variant['compiler_path']))!=variant['compiler_sha256']:
                raise RuntimeError('Compiler changed during comparison')
        report['success']=True;save()
        print(f"Static assembly comparison: {len(report['functions'])} functions, {len(variants)} compiler configurations; no program execution or speed measurement")
        for function,item in report['functions'].items():
            if function not in report['common_functions']:continue
            text=', '.join(name+'='+str(version['instruction_sites']) for name,version in item['variants'].items())
            print(function+': printed instruction sites '+text)
    except BaseException as error:
        report.update(success=False,error=str(error));save();raise


if __name__=='__main__':main()
