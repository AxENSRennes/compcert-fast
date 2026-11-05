#!/usr/bin/env python3
"""Check automatic pairing of ordinary uint32_t array updates on ARM64."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / 'perf/artifacts/arraypair'
OUTPUT = ROOT / 'perf/results/arraypair.json'
TRUST_BASE = '472feccc3b037e8294a1c299dd214350468f92bb'
TRUSTED = [
    'aarch64/Asm.v', 'aarch64/Builtins1.v', 'aarch64/Asmexpand.ml',
    'aarch64/TargetPrinter.ml', 'aarch64/Machregs.v',
    'aarch64/CBuiltins.ml', 'common/Values.v', 'common/Memory.v',
    'common/Memdata.v', 'common/AST.v', 'common/Events.v', 'common/Builtins.v',
    'cfrontend/Clight.v', 'cfrontend/Cop.v',
]
POSITIVE = {'add_while': 7, 'add_for': 0xffffffff, 'add_index': 0x80000000}
NEGATIVE = ['add_volatile', 'add_signed', 'add_stride', 'add_postdec', 'add_end',
            'add_size', 'add_from_next', 'add_break']
PACKED_ADD = '__builtin_cc_neon_add_u32x2'
EDGES = [0, 1, 2, 3, 0x7fffffff, 0x80000000, 0xffffffff, 0xaaaaaaaa, 0x55555555]
MASK = 0xffffffff

C_SOURCE = r'''
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>

void add_while(uint32_t *p, unsigned n) {
  while(n) { *p += 7; ++p; --n; }
}
void add_for(uint32_t *p, unsigned n) {
  for(;n;++p,--n) *p += 0xffffffffu;
}
void add_index(uint32_t *p, unsigned n) {
  for(unsigned i=0;i<n;++i) p[i] += 0x80000000u;
}
void add_volatile(volatile uint32_t *p, unsigned n) {
  while(n) { *p += 7u; ++p; --n; }
}
void add_signed(int32_t *p, unsigned n) {
  while(n) { *p += 7; ++p; --n; }
}
void add_stride(uint32_t *p, unsigned n) {
  for(unsigned i=0;i<n;i+=2) p[i] += 7u;
}
void add_postdec(uint32_t *p, unsigned n) {
  while(n--) { *p += 7u; ++p; }
}
void add_end(uint32_t *p, unsigned n) {
  uint32_t *end=p+n;
  for(;p!=end;++p) *p += 7u;
}
void add_size(uint32_t *p, size_t n) {
  for(size_t i=0;i<n;++i) p[i] += 7u;
}
void add_from_next(uint32_t *p, unsigned n) {
  while(n) { *p = p[1]+7u; ++p; --n; }
}
void add_break(uint32_t *p, unsigned n) {
  while(n) { if(!*p) break; *p += 7u; ++p; --n; }
}

static uint32_t sample(unsigned seed, unsigned i) {
  static const uint32_t edges[] = {0u,1u,2u,3u,0x7fffffffu,0x80000000u,
                                   0xffffffffu,0xaaaaaaaau,0x55555555u};
  uint32_t mix = seed ? seed*0x9e3779b9u+i*0x85ebca6bu : 0u;
  return edges[(seed+i)%9u]^mix;
}
static void dump(unsigned family, unsigned fn, unsigned n, unsigned offset,
                 unsigned seed, const uint32_t *p, unsigned count) {
  printf("%u %u %u %u %u",family,fn,n,offset,seed);
  for(unsigned i=0;i<count;++i) printf(" %u",p[i]);
  putchar('\n');
}
static void apply(unsigned fn, uint32_t *p, unsigned n) {
  if(fn==0u) add_while(p,n);
  else if(fn==1u) add_for(p,n);
  else add_index(p,n);
}

int main(void) {
  uint32_t a[48];
  for(unsigned n=0;n<37u;++n) for(unsigned off=0;off<4u;++off)
    for(unsigned seed=0;seed<9u;++seed) for(unsigned fn=0;fn<3u;++fn) {
      for(unsigned i=0;i<48u;++i) a[i]=sample(seed,i);
      apply(fn,a+off,n);
      dump(0,fn,n,off,seed,a,48);
    }

  long page=sysconf(_SC_PAGESIZE);
  if(page<128 || page%sizeof(uint32_t)!=0) return 2;
  size_t bytes=(size_t)page;
  unsigned char *pages=mmap(0,3u*bytes,PROT_NONE,MAP_PRIVATE|MAP_ANON,-1,0);
  if(pages==MAP_FAILED) return 3;
  unsigned char *middle=pages+bytes;
  if(mprotect(middle,bytes,PROT_READ|PROT_WRITE)!=0) return 4;
  for(unsigned n=1;n<18u;++n) for(unsigned end=0;end<2u;++end)
    for(unsigned seed=0;seed<=7u;seed+=7u) for(unsigned fn=0;fn<3u;++fn) {
      uint32_t *p = end ? (uint32_t *)(middle+bytes-n*sizeof(uint32_t))
                        : (uint32_t *)middle;
      uint32_t *canary = end ? p-1 : p+n;
      *canary=0xfedcba98u;
      for(unsigned i=0;i<n;++i) p[i]=sample(seed,i);
      apply(fn,p,n);
      if(*canary!=0xfedcba98u) return 5;
      dump(1,fn,n,end,seed,p,n);
    }
  if(munmap(pages,3u*bytes)!=0) return 6;
  add_while(0,0); add_for(0,0); add_index(0,0);
  puts("zero length accepts null");
  return 0;
}
'''


def oracle():
    def initial(seed, size):
        return [EDGES[(seed+i) % len(EDGES)] ^
                ((seed*0x9e3779b9 + i*0x85ebca6b) & MASK if seed else 0)
                for i in range(size)]

    def line(family, fn, n, offset, seed, size, start, increment):
        cells = initial(seed, size)
        cells[start:start+n] = [(value+increment) & MASK for value in cells[start:start+n]]
        return ' '.join(map(str, [family, fn, n, offset, seed, *cells]))

    regular = [line(0, fn, n, offset, seed, 48, offset, increment)
               for n in range(37) for offset in range(4) for seed in range(9)
               for fn, increment in enumerate(POSITIVE.values())]
    guarded = [line(1, fn, n, end, seed, n, 0, increment)
               for n in range(1, 18) for end in range(2) for seed in [0, 7]
               for fn, increment in enumerate(POSITIVE.values())]
    data = '\n'.join([*regular, *guarded, 'zero length accepts null', '']).encode()
    return data, len(regular), len(guarded)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def snapshot(files):
    return {name: sha((ROOT / name).read_bytes()) for name in files}


def rtl_body(text, function):
    return text.split('\n' + function + '(', 1)[1].split('\n}\n', 1)[0]


def paired_store_lanes(body):
    # PrintRTL omits the successor for pc - 1 and prints other successors
    # on an indented continuation line.
    nodes = {int(pc): (instruction, int(successor) if successor else int(pc)-1)
             for pc, instruction, successor in re.findall(
                 r'^[ \t]*(\d+):[ \t]+([^\n]+)(?:\n[ \t]+goto (\d+))?', body, re.M)}
    builtin = re.compile(r'(x\d+) = builtin "' + re.escape(PACKED_ADD) + r'"\(.*\)')
    calls = [(match[1], successor) for instruction, successor in nodes.values()
             if (match := builtin.fullmatch(instruction))]
    if len(calls) != 1:
        return None
    result, pc = calls[0]
    lanes = {result: 'packed'}
    extracts = {('lowlong', 'packed'): 'low', ('highlong', 'packed'): 'high',
                ('lowlong', 'shifted'): 'high'}
    stores = []
    addresses = set()
    visited = set()
    while pc in nodes and pc not in visited:
        visited.add(pc)
        instruction, pc = nodes[pc]
        if instruction.startswith(('if (', 'return')):
            return stores if len(addresses) == len(stores) else None
        jump = re.fullmatch(r'goto (\d+)', instruction)
        if jump:
            pc = int(jump[1])
            continue
        store = re.fullmatch(r'(\w+)\[(.+)\] = (x\d+)', instruction)
        if store:
            if store[1] != 'int32':
                return None
            addresses.add(store[2])
            stores.append(lanes.get(store[3]))
            continue
        assignment = re.fullmatch(r'(x\d+) = (.+)', instruction)
        if assignment:
            dst, rhs = assignment.groups()
            extract = re.fullmatch(r'(lowlong|highlong)\((x\d+)\)', rhs)
            shift = re.fullmatch(r'(x\d+) >>lu 32', rhs)
            if extract:
                lane = extracts.get((extract[1], lanes.get(extract[2])))
            elif shift and lanes.get(shift[1]) == 'packed':
                lane = 'shifted'
            else:
                lane = lanes.get(rhs)
            lanes[dst] = lane
    return None


def assembly_body(text, function):
    return text.split('\n_' + function + ':', 1)[1].split('.cfi_endproc', 1)[0]


def assembly_counts(body):
    def count(pattern):
        return len(re.findall(pattern, body, re.M))

    return {
        'neon_add_2s': count(r'\badd(?:\.2s\s+v\d+|\s+v\d+\.2s)\b'),
        'neon_add_4s': count(r'\badd(?:\.4s\s+v\d+|\s+v\d+\.4s)\b'),
        'neon_xor': count(r'\beor(?:\.\w+\s+v\d+|\s+v\d+\.)'),
        'vector_loads': count(r'^\s*(?:(?:ldr|ldp)\s+[qd]\d+|ld1\s+\{)'),
        'vector_stores': count(r'^\s*(?:(?:str|stp)\s+[qd]\d+|st1\s+\{)'),
    }


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    report = {'success': False, 'performance_measured': False, 'commands': [],
              'c_configurations': {}}

    def save():
        temporary = OUTPUT.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(OUTPUT)

    def run(command, label, env=None):
        command = [str(arg) for arg in command]
        report['commands'].append(command)
        result = subprocess.run(command, cwd=ARTIFACTS, env=env,
                                capture_output=True, timeout=180)
        (ARTIFACTS / (label + '.stdout')).write_bytes(result.stdout)
        (ARTIFACTS / (label + '.stderr')).write_bytes(result.stderr)
        result.check_returncode()
        return result.stdout

    save()
    try:
        sources = sorted(str(path.relative_to(ROOT))
                         for path in (ROOT / 'cfrontend').glob('ArrayPair*.v'))
        sources.extend(['perf/check_arraypair.py', 'perf/experiment-profiles.json',
                        'driver/Compiler.v', 'compcert.ini', 'ccomp'])
        before = snapshot(sources)
        trusted = snapshot(TRUSTED)
        baseline = {name: sha(subprocess.check_output(['git', 'show', TRUST_BASE+':'+name],
                                                     cwd=ROOT)) for name in TRUSTED}
        if trusted != baseline:
            raise RuntimeError('Existing semantics or NEON expansion changed')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-before')

        expected, regular_count, guard_count = oracle()
        source = ARTIFACTS / 'array_pair.c'
        source.write_text(C_SOURCE)
        if PACKED_ADD in C_SOURCE:
            raise RuntimeError('The C input must contain scalar loops only')
        clang_asm = ARTIFACTS / 'clang.s'
        clang_exe = ARTIFACTS / 'clang.exe'
        clang = ['clang', '-O2', '-fno-inline']
        run([*clang, '-S', source, '-o', clang_asm], 'clang-assembly')
        run([*clang, source, '-o', clang_exe], 'clang-build')
        clang_out = run([clang_exe], 'clang-run')
        if clang_out != expected:
            raise RuntimeError('Clang output differs from the modular arithmetic oracle')
        report['clang_O2_assembly'] = {
            name: assembly_counts(assembly_body(clang_asm.read_text(), name)) for name in POSITIVE}
        catalog = json.loads((ROOT / 'perf/experiment-profiles.json').read_text())
        configs = {'default': '', 'enabled': 'memory-neon',
                   'memory-loops': catalog['profiles']['memory-loops']}
        scalar_rtl = {}
        rtl_dump = ARTIFACTS / 'array_pair.rtl.0'
        for name, flags in configs.items():
            env = os.environ.copy()
            env.update(COMPCERT_CONFIG=str(ROOT / 'compcert.ini'), COMPCERT_EXPERIMENTS=flags)
            env.pop('COMPCERT_EXPERIMENT_TRACE', None)
            compiler = [ROOT / 'ccomp', '-stdlib', ROOT / 'runtime', '-fno-inline']
            asm = ARTIFACTS / (name + '.s')
            exe = ARTIFACTS / (name + '.exe')
            rtl_dump.unlink(missing_ok=True)
            run([*compiler, '-drtl', '-S', source, '-o', asm], name + '-assembly', env)
            rtl = rtl_dump.read_text()
            (ARTIFACTS / (name + '.rtl.0')).write_text(rtl)
            run([*compiler, source, '-o', exe], name + '-build', env)
            out = run([exe], name + '-run', env)
            if out != expected:
                raise RuntimeError(name + ': output differs from Clang and the oracle')
            enabled = 'memory-neon' in flags.split(',')
            functions = {}
            asm_text = asm.read_text()
            for function in [*POSITIVE, *NEGATIVE]:
                body = rtl_body('\n' + rtl, function)
                paired = enabled and function in POSITIVE
                packed_calls = body.count(PACKED_ADD)
                if packed_calls != int(paired):
                    raise RuntimeError(name + ': unexpected RTL0 packed call count in ' + function)
                if paired and 'int64[' in body:
                    raise RuntimeError(name + ': paired function introduces wide memory access: ' + function)
                stores = paired_store_lanes(body) if paired else []
                if paired and stores != ['low', 'high']:
                    raise RuntimeError(name + ': stores do not use both packed lanes in ' + function)
                if name == 'default':
                    scalar_rtl[function] = body
                elif function in NEGATIVE and body != scalar_rtl[function]:
                    raise RuntimeError(name + ': unsupported Clight function changed: ' + function)
                counts = assembly_counts(assembly_body(asm_text, function))
                if paired and counts['neon_add_2s'] == 0:
                    raise RuntimeError(name + ': paired function emits no NEON add: ' + function)
                if not paired and name != 'memory-loops' and counts['neon_add_2s']:
                    raise RuntimeError(name + ': unexpected NEON add in ' + function)
                functions[function] = {'rtl0_packed_add_calls': packed_calls,
                                       'rtl0_paired_store_lanes': stores, **counts}
            report['c_configurations'][name] = {
                'flags': flags, 'correctness_pass': True, 'stdout_sha256': sha(out),
                'assembly_sha256': sha(asm.read_bytes()), 'functions': functions,
            }
            save()
        if snapshot(sources) != before or snapshot(TRUSTED) != trusted:
            raise RuntimeError('Compiler, verifier or semantics changed during verification')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-after')
        report.update(success=True, regular_cases=regular_count, guard_page_cases=guard_count,
                      null_length_functions=len(POSITIVE), negative_rtl_controls=len(NEGATIVE),
                      trusted_baseline_commit=TRUST_BASE, trusted_source_sha256=trusted,
                      source_sha256=before, clang_assembly_sha256=sha(clang_asm.read_bytes()))
        save()
        print(f'{regular_count} array cases and {guard_count} guard-page cases passed in all configurations')
    except BaseException as error:
        report.update(success=False, error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
