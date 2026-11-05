#!/usr/bin/env python3
"""Check aligned two-lane ArrayPair accesses and scalar cleanup on ARM64."""
import json
import os
from pathlib import Path
import re
import subprocess

from check_arraypair import (PACKED_ADD, ROOT, TRUSTED, assembly_body,
                             assembly_counts, paired_store_lanes, rtl_body, sha, snapshot)

ARTIFACTS = ROOT / 'perf/artifacts/arraypair-wide'
OUTPUT = ROOT / 'perf/results/arraypair-wide.json'
TRUST_BASE = '9222fcdceac9b6ae0d5375853423eaa83578bf76'
WIDE = ['add_global8', 'add_static16', 'add_page']
POINTER = 'add_pointer'
NEGATIVE = ['add_weak', 'add_odd', 'add_shifted', 'add_volatile', 'add_size']
MASK = 0xffffffff
EDGES = [MASK, 0, 0, MASK, 0x7fffffff, 0x80000000, 1, 0xaaaaaaaa]

C_SOURCE = r'''
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>

_Alignas(8) uint32_t global8[35];
static _Alignas(16) uint32_t static16[35];
_Alignas(16384) uint32_t page_array[8192];
uint32_t weak[35];
static _Alignas(8) uint32_t odd[35], shifted[36], size_array[35];
static _Alignas(8) volatile uint32_t volatile_array[35];

void add_global8(unsigned n) {
  for(unsigned i=0;i<n;++i) global8[i]+=1u;
}
void add_static16(unsigned n) {
  for(unsigned i=0;i<n;++i) static16[i]+=0x80000000u;
}
void add_page(unsigned n) {
  for(unsigned i=0;i<n;++i) page_array[i]+=7u;
}
void add_pointer(uint32_t *p,unsigned n) {
  for(unsigned i=0;i<n;++i) p[i]+=1u;
}
void add_weak(unsigned n) {
  for(unsigned i=0;i<n;++i) weak[i]+=1u;
}
void add_odd(unsigned n) {
  for(unsigned i=1;i<n;++i) odd[i]+=1u;
}
void add_shifted(unsigned n) {
  for(unsigned i=0;i<n;++i) shifted[i+1]+=1u;
}
void add_volatile(unsigned n) {
  for(unsigned i=0;i<n;++i) volatile_array[i]+=1u;
}
void add_size(size_t n) {
  for(size_t i=0;i<n;++i) size_array[i]+=1u;
}

static uint32_t sample(unsigned seed,unsigned i) {
  static const uint32_t edges[]={0xffffffffu,0u,0u,0xffffffffu,0x7fffffffu,
                                  0x80000000u,1u,0xaaaaaaaau};
  uint32_t mix=seed ? seed*0x9e3779b9u+i*0x85ebca6bu : 0u;
  return edges[(seed+i)%8u]^mix;
}
static void reset(volatile uint32_t *p,unsigned len,unsigned seed) {
  for(unsigned i=0;i<len;++i) p[i]=sample(seed,i);
}
static void dump(unsigned kind,unsigned n,unsigned seed,
                 const volatile uint32_t *p,unsigned len) {
  printf("%u %u %u",kind,n,seed);
  for(unsigned i=0;i<len;++i) printf(" %u",p[i]);
  putchar('\n');
}
#define RUN(kind, fn, array) do { \
  unsigned len=sizeof(array)/sizeof((array)[0]); \
  reset(array,len,seed); fn(n); dump(kind,n,seed,array,len); \
} while(0)

int main(void) {
  _Alignas(8) uint32_t stack[37];
  for(unsigned n=0;n<=35u;++n) for(unsigned seed=0;seed<5u;++seed) {
    RUN(0,add_global8,global8);
    RUN(1,add_static16,static16);
    RUN(2,add_weak,weak);
    RUN(3,add_odd,odd);
    RUN(4,add_shifted,shifted);
    RUN(5,add_volatile,volatile_array);
    RUN(6,add_size,size_array);
    reset(stack,37,seed);
    if((uintptr_t)(stack+1)%8u!=4u) return 2;
    add_pointer(stack+1,n);
    dump(7,n,seed,stack,37);
  }

  long page=sysconf(_SC_PAGESIZE);
  if(page<128 || page>16384 || 16384%page || (uintptr_t)page_array%page) return 3;
  unsigned cells=(unsigned)(page/sizeof(uint32_t));
  uint32_t *next=page_array+cells;
  /* Protect only the second page of this dedicated global object. */
  if(mprotect(next,(size_t)page,PROT_NONE)) return 4;
  for(unsigned tail=0;tail<2u;++tail) for(unsigned seed=0;seed<2u;++seed) {
    unsigned n=cells-tail;
    reset(page_array,cells,seed);
    add_page(n);
    dump(8,n,seed,page_array,cells);
  }
  for(unsigned n=1;n<18u;n+=2u) for(unsigned seed=0;seed<2u;++seed) {
    uint32_t *p=next-n;
    if((uintptr_t)p%8u!=4u) return 5;
    reset(p-1,n+1,seed);
    add_pointer(p,n);
    dump(9,n,seed,p-1,n+1);
  }
  if(mprotect(next,(size_t)page,PROT_READ|PROT_WRITE)) return 6;
  add_pointer(0,0);
  puts("zero length accepts null");
  return 0;
}
'''


def oracle():
    def case(kind, n, seed, size, start, count, increment):
        values = [EDGES[(seed+i) % len(EDGES)] ^
                  ((seed*0x9e3779b9 + i*0x85ebca6b) & MASK if seed else 0)
                  for i in range(size)]
        values[start:start+count] = [(value+increment) & MASK
                                     for value in values[start:start+count]]
        return ' '.join(map(str, [kind, n, seed, *values]))

    regular = []
    for n in range(36):
        for seed in range(5):
            layouts = [(35, 0, n, 1), (35, 0, n, 0x80000000), (35, 0, n, 1),
                       (35, 1, max(n-1, 0), 1), (36, 1, n, 1), (35, 0, n, 1),
                       (35, 0, n, 1), (37, 1, n, 1)]
            regular.extend(case(kind, n, seed, *layout) for kind, layout in enumerate(layouts))
    cells = os.sysconf('SC_PAGE_SIZE') // 4
    guarded_wide = [case(8, n, seed, cells, 0, n, 7)
                    for n in [cells, cells-1] for seed in range(2)]
    guarded_pointer = [case(9, n, seed, n+1, 1, n, 1)
                       for n in range(1, 18, 2) for seed in range(2)]
    data = '\n'.join([*regular, *guarded_wide, *guarded_pointer,
                      'zero length accepts null', '']).encode()
    return data, len(regular), len(guarded_wide), len(guarded_pointer)


def rtl_paths(body):
    # PrintRTL uses pc - 1 for the omitted successor.
    nodes = {int(pc): (op, int(succ) if succ else int(pc)-1)
             for pc, op, succ in re.findall(
                 r'^[ \t]*(\d+):[ \t]+([^\n]+)(?:\n[ \t]+goto (\d+))?', body, re.M)}
    guard = re.compile(r'if \(.+ (>=u 2|>u 1|<u 2|<=u 1)\) goto (\d+) else goto (\d+)')
    starts = [match.groups() for op, _ in nodes.values() if (match := guard.fullmatch(op))]
    if len(starts) != 1:
        raise ValueError('Expected a single two-element dispatch')

    def straight_line(pc):
        ops = []
        visited = set()
        while pc in nodes and pc not in visited:
            visited.add(pc)
            op, pc = nodes[pc]
            if op.startswith(('if (', 'return')):
                return ops
            jump = re.fullmatch(r'goto (\d+)', op)
            if jump:
                pc = int(jump[1])
            else:
                ops.append(op)
        raise ValueError('Path did not reach a branch or return')

    condition, yes, no = starts[0]
    pair, tail = (no, yes) if condition.startswith('<') else (yes, no)
    return straight_line(int(pair)), straight_line(int(tail))


def wide_accesses(body):
    pair, tail = rtl_paths(body)
    load = re.compile(r'(x\d+) = (int\d+)\[.+\]')
    store = re.compile(r'(int\d+)\[.+\] = (x\d+)')
    builtin = re.compile(r'(x\d+) = builtin "' + re.escape(PACKED_ADD) + r'"\((x\d+), x\d+\)')
    assignments = re.compile(r'(x\d+) = (.+)')
    provenance = {}
    flow = []
    for op in pair:
        if match := load.fullmatch(op):
            provenance[match[1]] = ('load', match[2])
            flow.append(provenance[match[1]])
        elif match := builtin.fullmatch(op):
            provenance[match[1]] = ('builtin', provenance.get(match[2]))
            flow.append(provenance[match[1]])
        elif match := store.fullmatch(op):
            flow.append(('store', match[1], provenance.get(match[2])))
        elif match := assignments.fullmatch(op):
            provenance[match[1]] = provenance.get(match[2])
    wide_load = ('load', 'int64')
    packed = ('builtin', wide_load)
    if flow != [wide_load, packed, ('store', 'int64', packed)]:
        raise ValueError('Expected one int64 load feeding NEON and one int64 store of its result')
    tail_loads = [match[2] for op in tail if (match := load.fullmatch(op))]
    tail_stores = [match[1] for op in tail if (match := store.fullmatch(op))]
    if tail_loads != ['int32'] or tail_stores != ['int32'] or any(PACKED_ADD in op for op in tail):
        raise ValueError('Expected one int32 load and store in the scalar cleanup')
    return {'pair_load': 'int64', 'pair_store': 'int64', 'packed_dataflow': True,
            'tail_load': 'int32', 'tail_store': 'int32'}


def static_assembly(assembly):
    return {**assembly_counts(assembly),
            'integer64_loads_nonstack': len(re.findall(
                r'^\s*(?:ldr|ldur)\s+x\d+,\s*\[x(?!29\b)\d+', assembly, re.M)),
            'integer64_stores_nonstack': len(re.findall(
                r'^\s*(?:str|stur)\s+x\d+,\s*\[x(?!29\b)\d+', assembly, re.M))}


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
        result = subprocess.run(command, cwd=ARTIFACTS, env=env, capture_output=True, timeout=180)
        (ARTIFACTS / (label + '.stdout')).write_bytes(result.stdout)
        (ARTIFACTS / (label + '.stderr')).write_bytes(result.stderr)
        result.check_returncode()
        return result.stdout

    save()
    try:
        files = sorted(str(path.relative_to(ROOT))
                       for path in (ROOT / 'cfrontend').glob('ArrayPair*.v'))
        files.extend(['perf/check_arraypair_wide.py', 'perf/check_arraypair.py',
                      'perf/experiment-profiles.json', 'driver/Compiler.v', 'compcert.ini', 'ccomp'])
        before = snapshot(files)
        trusted = snapshot(TRUSTED)
        baseline = {name: sha(subprocess.check_output(['git', 'show', TRUST_BASE+':'+name],
                                                     cwd=ROOT)) for name in TRUSTED}
        if trusted != baseline:
            raise RuntimeError('Existing semantics or NEON expansion changed')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-before')

        source = ARTIFACTS / 'array_pair_wide.c'
        source.write_text(C_SOURCE)
        if PACKED_ADD in C_SOURCE:
            raise RuntimeError('Expected scalar C fixtures')
        expected, regular, guarded_wide, guarded_pointer = oracle()
        clang = ['clang', '-O2', '-fno-inline']
        clang_asm, clang_exe = ARTIFACTS / 'clang.s', ARTIFACTS / 'clang.exe'
        run([*clang, '-S', source, '-o', clang_asm], 'clang-assembly')
        run([*clang, source, '-o', clang_exe], 'clang-build')
        if run([clang_exe], 'clang-run') != expected:
            raise RuntimeError('Clang output differs from the modular arithmetic oracle')
        report['clang_O2_assembly'] = {
            name: static_assembly(assembly_body(clang_asm.read_text(), name)) for name in WIDE}

        catalog = json.loads((ROOT / 'perf/experiment-profiles.json').read_text())
        configs = {'default': '', 'enabled': 'memory-neon',
                   'memory-loops': catalog['profiles']['memory-loops']}
        baseline_rtl = {}
        rtl_dump = ARTIFACTS / 'array_pair_wide.rtl.0'
        for profile, flags in configs.items():
            env = os.environ.copy()
            env.update(COMPCERT_CONFIG=str(ROOT / 'compcert.ini'), COMPCERT_EXPERIMENTS=flags)
            env.pop('COMPCERT_EXPERIMENT_TRACE', None)
            compiler = [ROOT / 'ccomp', '-stdlib', ROOT / 'runtime', '-fno-inline']
            asm, exe = ARTIFACTS / (profile + '.s'), ARTIFACTS / (profile + '.exe')
            rtl_dump.unlink(missing_ok=True)
            run([*compiler, '-drtl', '-S', source, '-o', asm], profile + '-assembly', env)
            rtl = rtl_dump.read_text()
            (ARTIFACTS / (profile + '.rtl.0')).write_text(rtl)
            run([*compiler, source, '-o', exe], profile + '-build', env)
            actual = run([exe], profile + '-run', env)
            if actual != expected:
                raise RuntimeError(profile + ': output differs from Clang and the oracle')
            enabled = 'memory-neon' in flags.split(',')
            functions = {}
            asm_text = asm.read_text()
            for function in [*WIDE, POINTER, *NEGATIVE]:
                body = rtl_body('\n'+rtl, function)
                wide = enabled and function in WIDE
                paired = wide or (enabled and function == POINTER)
                counts = static_assembly(assembly_body(asm_text, function))
                if body.count(PACKED_ADD) != int(paired):
                    raise RuntimeError(profile + ': unexpected packed add count for ' + function)
                if paired and not counts['neon_add_2s']:
                    raise RuntimeError(profile + ': missing NEON add for ' + function)
                if not wide and 'int64[' in body:
                    raise RuntimeError(profile + ': unexpected int64 access in ' + function)
                detail = {}
                if wide:
                    try:
                        detail = wide_accesses(body)
                    except ValueError as error:
                        raise RuntimeError(profile + ': ' + function + ': ' + str(error)) from error
                    if not counts['integer64_loads_nonstack'] or not counts['integer64_stores_nonstack']:
                        raise RuntimeError(profile + ': missing ARM64 wide accesses in ' + function)
                elif paired:
                    if paired_store_lanes(body) != ['low', 'high']:
                        raise RuntimeError(profile + ': scalar stores lost the packed result')
                    detail = {'rtl0_paired_store_lanes': ['low', 'high']}
                if profile == 'default':
                    baseline_rtl[function] = body
                elif function in NEGATIVE and body != baseline_rtl[function]:
                    raise RuntimeError(profile + ': unsupported function changed: ' + function)
                functions[function] = {'rtl0_packed_add_calls': int(paired), **detail, **counts}
            report['c_configurations'][profile] = {'flags': flags, 'correctness_pass': True,
                'stdout_sha256': sha(actual), 'assembly_sha256': sha(asm.read_bytes()),
                'functions': functions}
            save()
        if snapshot(files) != before or snapshot(TRUSTED) != trusted:
            raise RuntimeError('Compiler, verifier or semantics changed during verification')
        run(['python3', ROOT / 'perf/guard.py'], 'guard-after')
        report.update(success=True, regular_cases=regular, aligned_guard_cases=guarded_wide,
                      unaligned_guard_cases=guarded_pointer, negative_rtl_controls=len(NEGATIVE),
                      trusted_baseline_commit=TRUST_BASE, trusted_source_sha256=trusted,
                      source_sha256=before, clang_assembly_sha256=sha(clang_asm.read_bytes()))
        save()
        print(f'{regular} array cases and {guarded_wide+guarded_pointer} guard-page cases passed')
    except BaseException as error:
        report.update(success=False, error=str(error))
        save()
        raise


if __name__ == '__main__':
    main()
