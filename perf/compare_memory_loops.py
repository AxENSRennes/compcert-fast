#!/usr/bin/env python3
"""Reproduce static comparisons for the new memory and loop transformations."""
from pathlib import Path
import subprocess
import sys

from check_loopfusion import C_SOURCE as FUSION
from check_loopinterchange import C_SOURCE as RECTANGLE
from check_memory_loops import SOURCE as MEMORY
from check_memoryneon import C_SOURCE as NEON_MEMORY
from check_pointerneon import C_SOURCE as POINTER_MEMORY
from check_autopair import C_SOURCE as AUTO_PAIRS

ROOT = Path(__file__).resolve().parents[1]


def main():
    artifacts = ROOT / 'perf/artifacts/memory-assembly'
    artifacts.mkdir(parents=True, exist_ok=True)
    source = artifacts / 'source.c'
    source.write_text('\n'.join(unit.split('\nint main(', 1)[0] for unit in (MEMORY, FUSION, RECTANGLE, NEON_MEMORY, POINTER_MEMORY, AUTO_PAIRS)))
    command = [sys.executable, str(ROOT / 'perf/compare_assembly.py'), '--source', str(source),
               '--output', str(ROOT / 'perf/results/memory-assembly.json'), '--artifacts', str(artifacts)]
    for name, flags in [('memory', 'memory-vector'), ('fusion', 'loop-fusion'),
                        ('interchange', 'loop-interchange'), ('tile2d', 'loop-tile2d'), ('tile', 'loop-tile'),
                        ('memory-neon', 'memory-neon')]:
        command.extend(['--experiments', name + '=' + flags])
    subprocess.run(command, cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
