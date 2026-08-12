#!/usr/bin/env python3
"""check-fixture-reloc-targets.py — GH #12145: callee-name gate for MANIFEST
fixtures.

For every MANIFEST row with a registered fixture and a lean RelocTable,
assemble the fixture and compare its R_RISCV relocation table (UND-class
symbol per instruction index, byte offset / 4) against the lean `_relocs`
entry at the same index. No guest addresses needed, so it covers exactly the
probe-only population that check-asm-to-program's link leg cannot see: leg
(a) compares .text bytes, and unlinked a jal to ANY undefined symbol encodes
identically — the callee name lives only in the relocation table, which
assemble_cmp never reads.

Skips (representation-equivalent, not name divergence): *ABS*
assembler-resolved absolutes, .L* local labels, local data labels.

Exit 1 with one line per mismatch (module / function / index / fixture
symbol / lean symbol), assembly failure, missing fixture, or shortfall from
the manifest's expected reloc-bearing population. Verified non-vacuous by
injection in both directions (GH #12145 thread): flipping a fixture jal target
and flipping a lean relocs entry each change the lane verdict to failure;
restoring returns it to success.
"""
import re, subprocess, sys, os
from tempfile import TemporaryDirectory
from pathlib import Path

ROOT = Path(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FIX = ROOT / 'scripts/asm-fixtures'

def split_top(s):
    parts, buf, d = [], [], 0
    for ch in s:
        if ch in '([': d += 1
        if ch in ')]': d -= 1
        if ch == ',' and d == 0:
            parts.append(''.join(buf).strip()); buf = []
        else: buf.append(ch)
    if ''.join(buf).strip(): parts.append(''.join(buf).strip())
    return parts

def parse_relocs(text, name):
    m = re.search(r'def\s+' + name + r'\s*:\s*RelocTable\s*:=\s*\[', text)
    if not m: return {}
    i = m.end(); d = 1; out = []
    while i < len(text) and d:
        if text[i] == '[': d += 1
        elif text[i] == ']': d -= 1
        if d: out.append(text[i])
        i += 1
    rel = {}
    for el in split_top(''.join(out)):
        em = re.match(r'\(\s*(\d+)\s*,\s*\.(jal|la|jalr)\s+\S+\s+"([^"]+)"', el)
        if em: rel[int(em.group(1))] = em.group(3)
    return rel

def prog_block(text, name):
    m = re.search(r'def\s+' + name + r'\s*:\s*(?:Program|\w+)\s*:=\s*\[', text)
    if not m: return None
    i = m.end(); d = 1; out = []
    while i < len(text) and d:
        if text[i] == '[': d += 1
        elif text[i] == ']': d -= 1
        if d: out.append(text[i])
        i += 1
    return ''.join(out)

def lean_relocs_for(text, fn):
    # find <stem>_relocs for the Function named fn
    m = re.search(r'def\s+' + fn + r'\s*:\s*String\s*:=', text)
    if not m: return None, None
    tail = text[m.start():m.start()+4000]
    pm = re.search(r'emitProgramR\s+(\w+)\s+(\w+)', tail)
    if not pm: return None, None
    return pm.group(1), parse_relocs(text, pm.group(2))

def fixture_relocs(path):
    # Do not use a shared /tmp object: concurrent agents and other users may
    # own it, turning every fixture into an uncounted assembly failure.
    with TemporaryDirectory(prefix='fixture-reloc-') as td:
        o = os.path.join(td, 'fixture.o')
        r = subprocess.run(
            ['riscv64-unknown-elf-as', '-o', o, str(path)],
            capture_output=True, text=True)
        if r.returncode != 0:
            return None, None, 'ASSEMBLE-FAIL'
        rr = subprocess.run(
            ['riscv64-unknown-elf-objdump', '-r', o],
            capture_output=True, text=True)
        tt = subprocess.run(
            ['riscv64-unknown-elf-objdump', '-t', o],
            capture_output=True, text=True)
        rel = {}
        for ln in rr.stdout.splitlines():
            mm = re.match(r'^([0-9a-f]+)\s+\S+\s+(\S+)$', ln.strip())
            if mm:
                idx = int(mm.group(1), 16) // 4
                sym = mm.group(2)
                if sym.endswith('-0x0') or sym == '.text': continue
                rel[idx] = sym
        und = set()
        defined = set()
        for ln in tt.stdout.splitlines():
            if '*UND*' in ln:
                und.add(ln.split()[-1])
            elif re.search(r'\s+(g|l)\s+', ln):
                parts = ln.split()
                if parts and not parts[-1].startswith('.'):
                    defined.add(parts[-1])
        return rel, (und, defined), None

def main():
    mismatches, assembly_failures, missing_fixtures = [], [], []
    checked, expected, skip = 0, 0, 0
    for ln in open(FIX / 'MANIFEST.tsv'):
        if ln.startswith('#') or not ln.strip(): continue
        fn, rel = ln.rstrip('\n').split('\t')[:2]
        lean = ROOT / rel
        if not lean.is_file(): continue
        text = lean.read_text()
        prog, lrel = lean_relocs_for(text, fn)
        if not lrel:
            skip += 1; continue  # no reloc-bearing conversion
        expected += 1
        fs = FIX / (fn + '.s')
        if not fs.is_file():
            missing_fixtures.append(fn)
            continue
        frel, symtabs, err = fixture_relocs(fs)
        if frel is None:
            assembly_failures.append((fn, err))
            print('ERR', fn, err)
            continue
        und, defined = symtabs
        checked += 1
        for idx in sorted(set(frel) | set(lrel)):
            fsym, lsym = frel.get(idx), lrel.get(idx)
            if fsym is not None and fsym in und and fsym != lsym:
                mismatches.append((fn, idx, fsym, lsym))
            elif fsym is None and lsym is not None and lsym in und:
                mismatches.append((fn, idx, fsym, lsym))
    print(f'checked {checked} of {expected} reloc-bearing fixture functions ({skip} no relocs)')
    print(f'assembly failures: {len(assembly_failures)}')
    print(f'missing fixtures: {len(missing_fixtures)}')
    print(f'mismatched reloc-target sites: {len(mismatches)}')
    from collections import Counter
    print(Counter(fn for fn, _, _, _ in mismatches).most_common())
    for fn, idx, fsym, lsym in mismatches[:400]:
        print(f'  {fn}:{idx}: fixture={fsym} lean={lsym}')
    for fn, err in assembly_failures:
        print(f'  assembly-failure {fn}: {err}')
    for fn in missing_fixtures:
        print(f'  missing-fixture {fn}')
    if checked < expected:
        print(f'ERROR checked {checked} reloc-bearing fixtures, expected at least {expected}')
    if mismatches or assembly_failures or missing_fixtures or checked < expected:
        sys.exit(1)

main()
