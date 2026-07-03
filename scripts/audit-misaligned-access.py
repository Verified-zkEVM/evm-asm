#!/usr/bin/env python3
"""
audit-misaligned-access.py — mechanical misaligned wide-access audit for the
emitted stateless guest.

Motivation (bead evm-asm-4ch8f.7): the verified RV64 semantics traps on
misaligned LD/SD/LW/LWU/FLW/FLD/FSW/FSD (isValidMemAccess / isValidDwordAccess
require isAligned4/8, EvmAsm/Rv64/Basic.lean:307-311) but ziskemu tolerates
them.  Any routine that issues a wide memory access whose *absolute* effective
address is not 4-/8-byte aligned cannot be verified as-is: `step` returns
`none` in the Lean interpreter.  The SSZ container base is INPUT_BASE+18 =
0x40000012 (2 mod 4), so wide loads on the SSZ offset table land on odd
alignments.

This scanner runs a per-routine, straight-line abstract interpretation over the
emitted `.s` and classifies every wide memory op into:

  CONFIRMED  — effective address is a *statically known constant* and is NOT
               correctly aligned for its width.  These are hard model traps.
  ALIGNED    — effective address statically known and correctly aligned.
  INPUT_DEP  — base register is provably derived from the INPUT region
               (0x40000000) but the offset is data-dependent (came from a
               memory load).  Alignment depends on input; needs per-routine
               reasoning.  These are the SSZ/RLP-cursor candidates.
  UNKNOWN    — base not statically tracked (e.g. sp-relative, callee args in
               a0.., or clobbered across a label).  Not flagged.

Abstract domain per register (within a straight-line run):
  ('const', n)          — known concrete value n
  ('input', off, exact) — INPUT_BASE + off; exact=True if off is a known
                          constant, False if off includes a data-dependent term
  None                  — unknown

Register knowledge is reset at every label (conservative join): control-flow
merges could bring any value, so we do not propagate across basic-block joins.
This under-reports (misses cross-block constants) but never mis-reports a
CONFIRMED trap, since a CONFIRMED requires a fully-known constant address
reached along a straight-line path.
"""

import re
import sys

INPUT_BASE = 0x40000000
INPUT_END  = 0x40002000
RAM_START  = 0xa0000000

# width in bytes for each wide (alignment-checked) memory mnemonic
WIDE = {
    'lw': 4, 'lwu': 4, 'sw': 4, 'flw': 4, 'fsw': 4,
    'ld': 8, 'sd': 8, 'fld': 8, 'fsd': 8,
}

MEM_RE = re.compile(r'^\s*(\w+)\s+\S+\s*,\s*(-?\d+)\s*\(\s*(\w+)\s*\)')
LABEL_RE = re.compile(r'^([A-Za-z_.][\w.]*)\s*:')
# instruction: mnemonic then operands
INSN_RE = re.compile(r'^\s*(\w+)\s+(.*)$')


def signed(imm):
    return int(imm)


def scan(path):
    regs = {}          # name -> abstract value
    cur_routine = '_start'
    findings = []      # (lineno, routine, mnem, off, base, kind, addr_or_note)

    def reset():
        regs.clear()

    with open(path) as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.split('#')[0].split('//')[0]
            # a line can carry `label: insn; insn` (see .Lsg_fail_* lines)
            for piece in line.split(';'):
                piece = piece.strip()
                if not piece:
                    continue
                m = LABEL_RE.match(piece)
                rest = piece
                if m:
                    lbl = m.group(1)
                    # global (routine) label -> new routine boundary
                    if not lbl.startswith('.'):
                        cur_routine = lbl
                    reset()  # any label is a potential join point
                    rest = piece[m.end():].strip()
                    if not rest:
                        continue
                process(rest, lineno, cur_routine, regs, findings)
    return findings


def process(insn, lineno, routine, regs, findings):
    # First, classify a wide memory op (uses base BEFORE any update)
    mm = MEM_RE.match(insn)
    im = INSN_RE.match(insn)
    mnem = im.group(1) if im else None

    if mm and mm.group(1) in WIDE:
        mnem, off_s, base = mm.group(1), mm.group(2), mm.group(3)
        width = WIDE[mnem]
        off = signed(off_s)
        bv = regs.get(base)
        kind, note = classify(bv, off, width)
        if kind in ('CONFIRMED', 'INPUT_DEP'):
            findings.append((lineno, routine, mnem, off, base, kind, note))

    # Then update register state for the destination (abstract transfer).
    transfer(insn, mnem, regs)


def classify(bv, off, width):
    if bv is None:
        return ('UNKNOWN', '')
    tag = bv[0]
    if tag == 'const':
        addr = (bv[1] + off) & ((1 << 64) - 1)
        if width == 8:
            aligned = (addr % 8 == 0)
        else:
            aligned = (addr % 4 == 0)
        if aligned:
            return ('ALIGNED', hex(addr))
        return ('CONFIRMED', hex(addr))
    if tag == 'input':
        base_off, exact = bv[1], bv[2]
        if exact:
            addr = (INPUT_BASE + base_off + off) & ((1 << 64) - 1)
            aligned = (addr % 8 == 0) if width == 8 else (addr % 4 == 0)
            return (('ALIGNED', hex(addr)) if aligned
                    else ('CONFIRMED', hex(addr)))
        # data-dependent offset from the input region
        return ('INPUT_DEP', f'INPUT_BASE+dep+{off}')
    return ('UNKNOWN', '')


def parse_ops(s):
    return [o.strip() for o in s.split(',')]


def mk_const(v):
    """Build an abstract value from a concrete 64-bit constant, folding any
    value inside the INPUT region into the ('input', off, exact=True) tag so
    that later `add`s with data-dependent addends propagate the region."""
    v &= (1 << 64) - 1
    if INPUT_BASE <= v < INPUT_END:
        return ('input', v - INPUT_BASE, True)
    return ('const', v)


def transfer(insn, mnem, regs):
    im = INSN_RE.match(insn)
    if not im:
        return
    ops = parse_ops(im.group(2))

    def clobber(rd):
        regs.pop(rd, None)

    if mnem in ('li',) and len(ops) == 2:
        rd = ops[0]
        try:
            regs[rd] = mk_const(int(ops[1], 0))
        except ValueError:
            clobber(rd)
        return
    if mnem in ('lui',) and len(ops) == 2:
        rd = ops[0]
        try:
            regs[rd] = mk_const(int(ops[1], 0) << 12)
        except ValueError:
            clobber(rd)
        return
    if mnem in ('addi', 'add') and len(ops) == 3:
        rd, rs, third = ops
        # addi rd, x0, imm  == li
        if rs == 'x0' and mnem == 'addi':
            try:
                regs[rd] = mk_const(int(third, 0))
            except ValueError:
                clobber(rd)
            return
        bv = regs.get(rs)
        if mnem == 'addi':
            try:
                imm = int(third, 0)
            except ValueError:
                clobber(rd); return
            if bv is None:
                clobber(rd)
            elif bv[0] == 'const':
                regs[rd] = mk_const(bv[1] + imm)
            elif bv[0] == 'input':
                regs[rd] = ('input', bv[1] + imm, bv[2])
            return
        # plain add rd, rs, rt
        bt = regs.get(third)
        def is_input(x): return x is not None and x[0] == 'input'
        def is_const(x): return x is not None and x[0] == 'const'
        if is_const(bv) and is_const(bt):
            regs[rd] = mk_const(bv[1] + bt[1])
        elif is_input(bv) and is_input(bt):
            # base + base: keep one base, offsets add, data-dependent unless both exact
            regs[rd] = ('input', bv[1] + bt[1], bv[2] and bt[2])
        elif is_input(bv):
            # input-base + something; exact only if addend is a known const
            if is_const(bt):
                regs[rd] = ('input', bv[1] + bt[1], bv[2])
            else:
                regs[rd] = ('input', bv[1], False)  # data-dependent offset
        elif is_input(bt):
            if is_const(bv):
                regs[rd] = ('input', bt[1] + bv[1], bt[2])
            else:
                regs[rd] = ('input', bt[1], False)
        else:
            clobber(rd)
        return
    # any other instruction: destination (first operand) becomes unknown.
    # Covers loads (value is data-dependent), shifts, or/and, sub, mul, etc.
    if ops:
        rd = ops[0]
        # register-writing forms only; branches/jumps/stores have no rd we track
        if mnem in ('sb', 'sh', 'sw', 'sd', 'fsw', 'fsd',
                    'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu',
                    'j', 'jal', 'jalr', 'ret', 'ecall', 'nop'):
            # jal/jalr write ra/rd; be conservative and clobber the first op if
            # it looks like a register
            if mnem in ('jal', 'jalr') and re.match(r'^x\d+$|^[a-z]+\d*$', rd):
                clobber(rd)
            return
        if re.match(r'^x\d+$', rd) or rd in (
            'ra','sp','gp','tp','a0','a1','a2','a3','a4','a5','a6','a7',
            't0','t1','t2','t3','t4','t5','t6','s0','s1','s2','s3','s4',
            's5','s6','s7','s8','s9','s10','s11','fp'):
            clobber(rd)


def main():
    total = {}
    for path in sys.argv[1:]:
        findings = scan(path)
        confirmed = [f for f in findings if f[5] == 'CONFIRMED']
        input_dep = [f for f in findings if f[5] == 'INPUT_DEP']
        # coverage: total wide ops seen (context for what the scan can/can't classify)
        total_wide = 0
        for raw in open(path):
            for piece in raw.split('#')[0].split(';'):
                mm = MEM_RE.match(piece.strip())
                if mm and mm.group(1) in WIDE:
                    total_wide += 1
        print(f'=== {path} ===')
        print(f'  total wide (4/8-byte) mem ops: {total_wide} '
              f'(bases with statically-known alignment are classified below; '
              f'the rest are UNKNOWN — sp-/heap-/arg-relative)')
        print(f'  CONFIRMED misaligned wide accesses (static traps): {len(confirmed)}')
        print(f'  INPUT_DEP wide accesses (data-dependent alignment): {len(input_dep)}')
        # per-routine confirmed breakdown
        byr = {}
        for (ln, r, mn, off, base, kind, note) in confirmed:
            byr.setdefault(r, []).append((ln, mn, off, base, note))
        if byr:
            print('  --- CONFIRMED by routine ---')
            for r in sorted(byr, key=lambda k: -len(byr[k])):
                print(f'    {r}: {len(byr[r])}')
                for (ln, mn, off, base, note) in byr[r][:8]:
                    print(f'        L{ln}: {mn} {off}({base})  -> addr {note}')
        # per-routine input_dep breakdown (top offenders)
        byr2 = {}
        for (ln, r, mn, off, base, kind, note) in input_dep:
            byr2.setdefault(r, 0)
            byr2[r] += 1
        if byr2:
            print('  --- INPUT_DEP by routine (top 25) ---')
            for r in sorted(byr2, key=lambda k: -byr2[k])[:25]:
                print(f'    {r}: {byr2[r]}')
        total[path] = (len(confirmed), len(input_dep))
    print('=== TOTAL ===')
    for p, (c, d) in total.items():
        print(f'  {p}: {c} confirmed, {d} input-dep')


if __name__ == '__main__':
    main()
