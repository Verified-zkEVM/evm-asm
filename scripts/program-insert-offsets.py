#!/usr/bin/env python3
"""Compute the offset edits required to INSERT an instruction into a verified `Program`.

Inserting one instruction into a `Program` literal in `EvmAsm/Codegen/Programs/*.lean`
is not a one-line change. Four distinct things move, and getting any of them wrong
produces assembly that LINKS CLEANLY while jumping into the middle of an
instruction -- silent corruption that no build, diff or `#guard` will catch:

  1. every `GuestAddrs.<routine> + N` annotation with `N >= insertion_pc` (+4);
  2. every RELATIVE branch whose SPAN CROSSES the insertion point -- measured on
     real routines: 5 in `extcodecopy_at_header_state_root`, 2 in
     `code_at_header_state_root`, 4 in `extcodesize_at_header_state_root`;
  3. the reloc side-table, which is indexed by INSTRUCTION NUMBER, so entries at or
     after `insertion_pc / 4` shift by one;
  4. the `#guard <camel>_prog.length` pin.

PREFER THE CONVERTER. If the routine has an asm fixture
(`scripts/asm-fixtures/<Func>.s`), edit the FIXTURE and run
`asm_to_program.py rewrite --file <lean> --funcs <Func>`: it computes all four
itself. This script exists for the cases where that is not available, and as an
independent check on it -- run both and compare, which is how (2) and (3) above were
first found. GH #10619.

Usage:
    scripts/program-insert-offsets.py <lean-file> <routine-label> <insertion-pc>

`insertion-pc` is the byte offset (from the routine's entry) of the instruction the
new one goes BEFORE -- i.e. the `+ N` in that instruction's own annotation. Prints
the branch adjustments, the annotation count, and the reloc index cutoff. Read-only:
it never edits the file.
"""
import re
import sys


def main() -> int:
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    path, routine, ins_pc = sys.argv[1], sys.argv[2], int(sys.argv[3])
    lines = open(path).read().splitlines()

    # Anchor on the annotation that names this PC, then index by 4 bytes/line: a
    # Program literal is one instruction per line.
    anchor = [i for i, l in enumerate(lines)
              if re.search(r'GuestAddrs\.' + re.escape(routine) + r' \+ ' + str(ins_pc) + r'\)', l)]
    if not anchor:
        sys.exit(f"no annotation `GuestAddrs.{routine} + {ins_pc}` in {path}")
    jal_i = anchor[-1]
    start, end = jal_i, jal_i
    while re.match(r'\s*\.[A-Z]', lines[start - 1]):
        start -= 1
    while end + 1 < len(lines) and re.match(r'\s*\.[A-Z]', lines[end + 1]):
        end += 1

    def pc(i: int) -> int:
        return ins_pc + (i - jal_i) * 4

    print(f"routine {routine}: instruction lines {start+1}..{end+1}, "
          f"PCs {pc(start)}..{pc(end)}; inserting at PC {ins_pc}\n")

    crossing = []
    for i in range(start, end + 1):
        m = re.search(r'\.(JAL|BEQ|BNE|BLT|BGE|BLTU|BGEU)\s+\.x\d+(?:\s+\.x\d+)?\s+\((-?\d+)\s*:', lines[i])
        if not m:
            continue
        n = int(m.group(2))
        here, tgt = pc(i), pc(i) + n
        if (here < ins_pc <= tgt) or (tgt < ins_pc <= here):
            delta = 4 if here < ins_pc else -4
            crossing.append((i + 1, m.group(1), n, n + delta))

    print(f"(2) relative branches SPANNING the insertion point: {len(crossing)}")
    for ln, op, n, n2 in crossing:
        print(f"      line {ln}: {op} {n} -> {n2}")
    ann = sum(len([x for x in re.findall(r'GuestAddrs\.' + re.escape(routine) + r' \+ (\d+)', l)
                   if int(x) >= ins_pc]) for l in lines)
    print(f"(1) `+ N` annotations with N >= {ins_pc} to bump by 4: {ann}")
    print(f"(3) reloc entries with index >= {ins_pc // 4} shift by one")
    print(f"(4) bump the `_prog.length` #guard by one")
    print("\nAlso: do NOT add inline comments inside the generated literal -- the "
          "byte-tie's\nsource check requires the converter's block verbatim.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
