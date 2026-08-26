#!/usr/bin/env python3
"""Fail when a full declaration name is declared in more than one module.

## Why this is a gate

The Lean 4.33 module system's import merge REJECTS a name declared in two
modules that are both in one import closure:

    import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq failed,
    environment already contains
    'EvmAsm.Evm64.divK_mulsub_correction_addback_beq_v4_spec_within_noNop'
    from EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqV4NoNop

Pre-module Lean tolerated the collision, so the tree accumulated them silently.
Two turned up during the migration (that one, and three theorems in
`Exp/Compose/SavedBitBoundaryEpilogueBase.lean` that `SavedBitBoundarySeq.lean`
also declares) -- each an identical STATEMENT proved twice with different tactic
scripts. Both were latent defects on `main`, not migration damage; see
MODULES.md 5d.

A duplicate that does not currently collide is still worth failing on. It means
a theorem was proved twice, it costs build time and review attention, and it
becomes a hard build error the moment some new module imports both.

## The baseline, and why it is a ceiling and not a floor

`BASELINE` pins the duplicates that exist today. The gate fails if a NEW one
appears; fixing an existing one and lowering `BASELINE` is always welcome. Note
this is a count that should only ever fall, so pinning it raw is safe -- unlike
a metric that grows with the repo, which would turn `main` red on unrelated
work.

`--list` prints the current duplicates and exits 0.
"""
import argparse
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
KW = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive)"
DECL = re.compile(
    rf"^(private )?(?:noncomputable )?(?:partial )?(?:meta )?(?:unsafe )?{KW} "
    rf"([A-Za-z0-9_.'?!]+)")
NS_OPEN = re.compile(r"^namespace ([A-Za-z0-9_.']+)")
NS_END = re.compile(r"^end\b")

# Duplicates present when this gate was written. Each is a theorem proved twice.
# Lower this number when you remove one; never raise it.
BASELINE = 9


def duplicates() -> dict[str, set[str]]:
    """Full name -> the modules declaring it, for names declared more than once.

    `private` declarations are skipped: they are mangled per module, so two of
    them never collide (MODULES.md 5a hazard 2 is about what happens when one
    stops being private, which is a different check).
    """
    full: dict[str, set[str]] = collections.defaultdict(set)
    for f in sorted((ROOT / "EvmAsm").rglob("*.lean")):
        stack: list[str] = []
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            m = NS_OPEN.match(line)
            if m:
                stack.append(m.group(1))
                continue
            if NS_END.match(line):
                if stack:
                    stack.pop()
                continue
            d = DECL.match(line)
            if d and not d.group(1):
                full[".".join(stack + [d.group(2)])].add(
                    str(f.relative_to(ROOT)))
    return {k: v for k, v in full.items() if len(v) > 1}


def self_test() -> int:
    """Plant a real duplicate in the tree and demand the gate reports it.

    A gate that scans source and prints a count can report a clean tree because
    its own matcher missed the thing it was written to find. `check-layering.sh`
    did exactly that before #12793 -- printed "(clean)" with the violation
    standing. So the pass here is not "the count came out right", it is "the
    count RISES when a duplicate is planted and falls back when it is removed".
    """
    fail = []
    base = len(duplicates())

    # 1. A duplicate the gate must SEE: same bare name, same namespace stack,
    #    two different files.
    victim = ROOT / "EvmAsm" / "_dupcheck_selftest.lean"
    victim.write_text(
        "namespace EvmAsm.Codegen.Proofs\n"
        "theorem bytesRegion_window_unfocus : True := trivial\n"
        "end EvmAsm.Codegen.Proofs\n", encoding="utf-8")
    try:
        seen = duplicates()
        planted = "EvmAsm.Codegen.Proofs.bytesRegion_window_unfocus"
        if str(victim.relative_to(ROOT)) not in seen.get(planted, set()):
            fail.append("  planted duplicate was NOT detected")
    finally:
        victim.unlink()

    # 2. NEGATIVE CONTROL: a name that is NOT a duplicate must not be reported,
    #    and removing the plant must restore the original count exactly.
    unique = ROOT / "EvmAsm" / "_dupcheck_selftest2.lean"
    unique.write_text(
        "namespace EvmAsm.Codegen.Proofs\n"
        "theorem _dupcheck_a_name_nothing_else_uses : True := trivial\n"
        "end EvmAsm.Codegen.Proofs\n", encoding="utf-8")
    try:
        after = duplicates()
        if len(after) != base:
            fail.append(f"  a UNIQUE name changed the count ({base} -> {len(after)})")
    finally:
        unique.unlink()

    # 3. NEGATIVE CONTROL: two PRIVATE declarations of one name do not collide
    #    (they are mangled per module), so they must not be reported.
    priv = ROOT / "EvmAsm" / "_dupcheck_selftest3.lean"
    priv.write_text(
        "namespace EvmAsm.Codegen.Proofs\n"
        "private theorem bytesRegion_window_unfocus : True := trivial\n"
        "end EvmAsm.Codegen.Proofs\n", encoding="utf-8")
    try:
        if len(duplicates()) != base:
            fail.append("  a PRIVATE declaration was counted as a duplicate")
    finally:
        priv.unlink()

    if len(duplicates()) != base:
        fail.append("  self-test did not restore the tree")
    if fail:
        print("check-duplicate-decls --self-test: FAILED")
        for x in fail:
            print(x)
        return 1
    print("check-duplicate-decls --self-test: OK (1 planted duplicate detected, "
          "2 negative controls: a unique name and a private duplicate)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true",
                    help="print the duplicates and exit 0")
    ap.add_argument("--self-test", action="store_true",
                    help="plant a duplicate and demand the gate reports it")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    dups = duplicates()
    for name in sorted(dups):
        print(f"  {name}")
        for f in sorted(dups[name]):
            print(f"      {f}")
    n = len(dups)
    if args.list:
        print(f"\n{n} duplicated full name(s)")
        return 0
    if n > BASELINE:
        print(f"\ncheck-duplicate-decls: FAIL — {n} duplicated full name(s), "
              f"baseline {BASELINE}.\n"
              f"A name declared in two modules is a hard build error under the "
              f"module system\nas soon as one import closure contains both "
              f"(MODULES.md 5d). Diff the two\ndeclarations: if the STATEMENTS "
              f"match, delete one and leave its module as a\n`public import` "
              f"re-export so its importers do not change.")
        return 1
    if n < BASELINE:
        print(f"\ncheck-duplicate-decls: {n} duplicate(s), below the baseline "
              f"of {BASELINE}.\nPlease lower BASELINE in "
              f"scripts/check-duplicate-decls.py to {n}.")
        return 1
    print(f"\ncheck-duplicate-decls: OK — {n} duplicated full name(s), "
          f"at the pinned baseline.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
