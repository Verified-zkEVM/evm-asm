#!/usr/bin/env python3
"""gen-port-kit.py — scaffold a verified-port skeleton for one guest routine.

Usage:
    python3 scripts/gen-port-kit.py <entry_label> \
        [--out EvmAsm/Stateless/<Area>/<Routine>SAsm.lean] \
        [--namespace EvmAsm.Stateless.<Area>]

Given the asm entry label of a guest routine (e.g. `bloom_eq`), locates its
`<camel>Function : String` def under the Codegen scan dirs, converts the body
to a `Program` literal via scripts/asm_to_program.py (byte-identity gate
included), and writes a ready-to-fill port skeleton:

  * header doc with the playbook checklist + EEST A/B command block,
  * the converted `Program` (verification view),
  * `#guard` pins (length),
  * a commented SAsm `Fn` + spec template with named pre/post holes.

If the routine cannot be converted mechanically (composite, caller-local
fragment, …) the skeleton embeds the raw asm in a comment and says which
exemplar to copy instead (see docs/agents/port-playbook.md Step 0).

The skeleton is NOT built automatically — filling the spec is the port work.
Acceptance: scripts/port-check.sh <out-file>.
"""

import argparse
import os
import re
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(SCRIPTS)
sys.path.insert(0, SCRIPTS)

atp = __import__("asm_to_program")


def find_function_def(camel_fn):
    """Return (relpath, text) of the Lean file defining `<camel_fn> : String`."""
    pat = re.compile(r"def\s+" + re.escape(camel_fn) + r"\s*:\s*String\s*:=")
    for rd in atp.SCAN_DIRS:
        d = os.path.join(REPO, rd)
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(d, fn)
            text = open(path).read()
            if pat.search(text):
                return os.path.relpath(path, REPO), text
    return None, None


TEMPLATE_SPEC = """
-- ============================================================================
-- TODO(port): the SAsm function + spec.
--
-- 1. Rebuild the routine as an SAsm `Fn` (structured control flow) whose
--    flattening equals `{prog_name}` — or, for a straight-line leaf, verify
--    `{prog_name}` directly with a cpsTripleWithin block spec.
-- 2. State the contract (playbook Step 2):
--    * pre  = the asm's implicit assumptions (offsets in range, alignment),
--      ghost input values via leByte/leU32/leU64 (ChainIdSAsm pattern);
--    * post = the ABI registers downstream code documents + written windows.
-- 3. Prove via `vcgen`; close VCs with the playbook Step 3 closers.
-- 4. Emit + swap (playbook Step 4) and run `scripts/port-check.sh` on this
--    file; EEST A/B if the emitted guest changed.
--
-- Exemplar for your routine class: see the table in
-- docs/agents/port-playbook.md Step 0.
-- ============================================================================
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("entry", help="asm entry label, e.g. bloom_eq")
    ap.add_argument("--out", help="output .lean path (default: print to stdout)")
    ap.add_argument("--namespace", dest="ns", default="EvmAsm.Stateless.Ports")
    args = ap.parse_args()

    camel = atp.lean_camel(args.entry)
    fn_def = camel + "Function"
    rel, text = find_function_def(fn_def)
    if rel is None:
        print(f"gen-port-kit: no `def {fn_def} : String` under {atp.SCAN_DIRS}", file=sys.stderr)
        print("Hint: run `python3 scripts/asm_to_program.py coverage | grep "
              f"{args.entry}` to see if the routine exists under another name.",
              file=sys.stderr)
        sys.exit(1)

    prog_name = camel + "_ported"
    converted = None
    conv_note = ""
    # Already converted to a Program (asm→Program waves)? Then the port
    # job is the SPEC over that Program — don't duplicate the conversion.
    m = re.search(
        r"def\s+" + re.escape(fn_def)
        + r"\s*:\s*String\s*:=\s*\n?\s*\"[^\"]*\"\s*\+\+\s*emitProgramR?\s+([A-Za-z0-9_']+)",
        text)
    if m:
        existing = m.group(1)
        prog_name = existing
        converted = (
            f"-- `{args.entry}` is ALREADY converted: `{existing} : Program` in {rel}\n"
            f"-- (correspondence theorem `{fn_def}_eq_prog` exists there).\n"
            f"-- The remaining work is the SPEC over `{existing}`:\n"
            f"--   * straight-line leaf -> cpsTripleWithin block spec directly over it;\n"
            f"--   * otherwise rebuild as an SAsm `Fn` whose flatten equals it,\n"
            f"--     with a `#guard <fn>.flatten 0 = {existing}` pin.\n"
            f"-- NOTE: this skeleton lives in the verified core and must NOT import\n"
            f"-- Codegen (layering L1) — restate the Program here with a value-equality\n"
            f"-- `#guard`/`decide` pin against the Codegen copy in the PR description,\n"
            f"-- or verify it under EvmAsm/Codegen/Proofs/ (which may import both).\n\n")
    try:
        if m:
            raise atp.ConvError("already converted; spec-only skeleton emitted")
        asm = atp.extract_function(text, fn_def)
        entry, renders, _emitted, ok, la, lb, relocs = atp.do_asm(asm)
        if not ok:
            conv_note = f"assemble+cmp DIFFERS ({la} vs {lb} bytes) — investigate before porting"
        else:
            body = ",\n    ".join(renders)
            reloc_note = ""
            if relocs:
                reloc_note = (
                    f"\n-- NOTE: {len(relocs)} `la`/cross-`jal` reloc(s); the immediates below are\n"
                    "-- the concrete guest-linked values (see asm_to_program.py wave-3 notes;\n"
                    "-- deployment needs the emitProgramR reloc side-table via\n"
                    "-- `asm_to_program.py rewrite`).")
            converted = (
                f"/-- Mechanical conversion of `{fn_def}` ({rel});\n"
                f"    byte-identity checked by scripts/asm_to_program.py at generation time. -/"
                f"{reloc_note}\n"
                f"def {prog_name} : Program :=\n  [ {body} ]\n\n"
                f"#guard {prog_name}.length = {len(renders)}\n")
    except atp.ConvError as e:
        conv_note = str(e)

    if converted is None:
        asm_block = ""
        try:
            asm_block = atp.extract_function(text, fn_def)
        except Exception:
            asm_block = "(could not extract asm body — composite def; read the source file)"
        converted = (
            f"-- Mechanical conversion NOT available: {conv_note or 'composite def'}\n"
            f"-- Raw asm body of {fn_def} ({rel}) for reference:\n"
            "/-\n" + asm_block.rstrip() + "\n-/\n\n"
            f"-- TODO(port): hand-write the SAsm `Fn` for this routine (copy the\n"
            f"-- class exemplar from the playbook Step 0 table) and `#guard`-pin\n"
            f"-- `(<fn>.flatten 0)` length + position-independence.\n")

    header = f"""/-
  {args.ns}.{camel[0].upper() + camel[1:]}SAsm

  Verified port of `{args.entry}` (source: {rel}, def `{fn_def}`).
  Generated by scripts/gen-port-kit.py — fill the TODO(port) blocks.

  Playbook: docs/agents/port-playbook.md   (class table in Step 0)
  Big picture: docs/agents/top-theorem-ledger.md

  ## Delivery checklist (sasm-howto §9)
  1. scripts/port-check.sh <this file>   -- build, warnings, tactics, axioms
  2. If emitted code changed — EEST A/B (both legs, identical failures only):
       git stash -u && lake exe codegen --program stateless_guest \\
         --halt linux93 -o gen-out/base && git stash pop
       lake exe codegen --program stateless_guest --halt linux93 -o gen-out/cand
       GUEST_ELF=<elf> EEST_RUN_DIR=<dir> \\
         scripts/codegen-eest-stateless-check.sh --no-build --backend spike \\
         --random --seed 4242 --limit 200 --jobs 8 --quiet-passes
  3. PLAN.md + docs/agents/top-theorem-ledger.md updated; bead closed only
     after the PR lands on main.
-/

import EvmAsm.Rv64.SAsm.Tactic

namespace {args.ns}

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

"""

    out_text = (header + converted
                + TEMPLATE_SPEC.replace("{prog_name}", prog_name)
                + f"\nend {args.ns}\n")

    if args.out:
        outp = os.path.join(REPO, args.out) if not os.path.isabs(args.out) else args.out
        if os.path.exists(outp):
            print(f"gen-port-kit: refusing to overwrite existing {args.out}", file=sys.stderr)
            sys.exit(1)
        os.makedirs(os.path.dirname(outp), exist_ok=True)
        open(outp, "w").write(out_text)
        print(f"wrote {args.out}")
        print(f"next: fill TODO(port), then scripts/port-check.sh {args.out}")
    else:
        print(out_text)


if __name__ == "__main__":
    main()
