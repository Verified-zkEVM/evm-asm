#!/usr/bin/env python3
"""Regression gate for GH #10784: MTx account-state commit arm consumes a
SELFDESTRUCT queued by a transaction that later fails at top level.

THE DEFECT (filed, verified): BlockVerdictMtxRuntime.lean:615 takes the
per-tx COMMIT arm when the tx status is nonzero OR
runtime_tx_post_preparation_reached is set; only the fall-through arm clears
account_state_pending/created/delete_count, and the depth-0 rollback does not
restore those counters. A destroy queued by a failed post-preparation tx is
therefore consumed by the commit arm. Measured direction: LATENT — the arm
FIRES on every failing post-preparation tx, yet the post-state root is
unaffected.

LATENCY CONDITIONS (load-bearing — this gate exists to pin them):

  1. Delete-queue insertion (NoopHalt.lean:520-600) is gated on the target
     being created in the SAME transaction (EIP-6780 semantics). Proven by
     fxA/fxB: delete=0 at commit-arm entry for pre-existing and
     prior-tx-created targets.
  2. The depth-0 rollback removes everything a failed tx created. Proven by
     fx1: created=1 delete=1 at commit-arm entry, yet the post-state root
     matches the spec byte-for-byte — committing the delete removes an
     already-absent account (a trie no-op).

If either condition changes, the numbers below MOVE and this gate must fire.
A gate that only checked the state root would pass forever and tell you
nothing: the root is no-op-identical BY the mechanism under test. So this
gate asserts the INSTRUMENTED-PROBE NUMBERS (arm marker and pending/created/
delete counts snapshotted at commit-arm entry) TOGETHER WITH byte-exact root
agreement. delete=1 on fx1 is the current correct-as-measured state; the
assertion is that it stays consistent with the roots matching.

WHAT THE GATE RUNS (three spec-valid fixtures from
scripts/fill/test_10784_mtx_commit_arm.py, filled with the in-repo EELS t8n):

  fx1  same-tx-created contract selfdestructs, then the tx REVERTs at top
       level. Expect: commit arm (17), post_preparation flag 1, at commit
       entry pending=7 created=1 delete=1; roots match.
  fxA  pre-existing contract (balance+storage) selfdestructs, then top-level
       REVERT. Expect: commit arm, flag 1, pending=4 created=0 delete=0;
       roots match.
  fxB  contract deployed in successful tx1, selfdestructs in tx2 which then
       REVERTs at top level. Expect: commit arm, flag 1, pending=2
       created=0 delete=0; roots match.

PRISTINE-CHANNEL ASSERTIONS (stateless_guest.elf + verdict_probe.elf):
guest succ byte at offset 32 == 1; guest output == fixture
statelessOutputBytes; probe verdict@0 == 1, bv_fail@8 == 0, and
sv_recomputed@168 == the fixture's declared blockHeader.stateRoot
(byte-for-byte — "roots match" means EXACT, not "no symptom noticed").

INSTRUMENTED-PROBE RECIPE (third use; do not reinvent): copy the EMITTED
verdict_probe .s (never the Lean tree, never the pristine ELF), apply the
string patch in instrument_probe_source() below — arm marker written at both
epilogue arms, pending/created/delete counts snapshotted at commit-arm entry
into new .bss cells, dump window slots 16/24/232/240/248 repointed at the
cells — then assemble and link with the standard flags:

    riscv64-unknown-elf-as -march=rv64imac -mno-relax -o probe.o probe.s
    riscv64-unknown-elf-ld -Ttext=0x80000000 -Tdata=0xa0b00000 \
        --section-start=.bss=0xa0b70000 --section-start=.sszscratch=0xbf980000 \
        -nostdlib --no-relax -o probe.elf probe.o

spike_run dumps a 256-byte window at OUTPUT 0xa0010000; every 8-byte slot in
0..248 is written by the probe, so the at-commit cells fit at 232..248.
Read outputs at NAMED offsets, e.g.:

    dd if=fx1_arm_out.bin bs=1 skip=16  count=8 | xxd -p   # arm marker (0x11)
    dd if=fx1_arm_out.bin bs=1 skip=248 count=8 | xxd -p   # delete at commit

USAGE (from the repo root; execution-specs submodule must be checked out):

    python3 scripts/gate-10784-mtx-commit-arm.py

Options: --workdir DIR (default gen-out/gate-10784-mtx-commit-arm),
--guest-elf / --probe-elf (default: emit fresh via lake into the workdir),
--reuse-fixtures (skip re-running fill), --keep-going (report all failures
before exiting nonzero). Diagnostic gate: asserts the measured state of
main; does not modify the guest.
"""

from __future__ import annotations

import argparse
import json
import struct
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FILL_FILE = REPO / "scripts" / "fill" / "test_10784_mtx_commit_arm.py"
SPECS_DIR = REPO / "execution-specs"
SPIKE_RUN = REPO / "scripts" / "spike" / "spike_run"

AS = "riscv64-unknown-elf-as"
LD = "riscv64-unknown-elf-ld"
AS_FLAGS = ["-march=rv64imac", "-mno-relax"]
LD_FLAGS = [
    "-Ttext=0x80000000",
    "-Tdata=0xa0b00000",
    "--section-start=.bss=0xa0b70000",
    "--section-start=.sszscratch=0xbf980000",
    "-nostdlib",
    "--no-relax",
]

# Output-window offsets (spike_run dumps 256 bytes from OUTPUT 0xa0010000).
OFF_SUCC = 32  # guest SszStatelessValidationResult success byte
OFF_VERDICT = 0
OFF_BV_FAIL = 8
OFF_ARM = 16  # instrumented: 17 = commit arm, 34 = fall-through clear
OFF_POST_PREP = 24  # instrumented: runtime_tx_post_preparation_reached
OFF_SV_RECOMPUTED = 168  # 32 bytes, guest-derived post-state root
OFF_PEND = 232  # instrumented: account_state_pending_count at commit entry
OFF_CREATED = 240  # instrumented: account_state_created_count at commit entry
OFF_DELETE = 248  # instrumented: account_state_delete_count at commit entry

ARM_COMMIT = 17
ARM_FALL_THROUGH = 34

FIXTURES = {
    # name -> (filled-json filename stem, expected at-commit-entry counts)
    "fx1": ("selfdestruct_created_same_tx_top_level_revert", (7, 1, 1)),
    "fxA": ("preexisting_selfdestruct_top_level_revert", (4, 0, 0)),
    "fxB": ("created_earlier_tx_selfdestruct_top_level_revert", (2, 0, 0)),
}


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    print("+", " ".join(str(c) for c in cmd))
    return subprocess.run(cmd, check=True, **kw)


def word(buf: bytes, off: int) -> int:
    return struct.unpack("<Q", buf[off : off + 8])[0]


def pack_input(blob: bytes) -> bytes:
    packed = struct.pack("<Q", len(blob)) + blob
    return packed + b"\x00" * ((-len(packed)) % 8)


def fill_fixtures(workdir: Path) -> None:
    out = workdir / "fixtures"
    run(
        [
            "uv",
            "run",
            "--directory",
            str(SPECS_DIR),
            "fill",
            str(FILL_FILE),
            "--fork",
            "Amsterdam",
            "--output",
            str(out),
            "--clean",
            "--no-html",
        ],
        cwd=REPO,
    )


def load_fixture(workdir: Path, stem: str) -> dict:
    """Return the Amsterdam blockchain-test block entry for `stem`."""
    root = workdir / "fixtures" / "blockchain_tests" / "for_amsterdam"
    candidates = sorted(root.rglob(f"{stem}.json"))
    if not candidates:
        raise SystemExit(f"fixture {stem}.json not found under {root}")
    for path in candidates:
        data = json.loads(path.read_text())
        for key, test in data.items():
            if "fork_Amsterdam-" in key:
                return test["blocks"][0]
    raise SystemExit(f"no fork_Amsterdam entry in any {stem}.json")


def emit_elf(program: str, prefix: Path) -> None:
    run(["lake", "build", "codegen"], cwd=REPO)
    run(
        [
            "lake",
            "exe",
            "codegen",
            "--program",
            program,
            "--halt",
            "linux93",
            "-o",
            str(prefix),
        ],
        cwd=REPO,
    )


def replace_once(src: str, old: str, new: str, label: str) -> str:
    n = src.count(old)
    if n != 1:
        raise SystemExit(f"instrumentation anchor {label!r} found {n} times (want 1)")
    return src.replace(old, new, 1)


def instrument_probe_source(src: str) -> str:
    """Patch the emitted verdict_probe .s (see the recipe in the module
    docstring). Anchors are exact strings in the emitted assembly; each must
    occur exactly once."""
    src = replace_once(
        src,
        "  la t1, bv_header_status; ld t2, 0(t1); sd t2, 16(t0)\n"
        "  la t1, bv_state_status; ld t2, 0(t1); sd t2, 24(t0)",
        "  la t1, acct_probe_arm_marker; ld t2, 0(t1); sd t2, 16(t0)\n"
        "  la t1, runtime_tx_post_preparation_reached; ld t2, 0(t1); sd t2, 24(t0)",
        "dump slots 16/24",
    )
    src = replace_once(
        src,
        "  la t1, bvgr_arena_status; ld t2, 0(t1); sd t2, 232(t0)\n"
        "  la t1, bvgr_arena_tx_count; ld t2, 0(t1); sd t2, 240(t0)\n"
        "  la t1, bvgr_arena_runtime_count; ld t2, 0(t1); sd t2, 248(t0)",
        "  la t1, acct_probe_pend_at_commit; ld t2, 0(t1); sd t2, 232(t0)\n"
        "  la t1, acct_probe_created_at_commit; ld t2, 0(t1); sd t2, 240(t0)\n"
        "  la t1, acct_probe_del_at_commit; ld t2, 0(t1); sd t2, 248(t0)",
        "dump slots 232/240/248",
    )
    src = replace_once(
        src,
        "  la t0, account_state_pending_count; sd zero, 0(t0);"
        " la t0, account_state_created_count; sd zero, 0(t0);"
        " la t0, account_state_delete_count; sd zero, 0(t0)\n",
        "  la t0, account_state_pending_count; sd zero, 0(t0);"
        " la t0, account_state_created_count; sd zero, 0(t0);"
        " la t0, account_state_delete_count; sd zero, 0(t0)\n"
        "  la t0, acct_probe_arm_marker; li t1, 34; sd t1, 0(t0)\n",
        "fall-through arm marker",
    )
    src = replace_once(
        src,
        ".Lbv_mtx_code_commit:\n",
        ".Lbv_mtx_code_commit:\n"
        "  la t0, acct_probe_arm_marker; li t1, 17; sd t1, 0(t0)\n"
        "  la t0, account_state_delete_count; ld t1, 0(t0);"
        " la t0, acct_probe_del_at_commit; sd t1, 0(t0)\n"
        "  la t0, account_state_created_count; ld t1, 0(t0);"
        " la t0, acct_probe_created_at_commit; sd t1, 0(t0)\n"
        "  la t0, account_state_pending_count; ld t1, 0(t0);"
        " la t0, acct_probe_pend_at_commit; sd t1, 0(t0)\n",
        "commit-arm marker + snapshot",
    )
    src += (
        "\n.section .bss\n"
        ".globl acct_probe_arm_marker\n"
        "acct_probe_arm_marker:\n  .zero 8\n"
        "acct_probe_del_at_commit:\n  .zero 8\n"
        "acct_probe_created_at_commit:\n  .zero 8\n"
        "acct_probe_pend_at_commit:\n  .zero 8\n"
    )
    return src


def build_instrumented_probe(probe_s: Path, workdir: Path) -> Path:
    patched = workdir / "verdict_probe_acct_arm.s"
    patched.write_text(instrument_probe_source(probe_s.read_text()))
    obj = workdir / "verdict_probe_acct_arm.o"
    elf = workdir / "verdict_probe_acct_arm.elf"
    run([AS, *AS_FLAGS, "-o", str(obj), str(patched)])
    run([LD, *LD_FLAGS, "-o", str(elf), str(obj)])
    return elf


def spike(elf: Path, input_path: Path, out_path: Path) -> bytes:
    run([str(SPIKE_RUN), str(elf), str(input_path), str(out_path)])
    return out_path.read_bytes()


FAILURES: list[str] = []


def check(label: str, ok: bool, detail: str, keep_going: bool) -> None:
    status = "ok " if ok else "FAIL"
    print(f"  [{status}] {label}: {detail}")
    if not ok:
        FAILURES.append(f"{label}: {detail}")
        if not keep_going:
            raise SystemExit(f"gate failed: {label}: {detail}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--workdir", default=str(REPO / "gen-out" / "gate-10784-mtx-commit-arm"))
    ap.add_argument("--guest-elf")
    ap.add_argument("--probe-elf")
    ap.add_argument("--reuse-fixtures", action="store_true")
    ap.add_argument("--keep-going", action="store_true")
    args = ap.parse_args()
    workdir = Path(args.workdir).resolve()
    workdir.mkdir(parents=True, exist_ok=True)

    guest_elf = Path(args.guest_elf) if args.guest_elf else workdir / "stateless_guest"
    probe_elf = Path(args.probe_elf) if args.probe_elf else workdir / "verdict_probe"
    for program, prefix in (("stateless_guest", guest_elf), ("zisk_stateless_verdict_v2", probe_elf)):
        if not prefix.with_suffix(".elf").exists():
            emit_elf(program, prefix.with_suffix(""))
    guest_elf = guest_elf if guest_elf.suffix == ".elf" else guest_elf.with_suffix(".elf")
    probe_elf = probe_elf if probe_elf.suffix == ".elf" else probe_elf.with_suffix(".elf")
    probe_s = probe_elf.with_suffix(".s")

    if not args.reuse_fixtures:
        fill_fixtures(workdir)

    arm_elf = build_instrumented_probe(probe_s, workdir)

    for name, (stem, (exp_pend, exp_created, exp_del)) in FIXTURES.items():
        print(f"== {name} ({stem}) ==")
        block = load_fixture(workdir, stem)
        blob = bytes.fromhex(block["statelessInputBytes"][2:])
        expected_out = bytes.fromhex(block["statelessOutputBytes"][2:])
        declared_root = bytes.fromhex(block["blockHeader"]["stateRoot"][2:])
        input_path = workdir / f"{name}.input"
        input_path.write_bytes(pack_input(blob))

        guest_out = spike(guest_elf, input_path, workdir / f"{name}.guest.out")
        check(
            f"{name} guest succ byte",
            guest_out[OFF_SUCC] == 1,
            f"succ@{OFF_SUCC} = {guest_out[OFF_SUCC]:#04x} (want 0x01)",
            args.keep_going,
        )
        check(
            f"{name} guest output == expected output",
            guest_out[: len(expected_out)] == expected_out,
            f"{guest_out[: len(expected_out)].hex()} vs {expected_out.hex()}",
            args.keep_going,
        )

        probe_out = spike(probe_elf, input_path, workdir / f"{name}.probe.out")
        check(
            f"{name} pristine verdict/bv_fail",
            word(probe_out, OFF_VERDICT) == 1 and word(probe_out, OFF_BV_FAIL) == 0,
            f"verdict@{OFF_VERDICT} = {word(probe_out, OFF_VERDICT)},"
            f" bv_fail@{OFF_BV_FAIL} = {word(probe_out, OFF_BV_FAIL)} (want 1, 0)",
            args.keep_going,
        )
        recomputed = probe_out[OFF_SV_RECOMPUTED : OFF_SV_RECOMPUTED + 32]
        check(
            f"{name} post-state root matches spec byte-for-byte",
            recomputed == declared_root,
            f"sv_recomputed@{OFF_SV_RECOMPUTED} = 0x{recomputed.hex()}"
            f" vs declared 0x{declared_root.hex()}",
            args.keep_going,
        )

        arm_out = spike(arm_elf, input_path, workdir / f"{name}.arm.out")
        arm = word(arm_out, OFF_ARM)
        flag = word(arm_out, OFF_POST_PREP)
        pend = word(arm_out, OFF_PEND)
        created = word(arm_out, OFF_CREATED)
        delete = word(arm_out, OFF_DELETE)
        check(
            f"{name} failing tx took COMMIT arm",
            arm == ARM_COMMIT and flag == 1,
            f"arm@{OFF_ARM} = {arm} (17=commit, 34=fall-through),"
            f" post_preparation@{OFF_POST_PREP} = {flag}",
            args.keep_going,
        )
        check(
            f"{name} counts at commit-arm entry",
            (pend, created, delete) == (exp_pend, exp_created, exp_del),
            f"pending={pend} created={created} delete={delete}"
            f" (want pending={exp_pend} created={exp_created} delete={exp_del})",
            args.keep_going,
        )

    if FAILURES:
        print(f"\nGATE FAILED ({len(FAILURES)} assertion(s)):")
        for failure in FAILURES:
            print("  -", failure)
        raise SystemExit(1)
    print("\nGATE PASSED: commit arm fires on all three shapes (delete=1 on fx1,"
          " 0 on fxA/fxB) and post-state roots match the spec byte-for-byte."
          " GH #10784 remains latent under the two pinned conditions.")


if __name__ == "__main__":
    main()
