#!/usr/bin/env python3
"""Witness generator for GH issue #10764 (withdrawal-credit false accept).

Diagnostic only: constructs a mutated stateless input and measures whether
the emitted guest accepts a block that execution-specs rejects.  It does not
change any guest code.

Claim under test
----------------
The guest's legacy/simple-transfer dispatch route is dead for any block with
at least one transaction (BlockVerdictMtxRuntime branches
bv_tx_count == 0 -> .Lbv_recipient_nc_done, so every non-empty block enters
the MTx path).  The only call to
block_verdict_withdrawal_nonstorage_effects -- the routine that reconciles
withdrawal balance credits against the declared block access list (BAL) --
sits in BlockVerdictEoaBodyEffectReconcile, reachable only from that dead
route.  Open question: does anything else on the MTx route validate
withdrawal credits?

Construction
------------
Fixture (identity = repo-relative path):
  gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures/
    blockchain_tests/for_amsterdam/amsterdam/
    eip7928_block_level_access_lists/block_access_lists_eip4895/
    bal_withdrawal_and_value_transfer_same_address.json

The block has 1 tx and 1 withdrawal of 10 gwei
(10,000,000,000 wei) to address 0xc0f6dc9e5836f54caadbf59cc69346c508e1992b.
The declared BAL for that address carries two balanceChanges rows:

  blockAccessIndex 1 -> postBalance  5,000,000,000  (0x012a05f200; the tx)
  blockAccessIndex 2 -> postBalance 15,000,000,000  (0x037e11d600; +10 gwei
                                                       withdrawal credit)

Mutation (one declared value plus the two forced re-pins):

  1. In the blob's BAL bytes, change the blockAccessIndex-2 postBalance
     RLP string 85 037e11d600 (15e9) to 85 012a05f200 (5e9).  Verified to
     occur exactly once in the blob, at offset 1051, in the context
     ... c7 01 85 012a05f200 c7 02 85 037e11d600 c0c0
     (BAI-1 row then BAI-2 row).  Same length, so no SSZ offsets move.
     After the edit the BAL declares that the withdrawal credited nothing:
     declared post-balance 5e9 vs true 15e9.
  2. Re-pin payload.state_root (blob offset 114) to the guest-derived
     post-state root (sv_recomputed), obtained by running the
     zisk_stateless_verdict_v2 probe on the step-1 blob.  Because
     block_verdict runs the block-hash check BEFORE block_state_root, the
     step-1 blob (whose declared block_hash is stale after the BAL edit)
     dies at .Lbv_block_hash_mismatch before sv_recomputed is written; the
     extraction therefore uses a DIAGNOSTIC probe assembled from the emitted
     probe .s with the bv_block_hash_check_enabled .data cell flipped
     .dword 1 -> .dword 0 (no source/tree change, guest ELF untouched):
       cp verdict_probe.s verdict_probe_nohash.s   # flip the cell
       riscv64-unknown-elf-as -march=rv64imac -mno-relax -o x.o x.s
       riscv64-unknown-elf-ld -Ttext=0x80000000 -Tdata=0xa3000000 \
         --section-start=.bss=0xa4000000 \
         --section-start=.sszscratch=0xbf800000 \
         -nostdlib --no-relax -o verdict_probe_nohash.elf x.o
     On the step-1 blob the nohash probe reports verdict=0 bv_fail=1
     (state-root mismatch, the expected failure) with header_status=0 and
     state_status=0, proving block_state_root ran; sv_recomputed @OUTPUT+168
     is then the guest-derived root.  The guest's post-state root is BAL-fed
     (block_state_root applies the declared BAL changes), so re-pinning makes
     the header's state_root oracle equal the guest's own output -- that
     circularity is exactly what the false accept exploits.  The mutated
     block is self-consistent with the guest's model BY CONSTRUCTION; that
     is what "false accept" means here.
  3. Re-pin payload.block_hash (blob offset 534) to
     keccak256(rlp.encode(_payload_header(payload, ...))) computed with the
     pinned execution-specs checkout.  _payload_header derives
     block_access_list_hash = keccak256(payload.block_access_list), so the
     BAL edit is already reflected; state_root comes from the payload
     field pinned in step 2.  Without this re-pin the block-hash check
     would reject the mutation for the wrong reason.

The declared blockAccessListHash header value never appears in the blob:
the guest recomputes it from the supplied BAL bytes
(block_access_list_hash routine), so only the two pins above are needed.

Verdict rule
------------
  * execution-specs run_stateless_guest REJECTS the step-3 blob and the
    guest (spike) ACCEPTS it (succ byte = 1)  => false accept CONFIRMED.
  * guest REJECTS => something on the MTx route validates withdrawal
    credits after all; the claim is withdrawn.  Equally useful.
  * cannot build/run => say where it is blocked.

Usage:
  uv run --directory execution-specs --quiet python3 \
      scripts/witness-10764-withdrawal-fa.py run [--work-dir DIR]

Requires the guest and probe ELFs (built once, no --no-build games):
  lake build codegen
  lake exe codegen --program stateless_guest --halt linux93 \
      -o gen-out/fa-witness-10764/stateless_guest
  lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 \
      -o gen-out/fa-witness-10764/verdict_probe
"""
from __future__ import annotations

import argparse
import json
import struct
import subprocess
import sys
import traceback
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

FIXTURE_REL = (
    "gen-out/eest-fixtures/tests-zkevm@v0.6.2/fixtures/fixtures/"
    "blockchain_tests/for_amsterdam/amsterdam/"
    "eip7928_block_level_access_lists/block_access_lists_eip4895/"
    "bal_withdrawal_and_value_transfer_same_address.json"
)

DEFAULT_WORK_DIR = REPO_ROOT / "gen-out" / "fa-witness-10764"
GUEST_ELF = DEFAULT_WORK_DIR / "stateless_guest.elf"
PROBE_ELF = DEFAULT_WORK_DIR / "verdict_probe.elf"
NOHASH_PROBE_ELF = DEFAULT_WORK_DIR / "verdict_probe_nohash.elf"
SPIKE_RUN = REPO_ROOT / "scripts" / "spike" / "spike_run"

SCHEMA_PREFIX_LEN = 2
STATE_ROOT_OFF = 114  # SSZ payload base 62 + 52
BLOCK_HASH_OFF = 534  # SSZ payload base 62 + 472

OLD_POST_BALANCE = bytes.fromhex("85037e11d600")  # RLP string: 15_000_000_000
NEW_POST_BALANCE = bytes.fromhex("85012a05f200")  # RLP string:  5_000_000_000
EDIT_CONTEXT = bytes.fromhex("c70185012a05f200c70285037e11d600c0c0")

# Probe OUTPUT (0xa0010000) layout; spike_run dumps a 256-byte window.
PROBE_OUT_VERDICT = 0
PROBE_OUT_BV_FAIL = 8
PROBE_OUT_HEADER_STATUS = 16
PROBE_OUT_STATE_STATUS = 24
PROBE_OUT_SV_RECOMPUTED = 168

DECLARED_WEI = 5_000_000_000
TRUE_WEI = 15_000_000_000
WITHDRAWAL_WEI = 10_000_000_000


def pack_ziskemu_input(blob: bytes) -> bytes:
    """8-byte LE length, blob, zero pad to 8 (mirrors eest-stateless-to-input)."""
    total = 8 + len(blob)
    pad = (-total) % 8
    return struct.pack("<Q", len(blob)) + blob + (b"\x00" * pad)


def load_fixture_blob(fixture_path: Path) -> tuple[bytes, dict]:
    doc = json.loads(fixture_path.read_text())
    # Fixture JSON: top-level test-name key(s) -> test body with .blocks[].
    blobs = []
    for test_name, body in doc.items():
        for i, block in enumerate(body.get("blocks", [])):
            sib = block.get("statelessInputBytes")
            if sib:
                blobs.append((test_name, i, block))
    if len(blobs) != 1:
        raise SystemExit(
            f"expected exactly 1 stateless block in fixture, got {len(blobs)}"
        )
    test_name, idx, block = blobs[0]
    blob = bytes.fromhex(block["statelessInputBytes"].removeprefix("0x"))
    return blob, block


def spec_imports():
    from ethereum.forks.amsterdam.execution_engine.validation_helpers import (
        _payload_header,
    )
    from ethereum.forks.amsterdam.stateless_guest import (
        deserialize_stateless_input,
        run_stateless_guest,
    )
    from ethereum.crypto.hash import keccak256
    from ethereum_rlp import rlp

    return (
        _payload_header,
        deserialize_stateless_input,
        run_stateless_guest,
        keccak256,
        rlp,
    )


def payload_block_hash(blob: bytes) -> bytes:
    """keccak256(rlp.encode(_payload_header(...))) for the blob's payload."""
    (_payload_header, deserialize_stateless_input, _, keccak256, rlp) = (
        spec_imports()
    )
    stateless_input = deserialize_stateless_input(blob)
    npr = stateless_input.new_payload_request
    header = _payload_header(
        npr.execution_payload,
        npr.parent_beacon_block_root,
        npr.execution_requests,
    )
    return bytes(keccak256(rlp.encode(header)))


def run_spike(elf: Path, input_path: Path, out_path: Path, log_path: Path) -> None:
    with log_path.open("wb") as log:
        proc = subprocess.run(
            [str(SPIKE_RUN), str(elf), str(input_path), str(out_path)],
            stdout=log,
            stderr=subprocess.STDOUT,
        )
    if proc.returncode != 0:
        raise SystemExit(
            f"spike_run failed rc={proc.returncode}; see {log_path}"
        )


def probe_fields(out_path: Path) -> dict:
    data = out_path.read_bytes()
    if len(data) < 232:
        raise SystemExit(f"probe output too short: {len(data)} bytes")
    u64 = lambda off: int.from_bytes(data[off : off + 8], "little")
    return {
        "verdict": u64(PROBE_OUT_VERDICT),
        "bv_fail": u64(PROBE_OUT_BV_FAIL),
        "header_status": u64(PROBE_OUT_HEADER_STATUS),
        "state_status": u64(PROBE_OUT_STATE_STATUS),
        "sv_recomputed": data[
            PROBE_OUT_SV_RECOMPUTED : PROBE_OUT_SV_RECOMPUTED + 32
        ],
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("command", choices=["run"])
    ap.add_argument(
        "--fixture",
        type=Path,
        default=REPO_ROOT / FIXTURE_REL,
        help="fixture JSON (identity is its repo-relative path)",
    )
    ap.add_argument("--work-dir", type=Path, default=DEFAULT_WORK_DIR)
    args = ap.parse_args()

    work = args.work_dir
    work.mkdir(parents=True, exist_ok=True)
    for elf in (GUEST_ELF, PROBE_ELF, NOHASH_PROBE_ELF):
        if not elf.exists():
            raise SystemExit(
                f"missing {elf}; build it first (see module docstring)"
            )
    if not SPIKE_RUN.exists():
        raise SystemExit(f"missing {SPIKE_RUN}")

    fixture_rel = args.fixture.resolve().relative_to(REPO_ROOT)
    print(f"fixture: {fixture_rel}")
    blob0, block_json = load_fixture_blob(args.fixture)
    print(f"blob length: {len(blob0)} bytes")
    assert blob0[:SCHEMA_PREFIX_LEN] == bytes.fromhex("1501")

    # --- Step 0: method sanity on the ORIGINAL blob ---------------------
    # The recomputed header hash must equal the fixture's declared hash.
    declared_hash = bytes.fromhex(
        block_json["blockHeader"]["hash"].removeprefix("0x")
    )
    recomputed0 = payload_block_hash(blob0)
    print(f"original block hash declared:   0x{declared_hash.hex()}")
    print(f"original block hash recomputed: 0x{recomputed0.hex()}")
    if recomputed0 != declared_hash:
        raise SystemExit("method sanity failed on the original blob")

    # --- Step 1: BAL mutation -------------------------------------------
    if blob0.count(OLD_POST_BALANCE) != 1:
        raise SystemExit("15e9 pattern not unique in blob")
    off = blob0.index(OLD_POST_BALANCE)
    ctx = blob0[off - 10 : off + len(OLD_POST_BALANCE) + 2]
    if ctx != EDIT_CONTEXT:
        raise SystemExit(f"edit context mismatch at {off}: {ctx.hex()}")
    print(f"edit offset: {off} (expected 1051)")
    blob1 = blob0[:off] + NEW_POST_BALANCE + blob0[off + len(OLD_POST_BALANCE) :]
    assert len(blob1) == len(blob0)
    (work / "v1-bal-only.blob").write_bytes(blob1)
    (work / "v1-bal-only.input").write_bytes(pack_ziskemu_input(blob1))

    # --- Step 2: nohash probe on v1 to get the guest-derived root -------
    # The pristine probe dies at .Lbv_block_hash_mismatch (bv_fail=31)
    # before block_state_root runs; the hash-check-disabled diagnostic
    # probe reaches block_state_root and reports the expected state-root
    # mismatch signature (verdict=0, bv_fail=1, statuses 0).
    run_spike(
        NOHASH_PROBE_ELF,
        work / "v1-bal-only.input",
        work / "v1.probe.out",
        work / "v1.probe.log",
    )
    f1 = probe_fields(work / "v1.probe.out")
    sv_recomputed = f1["sv_recomputed"]
    print(
        "nohash probe on v1 (BAL-only): verdict={verdict} bv_fail={bv_fail} "
        "header_status={header_status} state_status={state_status}".format(**f1)
    )
    if not (
        f1["verdict"] == 0
        and f1["bv_fail"] == 1
        and f1["header_status"] == 0
        and f1["state_status"] == 0
        and sv_recomputed != b"\x00" * 32
    ):
        raise SystemExit(
            "nohash probe on v1 did not reach block_state_root as expected; "
            "refusing to re-pin from an untrusted sv_recomputed"
        )
    print(f"sv_recomputed (guest-derived post-state root): 0x{sv_recomputed.hex()}")

    # --- Step 3: re-pin state_root and block_hash ------------------------
    blob2 = blob1[:STATE_ROOT_OFF] + sv_recomputed + blob1[STATE_ROOT_OFF + 32 :]
    new_block_hash = payload_block_hash(blob2)
    blob3 = blob2[:BLOCK_HASH_OFF] + new_block_hash + blob2[BLOCK_HASH_OFF + 32 :]
    (work / "v3-pinned.blob").write_bytes(blob3)
    (work / "v3-pinned.input").write_bytes(pack_ziskemu_input(blob3))
    print(f"re-pinned state_root: 0x{sv_recomputed.hex()}")
    print(f"re-pinned block_hash: 0x{new_block_hash.hex()}")

    # --- Step 4: execution-specs verdict on v3 ---------------------------
    # run_stateless_guest catches every exception into
    # successful_validation=False; to quote WHICH check fires we then
    # re-run the verify_stateless_new_payload body bare (same code path,
    # no try/except) and print the traceback.
    (_, deserialize_stateless_input, run_stateless_guest, _, _) = spec_imports()
    out = run_stateless_guest(blob3)
    spec_succ = out[32] if len(out) > 32 else None
    spec_rejects = spec_succ == 0
    print(f"execution-specs run_stateless_guest on v3: succ byte = {spec_succ}")
    if spec_rejects:
        from ethereum.forks.amsterdam.stateless import (
            ChainContext,
            WitnessState,
            build_code_db,
            build_node_db,
            validate_chain_config,
            validate_headers,
        )
        from ethereum.forks.amsterdam.execution_engine.new_payload import (
            execute_new_payload_request,
        )

        si = deserialize_stateless_input(blob3)
        try:
            validate_chain_config(si.chain_config, si.new_payload_request)
            decoded_headers, block_hashes = validate_headers(si.witness.headers)
            chain_context = ChainContext(
                chain_id=si.chain_config.chain_id,
                block_hashes=block_hashes,
                parent_header=decoded_headers[-1],
            )
            pre_state = WitnessState(
                _node_db=build_node_db(si.witness.state),
                _state_root=decoded_headers[-1].state_root,
                _code_db=build_code_db(si.witness.codes),
            )
            execute_new_payload_request(
                si.new_payload_request,
                pre_state,
                chain_context,
                transaction_public_keys=si.public_keys,
            )
        except Exception:
            print("bare re-run raised (this is the rejecting check):")
            traceback.print_exc(limit=8)
        else:
            print("bare re-run did NOT raise; rejection path not identified")

    # --- Step 5: guest verdict on v3 -------------------------------------
    run_spike(
        GUEST_ELF,
        work / "v3-pinned.input",
        work / "v3.guest.out",
        work / "v3.guest.log",
    )
    guest_out = (work / "v3.guest.out").read_bytes()
    guest_succ = guest_out[32] if len(guest_out) > 32 else None
    run_spike(
        PROBE_ELF,
        work / "v3-pinned.input",
        work / "v3.probe.out",
        work / "v3.probe.log",
    )
    f3 = probe_fields(work / "v3.probe.out")
    print(f"guest on v3: succ byte = {guest_succ}")
    print(
        "probe on v3: verdict={verdict} bv_fail={bv_fail} "
        "header_status={header_status} state_status={state_status}".format(**f3)
    )

    # --- Verdict ----------------------------------------------------------
    print()
    print("compared pair (BAI-2 postBalance for the withdrawal address):")
    print(f"  declared: {DECLARED_WEI} wei")
    print(f"  true:     {TRUE_WEI} wei (withdrawal of {WITHDRAWAL_WEI} wei credited)")
    accepts = guest_succ == 1
    if spec_rejects and accepts:
        print("RESULT: spec REJECTS + guest ACCEPTS => FALSE ACCEPT CONFIRMED")
    elif not accepts:
        print(
            "RESULT: guest REJECTS => something else validates withdrawal "
            "credits; claim withdrawn"
        )
    else:
        print("RESULT: unexpected combination; inspect artifacts in work dir")


if __name__ == "__main__":
    main()
