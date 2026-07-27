#!/usr/bin/env python3
"""Convert EEST "zkevm" stateless fixtures into ziskemu guest inputs.

The EEST zkevm fixtures (release line ``zkevm@vX.Y.Z``, targeting the
Amsterdam / Glamsterdam fork) are ``blockchain_tests`` whose blocks each
carry two extra hex fields:

  * ``statelessInputBytes``  -- the schema-prefixed (``0x1501...``) SSZ
    ``StatelessInput`` that ``run_stateless_guest`` consumes.
  * ``statelessOutputBytes`` -- the canonical SSZ
    ``StatelessValidationResult`` the guest is expected to produce.

This tool walks a directory of such fixtures and, for every block that
has ``statelessInputBytes``, writes a ziskemu ``-i`` input file in the
exact layout ``scripts/stateless-gen-input.py`` uses
(``<u64 LE length><blob><zero pad to 8>``), and emits a TSV manifest
that the harness (``codegen-eest-stateless-check.sh``) iterates.

The ``blob`` is intentionally the fixture's ``statelessInputBytes``
byte-for-byte.  The length prefix and zero padding are ziskemu host transport;
they are not part of execution-specs ``run_stateless_guest`` input content.
Manifest fields derived below are for launch/reporting only and must not become
a second authoritative guest input schema.

Manifest columns (tab-separated, one row per guest invocation):
  label  input_file  expected_hex  succ_bit  input_len  block_gas_limit  fixture_relpath

Usage:
  eest-stateless-to-input.py --fixtures-dir DIR --out-dir DIR
                             [--manifest FILE] [--skip N] [--limit N]
                             [--filter SUB] [--verify-input-parity]
                             [--verify-execution-spec-input]
                             [--verify-run-stateless-guest]

``--filter`` keeps only stateless blocks whose fixture relative path or
per-block EEST test label contains the given substring.  ``--skip`` drops the
first N selected stateless blocks after filtering, then ``--limit`` caps the
number of guest invocations emitted.
``--random --seed S`` first enumerates the filtered block rows and samples the
requested cap uniformly without replacement.  The positive control for this
mode is the sampled failure count: it should track the corpus failure rate;
an all-pass draw from a corpus with roughly a thousand failures signals a
clustered selection rather than evidence that the screen is clean.
``--verify-input-parity`` unpacks each emitted ziskemu input and checks that
the guest-visible blob is byte-for-byte the fixture's ``statelessInputBytes``.
``--verify-execution-spec-input`` additionally decodes that same blob through
the Python execution-specs stateless input path used by ``run_stateless_guest``.
``--verify-run-stateless-guest`` runs Python execution-specs
``run_stateless_guest`` on that same blob and requires the fixture's
``statelessOutputBytes`` to match; this is useful only when fixtures were
generated from the same execution-specs checkout.
"""
from __future__ import annotations

import argparse
import json
import os
import struct
import random
import sys
from pathlib import Path


def pack_ziskemu_input(blob: bytes) -> bytes:
    """Mirror scripts/stateless-gen-input.py: 8-byte LE length, blob, pad to 8."""
    total = 8 + len(blob)
    pad = (-total) % 8
    return struct.pack("<Q", len(blob)) + blob + (b"\x00" * pad)


def unpack_ziskemu_input(packed: bytes) -> bytes:
    """Inverse of pack_ziskemu_input, validating length and zero padding."""
    if len(packed) < 8:
        raise ValueError(f"packed input too short: {len(packed)}")
    n = struct.unpack("<Q", packed[:8])[0]
    end = 8 + n
    if len(packed) < end:
        raise ValueError(f"packed input truncated: length={n}, bytes={len(packed)}")
    pad = packed[end:]
    if any(pad):
        raise ValueError("packed input has non-zero padding")
    if len(pad) != (-end) % 8:
        raise ValueError(f"packed input has wrong padding length: {len(pad)}")
    return packed[8:end]


def sanitize(s: str) -> str:
    return "".join(c if c.isalnum() or c in "._-" else "_" for c in s)


def stateless_input_block_gas_limit(blob: bytes) -> int:
    """Return execution_payload.gas_limit from schema-prefixed StatelessInput."""
    off = 2 + 60 + 412
    end = off + 8
    if len(blob) < end:
        raise ValueError(f"statelessInputBytes too short for gas limit: {len(blob)}")
    return int.from_bytes(blob[off:end], "little")


# A uniform draw must SPAN the corpus. This is asserted in the script rather
# than described in the help text because the help text has now twice claimed
# corpus-wide sampling and been wrong -- first when --random never reached the
# converter at all (GH #10596), then when it sampled fixture FILES rather than
# blocks (GH #10597). Prose does not hold this contract.
#
# Exempted below a threshold because a genuinely small draw can legitimately
# land anywhere, and a check that fires on correct input is worse than none.
SPAN_CHECK_MIN_DRAW = 20
SPAN_CHECK_MIN_CORPUS_RATIO = 4


def selection_span_error(picked: list[int], corpus_len: int) -> str | None:
    """Return an error message if `picked` is not plausibly a uniform draw.

    `picked` are positions into the enumerated corpus. A uniform draw of k
    from n lands entirely in the first half with probability 2**-k, so for any
    non-tiny k a wholly front-loaded selection means the sampler is not
    sampling. Returns None when the selection is acceptable or the draw is too
    small for the test to carry.
    """
    k = len(picked)
    if k < SPAN_CHECK_MIN_DRAW or corpus_len <= SPAN_CHECK_MIN_CORPUS_RATIO * k:
        return None
    hi = max(picked)
    if hi < corpus_len // 2:
        return (
            f"sampler self-check FAILED -- {k} blocks drawn from {corpus_len} "
            f"but the highest corpus index is {hi}, entirely within the first "
            f"half. Under uniform sampling that is a 2**-{k} event, so the "
            f"selection is almost certainly not uniform. Refusing to emit a "
            f"manifest that would be reported as corpus-wide coverage."
        )
    return None


def iter_blocks(fixture_path: Path):
    """Yield (label, input_bytes, expected_bytes, block_gas_limit) for each stateless block."""
    try:
        doc = json.loads(fixture_path.read_text())
    except (json.JSONDecodeError, OSError) as exc:  # corrupt / unreadable
        print(f"  warn: cannot parse {fixture_path}: {exc}", file=sys.stderr)
        return
    for test_name, tc in doc.items():
        blocks = tc.get("blocks") if isinstance(tc, dict) else None
        if not isinstance(blocks, list):
            continue
        # Short, stable per-test tag (the part after the last "::").
        short = test_name.split("::")[-1] if "::" in test_name else test_name
        for bi, blk in enumerate(blocks):
            if not isinstance(blk, dict):
                continue
            sib = blk.get("statelessInputBytes")
            sob = blk.get("statelessOutputBytes")
            if not sib or not sob:
                continue  # block opted out of stateless validation
            try:
                ib = bytes.fromhex(sib[2:] if sib.startswith("0x") else sib)
                ob = bytes.fromhex(sob[2:] if sob.startswith("0x") else sob)
            except ValueError as exc:
                print(f"  warn: bad hex in {fixture_path}: {exc}", file=sys.stderr)
                continue
            try:
                gas_limit = stateless_input_block_gas_limit(ib)
            except ValueError:
                # Malformed inputs are guest test cases in v0.5.0:
                # `run_stateless_guest` returns a failed sentinel for them.
                gas_limit = 0
            label = sanitize(f"{short}#b{bi}")
            yield label, ib, ob, gas_limit


def load_execution_specs_input_decoder():
    """Import execution-specs lazily so normal conversion has no extra deps."""
    try:
        from ethereum.forks.amsterdam.stateless_guest import deserialize_stateless_input
        from ethereum_types.bytes import Bytes
    except ImportError as exc:
        raise RuntimeError(
            "execution-specs input verification must be run with execution-specs "
            "dependencies available, e.g. `uv run --directory execution-specs "
            "--quiet python3 ../scripts/eest-stateless-to-input.py ...`"
        ) from exc

    def decode(blob: bytes) -> None:
        deserialize_stateless_input(Bytes(blob))

    return decode


def load_run_stateless_guest():
    """Import execution-specs run_stateless_guest lazily."""
    try:
        from ethereum.forks.amsterdam.stateless_guest import run_stateless_guest
        from ethereum_types.bytes import Bytes
    except ImportError as exc:
        raise RuntimeError(
            "--verify-run-stateless-guest must be run with execution-specs "
            "dependencies available, e.g. `uv run --directory execution-specs "
            "--quiet python3 ../scripts/eest-stateless-to-input.py ...`"
        ) from exc

    def run(blob: bytes) -> bytes:
        return bytes(run_stateless_guest(Bytes(blob)))

    return run


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--fixtures-dir", required=True, type=Path)
    ap.add_argument("--out-dir", required=True, type=Path)
    ap.add_argument("--manifest", type=Path, default=None)
    ap.add_argument("--skip", type=int, default=0, help="skip first N selected invocations")
    ap.add_argument("--limit", type=int, default=0, help="cap invocations (0 = no cap)")
    ap.add_argument(
        "--random",
        action="store_true",
        help="sample stateless blocks uniformly without replacement before "
             "applying --skip/--limit; --filter narrows the population first. "
             "Requires --seed.",
    )
    ap.add_argument(
        "--seed", type=int, default=None,
        help="seed for --random; required with it so a run is reproducible",
    )
    ap.add_argument(
        "--filter",
        default="",
        help="keep blocks whose fixture relpath or test label contains this",
    )
    ap.add_argument(
        "--verify-input-parity",
        action="store_true",
        help="verify each emitted ziskemu input carries exactly statelessInputBytes",
    )
    ap.add_argument(
        "--verify-execution-spec-input",
        action="store_true",
        help="verify execution-specs can decode the exact guest input blob",
    )
    ap.add_argument(
        "--verify-run-stateless-guest",
        action="store_true",
        help="verify execution-specs run_stateless_guest(input) equals statelessOutputBytes",
    )
    args = ap.parse_args()

    if args.skip < 0:
        ap.error("--skip must be nonnegative")
    if args.limit < 0:
        ap.error("--limit must be nonnegative")
    if args.random and args.seed is None:
        ap.error("--random requires --seed (a run that cannot be reproduced is not a result)")
    if args.seed is not None and not args.random:
        ap.error("--seed is meaningless without --random")

    fixtures_dir: Path = args.fixtures_dir
    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = args.manifest or (out_dir / "manifest.tsv")
    try:
        decode_spec_input = (
            load_execution_specs_input_decoder()
            if args.verify_execution_spec_input or args.verify_run_stateless_guest
            else None
        )
        run_spec = load_run_stateless_guest() if args.verify_run_stateless_guest else None
    except RuntimeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    json_files = sorted(
        p for p in fixtures_dir.rglob("*.json")
        if ".meta" not in p.parts
    )

    selected = 0
    n = 0
    used_labels: set[str] = set()
    with manifest_path.open("w") as mf:
        def write_block(
            label: str,
            ib: bytes,
            ob: bytes,
            gas_limit: int,
            relpath: str,
        ) -> bool:
            nonlocal n
            # Make the label unique across fixtures by prefixing a counter.
            # Truncate the descriptive part so the on-disk filename stays
            # within the OS limit (255 bytes) -- blob test names with full
            # parametrization can be 200+ chars. The counter prefix already
            # guarantees uniqueness; the collision guard handles truncation
            # clashes.
            uniq = f"{n:05d}_{label[:96]}"
            if uniq in used_labels:
                uniq = f"{uniq}_{len(used_labels)}"
            used_labels.add(uniq)

            input_file = out_dir / f"{uniq}.input"
            packed = pack_ziskemu_input(ib)
            if args.verify_input_parity or decode_spec_input is not None:
                try:
                    recovered = unpack_ziskemu_input(packed)
                except ValueError as exc:
                    print(
                        f"  error: ziskemu input packing mismatch for "
                        f"{relpath} {label}: {exc}",
                        file=sys.stderr,
                    )
                    return False
                if recovered != ib:
                    print(
                        f"  error: ziskemu input blob differs from "
                        f"statelessInputBytes for {relpath} {label}",
                        file=sys.stderr,
                    )
                    return False
            if decode_spec_input is not None:
                try:
                    decode_spec_input(ib)
                except Exception as exc:
                    print(
                        f"  error: execution-specs cannot decode "
                        f"statelessInputBytes for {relpath} {label}: {exc}",
                        file=sys.stderr,
                    )
                    return False
            if run_spec is not None:
                spec_output = run_spec(ib)
                if spec_output != ob:
                    print(
                        f"  error: run_stateless_guest output differs from "
                        f"statelessOutputBytes for {relpath} {label}",
                        file=sys.stderr,
                    )
                    print(f"    spec:    {spec_output.hex()}", file=sys.stderr)
                    print(f"    fixture: {ob.hex()}", file=sys.stderr)
                    return False
            input_file.write_bytes(packed)
            succ_bit = ob[32] if len(ob) > 32 else -1
            mf.write(
                "\t".join(
                    [
                        uniq,
                        str(input_file),
                        ob.hex(),
                        str(succ_bit),
                        str(len(ib)),
                        str(gas_limit),
                        relpath,
                    ]
                )
                + "\n"
            )
            n += 1
            return True

        if args.random:
            # A fixture file often contains several blocks from the same
            # scenario. Shuffling files therefore samples fixture families,
            # not the individual blocks that the harness executes. Enumerate
            # the filtered block population, then draw rows directly.
            candidates = []
            for fp in json_files:
                relpath = str(fp.relative_to(fixtures_dir))
                for label, ib, ob, gas_limit in iter_blocks(fp):
                    if args.filter and args.filter not in relpath and args.filter not in label:
                        continue
                    candidates.append((label, ib, ob, gas_limit, relpath))

            if args.limit == 0 and args.skip == 0:
                # `--all --random` selects every row already; avoid creating a
                # needless complete permutation merely to change run order.
                sampled = candidates
            else:
                sample_count = len(candidates) if args.limit == 0 else min(
                    len(candidates), args.skip + args.limit
                )
                # Sample POSITIONS rather than elements so the selection can
                # be span-checked. random.sample picks indices independently
                # of element values, so for a population of the same length
                # this selects exactly what sample(candidates, k) would --
                # verified across seeds; existing seeds reproduce unchanged.
                picked = random.Random(args.seed).sample(
                    range(len(candidates)), sample_count
                )
                span_err = selection_span_error(picked, len(candidates))
                if span_err is not None:
                    print(f"error: {span_err}", file=sys.stderr)
                    return 1
                sampled = [candidates[i] for i in picked]
            for label, ib, ob, gas_limit, relpath in sampled[args.skip:]:
                if not write_block(label, ib, ob, gas_limit, relpath):
                    return 1
            if args.limit and len(candidates) > args.skip + args.limit:
                print(
                    f"==> limit {args.limit} reached; sampled blocks uniformly "
                    f"without replacement from {len(candidates)} candidates",
                    file=sys.stderr,
                )
            print(f"wrote {n} input(s) + manifest {manifest_path}")
            return 0

        for fp in json_files:
            relpath = str(fp.relative_to(fixtures_dir))
            for label, ib, ob, gas_limit in iter_blocks(fp):
                if args.filter and args.filter not in relpath and args.filter not in label:
                    continue
                if selected < args.skip:
                    selected += 1
                    continue
                selected += 1
                if args.limit and n >= args.limit:
                    print(
                        f"==> limit {args.limit} reached; stopping "
                        f"(more fixtures available -- truncated)",
                        file=sys.stderr,
                    )
                    mf.flush()
                    print(f"wrote {n} input(s) + manifest {manifest_path}")
                    return 0
                if not write_block(label, ib, ob, gas_limit, relpath):
                    return 1

    print(f"wrote {n} input(s) + manifest {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
