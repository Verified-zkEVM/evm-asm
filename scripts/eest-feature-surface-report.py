#!/usr/bin/env python3
"""Map EEST stateless fixtures to missing stateless-guest feature surfaces.

The output is a scheduling aid for feature-completeness work: it classifies
fixture blocks by the EVM/EL surface they are likely to require, and points to
the bead that owns that surface. Classification is path-based so it stays cheap
and can be rerun whenever the fixture set changes.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Surface:
    key: str
    title: str
    bead: str
    default_filter: str
    patterns: tuple[str, ...]


@dataclass(frozen=True)
class OpcodeFamily:
    key: str
    title: str
    bead: str
    default_filter: str
    patterns: tuple[str, ...]


SURFACES: tuple[Surface, ...] = (
    Surface(
        key="scenarios",
        title="frontier scenario matrices",
        bead="evm-asm-fhsxz.2.4.2.54.2",
        default_filter="frontier/scenarios/scenarios/scenarios",
        patterns=(
            "frontier/scenarios/scenarios/scenarios",
            "frontier/scenarios/test_scenarios",
        ),
    ),
    Surface(
        key="tx",
        title="simple tx/value transfer",
        bead="evm-asm-fhsxz.2.4.2.56",
        default_filter="validation/transaction",
        patterns=(
            "validation/transaction",
            "tx_type",
            "transaction_validity",
            "tx_intrinsic_gas",
            "set_code_tx",
            "eip1559_fee_market_change",
        ),
    ),
    Surface(
        key="gas",
        title="gas accounting",
        bead="evm-asm-fhsxz.2.4.2.57",
        default_filter="precompile_warming",
        patterns=(
            "gas_cost",
            "gas_costs",
            "gas_accounting",
            "precompile_warming",
            "warm_status",
            "access_list",
            "memory_expansion",
            "oog",
            "_gas",
            "refund",
            "calldata_floor",
            "state_gas",
            "blob_base_fee",
        ),
    ),
    Surface(
        key="state",
        title="witness-backed state reads",
        bead="evm-asm-fhsxz.2.4.2.58",
        default_filter="sload_non_const",
        patterns=(
            "sload",
            "balance",
            "extcode",
            "selfbalance",
            "blockhash",
            "witness_state_reads",
            "witness_bytecodes",
            "account",
        ),
    ),
    Surface(
        key="post-state",
        title="general post-state root",
        bead="evm-asm-fhsxz.2.4.2.59",
        default_filter="sstore_non_const",
        patterns=(
            "sstore",
            "tstore",
            "tload",
            "storage",
            "state_writes",
            "state_deletes",
            "selfdestruct",
            "block_access_lists",
            "withdrawal_requests",
            "deposits",
            "consolidations",
            "requests",
            "system_contracts",
            "state_creation",
        ),
    ),
    Surface(
        key="opcode",
        title="opcode dispatcher",
        bead="evm-asm-fhsxz.2.4.2.60",
        default_filter="frontier/opcodes",
        patterns=(
            "frontier/opcodes",
            "all_opcodes",
            "mcopy",
            "blobhash_opcode",
            "blobgasfee_opcode",
            "count_leading_zeros",
            "dupn_swapn_exchange",
            "push0",
            "shift",
            "exp",
            "calldataload",
            "calldatacopy",
            "calldatasize",
            "codecopy",
            "jump",
        ),
    ),
    Surface(
        key="call-create",
        title="call/create frames",
        bead="evm-asm-fhsxz.2.4.2.61",
        default_filter="stCallCodes",
        patterns=(
            "callcode",
            "delegatecall",
            "staticcall",
            "call_",
            "/call",
            "create",
            "create2",
            "initcode",
            "return_data",
            "returndata",
            "reentrancy",
        ),
    ),
    Surface(
        key="precompile",
        title="precompile dispatch",
        bead="evm-asm-fhsxz.2.4.2.62",
        default_filter="frontier/precompiles",
        patterns=(
            "precompile",
            "precompiled",
            "identity_precompile",
            "ecrecover",
            "ripemd",
            "modexp",
            "ecadd",
            "ecmul",
            "ecpairing",
            "blake2",
            "bls12",
            "point_evaluation",
            "p256verify",
        ),
    ),
    Surface(
        key="receipts-logs",
        title="receipts/logs/bloom",
        bead="evm-asm-fhsxz.2.4.2.63",
        default_filter="log0_non_const",
        patterns=(
            "/log",
            "logs",
            "receipt",
            "bloom",
            "eth_transfer_logs",
            "burn_logs",
            "transfer_logs",
        ),
    ),
    Surface(
        key="advanced",
        title="advanced fork features",
        bead="evm-asm-fhsxz.8",
        default_filter="eip4844_blobs",
        patterns=(
            "blob",
            "kzg",
            "peerdas",
            "slotnum",
            "optional_proofs",
            "witness_headers",
            "witness_public_keys",
            "validation_codes",
            "parent_beacon_block_root",
            "beacon_root",
            "excess_blob_gas",
            "max_block_rlp_size",
            "block_rlp_limit",
            "max_contract_size",
            "max_code_size",
            "max_initcode_size",
        ),
    ),
)


OPCODE_FAMILIES: tuple[OpcodeFamily, ...] = (
    OpcodeFamily(
        key="arithmetic-bitwise-comparison",
        title="arithmetic, bitwise, comparison, stack",
        bead="evm-asm-fhsxz.2.4.2.60.2",
        default_filter="frontier/opcodes",
        patterns=(
            "frontier/opcodes",
            "add",
            "sub",
            "mul",
            "div",
            "mod",
            "sdiv",
            "smod",
            "addmod",
            "mulmod",
            "exp",
            "signextend",
            "lt",
            "gt",
            "slt",
            "sgt",
            "eq",
            "iszero",
            "and",
            "or",
            "xor",
            "not",
            "byte",
            "shl",
            "shr",
            "sar",
            "shift",
            "clz",
            "count_leading_zeros",
            "push",
            "dup",
            "swap",
            "dupn_swapn_exchange",
        ),
    ),
    OpcodeFamily(
        key="memory-calldata-returndata",
        title="memory, calldata, code, returndata",
        bead="evm-asm-fhsxz.2.4.2.60.3",
        default_filter="frontier/opcodes",
        patterns=(
            "mload",
            "mstore",
            "mstore8",
            "msize",
            "mcopy",
            "memory_expansion",
            "calldataload",
            "calldatasize",
            "calldatacopy",
            "codesize",
            "codecopy",
            "returndatasize",
            "returndatacopy",
            "return_data",
            "returndata",
        ),
    ),
    OpcodeFamily(
        key="control-halting-exceptions",
        title="control flow, halting, exceptional exits",
        bead="evm-asm-fhsxz.2.4.2.60.4",
        default_filter="frontier/opcodes",
        patterns=(
            "jump",
            "jumpi",
            "jumpdest",
            "invalid_addr",
            "invalid_jump",
            "stack_underflow",
            "stack_overflow",
            "oog",
            "out_of_gas",
            "stop",
            "return",
            "revert",
            "invalid",
            "pc",
        ),
    ),
    OpcodeFamily(
        key="environment-block-context",
        title="environment and block context reads",
        bead="evm-asm-fhsxz.2.4.2.60.5",
        default_filter="frontier/opcodes",
        patterns=(
            "address",
            "balance",
            "origin",
            "caller",
            "callvalue",
            "gasprice",
            "coinbase",
            "timestamp",
            "number",
            "prevrandao",
            "difficulty",
            "gaslimit",
            "chainid",
            "selfbalance",
            "basefee",
            "blobhash",
            "blobgasfee",
            "blockhash",
            "extcodesize",
            "extcodehash",
            "extcodecopy",
            "extcode",
        ),
    ),
    OpcodeFamily(
        key="storage-logs-selfdestruct",
        title="storage, logs, transient storage, SELFDESTRUCT",
        bead="evm-asm-fhsxz.2.4.2.60.6",
        default_filter="frontier/opcodes",
        patterns=(
            "sload",
            "sstore",
            "tload",
            "tstore",
            "log0",
            "log1",
            "log2",
            "log3",
            "log4",
            "/log",
            "logs",
            "selfdestruct",
            "eip6780_selfdestruct",
        ),
    ),
    OpcodeFamily(
        key="call-create-frames",
        title="CALL-family and CREATE-family frames",
        bead="evm-asm-fhsxz.2.4.2.61.1",
        default_filter="stCallCodes",
        patterns=(
            "callcode",
            "delegatecall",
            "staticcall",
            "call_",
            "/call",
            "create",
            "create2",
            "initcode",
            "reentrancy",
        ),
    ),
    OpcodeFamily(
        key="precompile-dispatch",
        title="CALL/STATICCALL precompile dispatch",
        bead="evm-asm-fhsxz.2.4.2.62",
        default_filter="frontier/precompiles",
        patterns=(
            "precompile",
            "precompiled",
            "identity_precompile",
            "ecrecover",
            "ripemd",
            "sha256",
            "modexp",
            "ecadd",
            "ecmul",
            "ecpairing",
            "blake2",
            "bls12",
            "point_evaluation",
            "p256verify",
        ),
    ),
)


def iter_stateless_fixture_paths(fixtures_dir: Path):
    for path in sorted(fixtures_dir.rglob("*.json")):
        if ".meta" in path.parts:
            continue
        relpath = str(path.relative_to(fixtures_dir))
        try:
            doc = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as exc:
            print(f"warn: cannot parse {path}: {exc}")
            continue
        for tc in doc.values():
            if not isinstance(tc, dict):
                continue
            blocks = tc.get("blocks")
            if not isinstance(blocks, list):
                continue
            for block in blocks:
                if (
                    isinstance(block, dict)
                    and block.get("statelessInputBytes")
                    and block.get("statelessOutputBytes")
                ):
                    yield relpath


def match_surfaces(relpath: str) -> list[Surface]:
    lower = relpath.lower()
    return [
        surface
        for surface in SURFACES
        if any(pattern.lower() in lower for pattern in surface.patterns)
    ]


def normalized_tokens(relpath: str) -> tuple[str, set[str]]:
    lower = relpath.lower()
    normalized = re.sub(r"[^a-z0-9]+", "_", lower).strip("_")
    return normalized, set(filter(None, normalized.split("_")))


def opcode_pattern_matches(
    relpath: str, normalized: str, tokens: set[str], pattern: str
) -> bool:
    lower_pattern = pattern.lower()
    if "/" in lower_pattern:
        return lower_pattern in relpath.lower()
    pattern_norm = re.sub(r"[^a-z0-9]+", "_", lower_pattern).strip("_")
    if "_" in pattern_norm:
        return pattern_norm in normalized
    return pattern_norm in tokens


def match_opcode_families(relpath: str) -> list[OpcodeFamily]:
    normalized, tokens = normalized_tokens(relpath)
    return [
        family
        for family in OPCODE_FAMILIES
        if any(
            opcode_pattern_matches(relpath, normalized, tokens, pattern)
            for pattern in family.patterns
        )
    ]


def render_markdown(rows: list[dict[str, object]], unclassified: dict[str, object]) -> None:
    print("| surface | blocks | fixture files | bead | example filter |")
    print("| --- | ---: | ---: | --- | --- |")
    for row in rows:
        print(
            "| {title} | {blocks} | {files} | `{bead}` | `{filter}` |".format(
                **row
            )
        )
    print(
        "| unclassified / mixed | {blocks} | {files} | inspect manually | n/a |".format(
            **unclassified
        )
    )


def render_tsv(rows: list[dict[str, object]], unclassified: dict[str, object]) -> None:
    print("key\ttitle\tblocks\tfixture_files\tbead\texample_filter\texamples")
    for row in rows:
        print(
            "{key}\t{title}\t{blocks}\t{files}\t{bead}\t{filter}\t{examples}".format(
                **row
            )
        )
    print(
        "unclassified\tunclassified / mixed\t{blocks}\t{files}\tinspect manually\tn/a\t{examples}".format(
            **unclassified
        )
    )


def main() -> int:
    root = repo_root()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fixtures-dir",
        type=Path,
        default=root
        / "gen-out"
        / "eest-fixtures"
        / "zkevm@v0.4.0"
        / "fixtures"
        / "fixtures",
    )
    parser.add_argument("--format", choices=("markdown", "tsv"), default="markdown")
    parser.add_argument(
        "--opcode-families",
        action="store_true",
        help="report opcode-family fixture groups instead of broad feature surfaces",
    )
    parser.add_argument(
        "--example-limit",
        type=int,
        default=3,
        help="number of fixture relpath examples to keep per surface",
    )
    args = parser.parse_args()

    if args.example_limit < 0:
        parser.error("--example-limit must be nonnegative")
    if not args.fixtures_dir.is_dir():
        parser.error(f"fixtures dir not found: {args.fixtures_dir}")

    items = OPCODE_FAMILIES if args.opcode_families else SURFACES
    matcher = match_opcode_families if args.opcode_families else match_surfaces

    counts = {surface.key: 0 for surface in items}
    files = {surface.key: set() for surface in items}
    examples = {surface.key: [] for surface in items}
    unclassified_count = 0
    unclassified_files: set[str] = set()
    unclassified_examples: list[str] = []

    for relpath in iter_stateless_fixture_paths(args.fixtures_dir):
        matches = matcher(relpath)
        if not matches:
            unclassified_count += 1
            unclassified_files.add(relpath)
            if (
                relpath not in unclassified_examples
                and len(unclassified_examples) < args.example_limit
            ):
                unclassified_examples.append(relpath)
            continue
        for surface in matches:
            counts[surface.key] += 1
            files[surface.key].add(relpath)
            if (
                relpath not in examples[surface.key]
                and len(examples[surface.key]) < args.example_limit
            ):
                examples[surface.key].append(relpath)

    rows: list[dict[str, object]] = []
    for surface in items:
        rows.append(
            {
                "key": surface.key,
                "title": surface.title,
                "blocks": counts[surface.key],
                "files": len(files[surface.key]),
                "bead": surface.bead,
                "filter": surface.default_filter,
                "examples": "; ".join(examples[surface.key]),
            }
        )
    rows.sort(key=lambda row: (-int(row["blocks"]), str(row["key"])))
    unclassified = {
        "blocks": unclassified_count,
        "files": len(unclassified_files),
        "examples": "; ".join(unclassified_examples),
    }

    if args.format == "markdown":
        render_markdown(rows, unclassified)
    else:
        render_tsv(rows, unclassified)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
