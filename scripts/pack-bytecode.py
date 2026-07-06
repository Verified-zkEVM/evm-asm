#!/usr/bin/env python3
"""
pack-bytecode.py — pack a bytecode (and optional calldata) into a
ziskemu `-i <file>` payload.

Used by M8.5's `scripts/codegen-opcodes-runtime-check.sh` to turn
the bytecode column of `lake exe codegen --list-test-cases` (which
mirrors `EvmAsm/Codegen/Tests/Cases.lean`'s `bytecode` field, e.g.
`"0x60, 0x02, 0x60, 0x0a, 0x04, 0x00"`) into a binary file the
runtime-bytecode dispatcher reads at `INPUT_ADDR + INPUT_DATA_OFFSET`.

M21 extension: optionally append a calldata segment, length-prefixed,
so the dispatcher's prologue can populate `env.callDataPtr` /
`env.callDataLen` and CALLDATALOAD / CALLDATACOPY can read real bytes.

M22 extension: optionally append a third segment carrying a list of
(storage-key, storage-value) pairs. The dispatcher prologue copies
them into a writable in-`.data` slot table; SLOAD / SSTORE read /
mutate the table via linear scan.

M28 extension: optionally append a fourth segment carrying blob
context: the BLOBBASEFEE value as one EVM stack word, followed by the
transaction's BLOBHASH versioned-hash list. The dispatcher prologue
copies these into blob-context slots; opcodes 0x4a / 0x49 read them.
Both default to zero/empty.

M29 extension: optionally append a fifth segment carrying BLOCKHASH
runtime context: current block number plus recent ancestor hashes in
increasing block-number order. The dispatcher prologue copies up to
256 hashes into a bounded table. BLOCKHASH(target) uses the Amsterdam
execution-spec window rule: target must be older than the current block
and within the supplied recent-hash list, otherwise it returns zero.

M29 extension: optionally append a fifth segment carrying the 13 simple
environment opcode words in `EvmEnv` 32-byte slot order, followed by the
EIP-7843 SLOTNUM word. The dispatcher
prologue copies those words into `evm_env` so ADDRESS, ORIGIN, CALLER,
CALLVALUE, GASPRICE, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT,
CHAINID, SELFBALANCE, and BASEFEE can read nonzero runtime values.

M31 extension: optionally append account-witness context for runtime
BALANCE/EXTCODE* handlers: parent header RLP, witness.state, and
witness.codes. The dispatcher stores pointers and lengths in `evm_env`;
zero header length means no witness context is available.

Usage:
    pack-bytecode.py "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00" output.bin
    pack-bytecode.py --calldata "0xdeadbeef" "0x36, 0x00" output.bin
    pack-bytecode.py --storage "(0x00, 0xdead)" "0x60, 0x00, 0x54, 0x00" output.bin
    pack-bytecode.py --blob-base-fee 0x1234 "0x4a, 0x00" output.bin
    pack-bytecode.py --blob-hashes "0xabc...,0xdef..." "0x60, 0x00, 0x49, 0x00" output.bin
    pack-bytecode.py --env "caller=0x1234,timestamp=0x2a" "0x33, 0x00" output.bin
    echo "0x60, 0x00" | pack-bytecode.py - output.bin

Output layout:

    bytes 0..8         <8-byte LE u64 length of bytecode>
    bytes 8..          <bytecode bytes>
                       <zero pad to 8-byte boundary>
    next 8 bytes       <8-byte LE u64 length of calldata>
    following          <calldata bytes>
                       <zero pad to 8-byte boundary>
    next 8 bytes       <8-byte LE u64 slot_count>            (M22)
    following          <slot_count × 64-byte (key, value)>   (M22)
                       <zero pad to 8-byte boundary>
    next 32 bytes      <blob_base_fee as EVM stack word>      (M28)
    next 8 bytes       <8-byte LE u64 blob_hash_count>        (M28)
    following          <count × 32-byte versioned hash words> (M28)
    next 8 bytes       <8-byte LE u64 current_block_number>  (M29)
    next 8 bytes       <8-byte LE u64 block_hash_count>      (M29)
    following          <count × 32-byte recent hashes>       (M29)
                       Hashes are passed as normal big-endian hex and
                       serialized in EVM-stack byte order.
    next 416 bytes     <13 simple env words in evm_env order>
    next 32 bytes      <SLOTNUM word>
    next 8 bytes       <8-byte LE u64 gas limit>             (M30)
    next 8 bytes       <8-byte LE u64 validate tx gas flag>  (M35)
    next 8 bytes       <8-byte LE u64 is contract creation>  (M35)
    next 8 bytes       <8-byte LE u64 parent header RLP len> (M31)
    next 8 bytes       <8-byte LE u64 witness.state len>     (M31)
    next 8 bytes       <8-byte LE u64 witness.codes len>     (M31)
    following          <header RLP || witness.state || witness.codes>

ziskemu prepends 8 more bytes of its own metadata when loading,
landing the bytecode-length prefix at INPUT_ADDR+8 and the bytecode
at INPUT_ADDR+16 — which is where the runtime-bytecode dispatcher's
`li x10, 0x40000010` points. The calldata-length prefix lands at
the first 8-byte boundary past the bytecode bytes; the dispatcher
prologue computes those addresses at startup, then chains to the
slot-count prefix at the first 8-byte boundary past the calldata.

Backwards-compatible: pre-M21 callers that don't pass --calldata get
a zero-length calldata segment appended, which preserves the M17
"CALLDATA opcodes are no-op" behavior for existing test cases.
Pre-M22 callers that don't pass --storage get a zero-length storage
segment appended (SLOAD returns 0, SSTORE appends to an empty table).
Pre-M28 callers that don't pass --blob-base-fee / --blob-hashes get
a zero word and an empty versioned-hash list.
Pre-M29 callers that don't pass --block-hashes get current block 0 and
an empty recent-hash table (BLOCKHASH returns 0).
Pre-env callers that don't pass --env get zero words for every simple
environment opcode.
Pre-M35 callers that don't pass --validate-tx-gas preserve the runtime
dispatcher's old behavior: the gas trailer is treated as already-available
execution gas. When --validate-tx-gas is set, the dispatcher treats --gas as
transaction gas, computes Amsterdam call/create intrinsic gas plus the
EIP-7623 calldata floor from calldata, rejects if the transaction gas cannot
cover max(intrinsic, floor), and starts opcode execution with gas - intrinsic.
Pre-M31 callers that don't pass --state-header-rlp get a zero-length
account-witness context.
"""
import argparse
import re
import struct
import sys

ENV_FIELDS = [
    "address",
    "self_balance",
    "caller",
    "call_value",
    "origin",
    "gas_price",
    "coinbase",
    "timestamp",
    "number",
    "prevrandao",
    "gas_limit",
    "base_fee",
    "chain_id",
    "slot_number",
]

ENV_ALIASES = {
    "selfbalance": "self_balance",
    "self_balance": "self_balance",
    "callvalue": "call_value",
    "call_value": "call_value",
    "tx_origin": "origin",
    "gasprice": "gas_price",
    "gas_price": "gas_price",
    "prev_randao": "prevrandao",
    "prevrandao": "prevrandao",
    "gaslimit": "gas_limit",
    "gas_limit": "gas_limit",
    "basefee": "base_fee",
    "base_fee": "base_fee",
    "chainid": "chain_id",
    "chain_id": "chain_id",
}

ENV_ALIASES.update({field: field for field in ENV_FIELDS})


def parse_csv(csv: str) -> bytes:
    """Parse a `0xNN, 0xMM, ...` string into raw bytes."""
    tokens = re.findall(r"0[xX][0-9a-fA-F]+", csv)
    if not tokens:
        raise ValueError(f"no `0xNN` tokens in input: {csv!r}")
    return bytes(int(t, 16) for t in tokens)


def parse_calldata(calldata_arg: str) -> bytes:
    """Parse a calldata arg as either CSV (`0x60, 0x42`) or hex blob
    (`0xdeadbeef` or `deadbeef`). Empty string returns empty bytes."""
    s = calldata_arg.strip()
    if not s:
        return b""
    # CSV form (has commas)?
    if "," in s:
        return parse_csv(s)
    # Hex-blob form, with optional 0x prefix
    if s.startswith(("0x", "0X")):
        s = s[2:]
    if len(s) % 2 != 0:
        raise ValueError(f"hex blob has odd length: {calldata_arg!r}")
    return bytes.fromhex(s)


def parse_bytes_arg(value: str) -> bytes:
    """Parse a byte blob argument. `@path` reads raw bytes from a file;
    otherwise the value is parsed like calldata (CSV or hex blob)."""
    s = value.strip()
    if not s:
        return b""
    if s.startswith("@"):
        with open(s[1:], "rb") as f:
            return f.read()
    return parse_calldata(s)


def pad_to_8(buf: bytes) -> bytes:
    """Zero-pad a bytes buffer up to the next 8-byte boundary."""
    pad = (-len(buf)) % 8
    if pad:
        buf += b"\x00" * pad
    return buf


def parse_storage(storage_arg: str) -> list[tuple[bytes, bytes]]:
    """Parse a --storage arg into a list of (key, value) byte pairs,
    each in EVM-stack representation (4 little-endian u64 limbs, low
    limb first).

    Supported forms:
    - Empty: returns [].
    - Parenthesized pairs: "(0xKEY, 0xVAL) (0xKEY2, 0xVAL2)" where
      each KEY / VAL is a hex blob (with optional 0x prefix)
      interpreted as a u256 integer. The serialized bytes are the
      reverse of the natural 32-byte big-endian encoding — that is
      the layout PUSH32 + SSTORE would deposit on the EVM stack
      (see push32_basic in Tests/Cases.lean).
    """
    s = storage_arg.strip()
    if not s:
        return []
    pairs = re.findall(
        r"\(\s*(0[xX][0-9a-fA-F]+|[0-9a-fA-F]+)\s*,"
        r"\s*(0[xX][0-9a-fA-F]+|[0-9a-fA-F]+)\s*\)",
        s,
    )
    if not pairs:
        raise ValueError(f"no `(key, value)` pairs in --storage: {storage_arg!r}")
    out: list[tuple[bytes, bytes]] = []
    for raw_key, raw_val in pairs:
        out.append((_to_stack_bytes(raw_key), _to_stack_bytes(raw_val)))
    return out


def parse_blob_hashes(blob_hashes_arg: str) -> list[bytes]:
    """Parse --blob-hashes into 32-byte words in EVM-stack representation.

    Supported forms:
    - Empty: returns [].
    - Comma/space-separated hex blobs: "0xHASH, 0xHASH2".
      Each blob is interpreted as a 32-byte big-endian versioned hash
      and serialized in the same stack-word representation as PUSH32.
    """
    s = blob_hashes_arg.strip()
    if not s:
        return []
    tokens = re.findall(r"0[xX][0-9a-fA-F]+|[0-9a-fA-F]+", s)
    if not tokens:
        raise ValueError(f"no hex blobs in --blob-hashes: {blob_hashes_arg!r}")
    out: list[bytes] = []
    for token in tokens:
        out.append(_to_stack_bytes(token))
    return out


def parse_block_hashes(block_hashes_arg: str) -> list[bytes]:
    """Parse --block-hashes into EVM-stack byte order hashes.

    Supported forms:
    - Empty: returns [].
    - Comma or whitespace separated hex blobs, each exactly 32 bytes
      after optional 0x prefix.
    """
    s = block_hashes_arg.strip()
    if not s:
        return []
    tokens = re.findall(r"0[xX][0-9a-fA-F]+|[0-9a-fA-F]+", s)
    if not tokens:
        raise ValueError(f"no hashes in --block-hashes: {block_hashes_arg!r}")
    out: list[bytes] = []
    for token in tokens:
        raw = token[2:] if token.startswith(("0x", "0X")) else token
        if len(raw) != 64:
            raise ValueError(f"block hash must be exactly 32 bytes: {token!r}")
        out.append(bytes.fromhex(raw)[::-1])
    return out


def parse_env(env_arg: str) -> dict[str, bytes]:
    """Parse a simple-env trailer spec into field -> stack-word bytes.

    Supported form: comma- or whitespace-separated `field=0xVALUE` pairs.
    Field names accept opcode-style spellings (`CALLVALUE`, `SELFBALANCE`)
    and snake_case names (`call_value`, `self_balance`).
    """
    s = env_arg.strip()
    if not s:
        return {}
    out: dict[str, bytes] = {}
    for item in re.split(r"[\s,]+", s):
        if not item:
            continue
        if "=" not in item:
            raise ValueError(f"bad --env item {item!r}; expected field=0xVALUE")
        raw_name, raw_value = item.split("=", 1)
        key = raw_name.strip().lower().replace("-", "_")
        field = ENV_ALIASES.get(key)
        if field is None:
            known = ", ".join(ENV_FIELDS)
            raise ValueError(f"unknown --env field {raw_name!r}; known fields: {known}")
        out[field] = _to_stack_bytes(raw_value)
    return out


def _to_stack_bytes(hex_blob: str) -> bytes:
    """Decode a hex blob (with optional 0x prefix) as a u256 integer
    and serialize as 32 bytes in EVM-stack representation: 4 LE u64
    limbs, low limb first. Equivalent to reversing the BE 32-byte
    encoding the user would naturally write."""
    s = hex_blob.strip()
    if s.startswith(("0x", "0X")):
        s = s[2:]
    if len(s) % 2 != 0:
        s = "0" + s  # nibble alignment
    raw_be = bytes.fromhex(s)
    if len(raw_be) > 32:
        raise ValueError(f"storage key/value > 32 bytes: {hex_blob!r}")
    raw_be = b"\x00" * (32 - len(raw_be)) + raw_be
    return raw_be[::-1]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pack a bytecode (and optional calldata) into a "
                    "ziskemu input file."
    )
    parser.add_argument(
        "bytecode",
        help="Comma-separated bytecode (e.g. '0x60, 0x02, 0x00'). "
             "Use '-' to read from stdin.",
    )
    parser.add_argument(
        "output",
        help="Path to write the packed binary. Use '-' for stdout.",
    )
    parser.add_argument(
        "--calldata",
        default="",
        help="Optional calldata, as either CSV ('0x60, 0x42') or a "
             "hex blob ('0xdeadbeef'). Defaults to empty (back-compat).",
    )
    parser.add_argument(
        "--storage",
        default="",
        help="Optional storage preload: parenthesized hex pairs like "
             "'(0x00, 0xdead) (0x01, 0xbeef)'. Each key / value is "
             "interpreted as a u256 integer and serialized in EVM-stack "
             "byte order. Defaults to empty (no preload).",
    )
    parser.add_argument(
        "--blob-base-fee",
        default="",
        help="Optional BLOBBASEFEE value as a u256 hex integer. Serialized "
             "in EVM-stack byte order. Defaults to zero.",
    )
    parser.add_argument(
        "--blob-hashes",
        default="",
        help="Optional comma/space-separated BLOBHASH versioned hashes. Each "
             "entry is a 32-byte hex blob serialized in EVM-stack byte order.",
    )
    parser.add_argument(
        "--block-number",
        default="0",
        help="Current block number for BLOCKHASH context. Accepts decimal "
             "or 0x-prefixed integer. Defaults to 0.",
    )
    parser.add_argument(
        "--block-hashes",
        default="",
        help="Optional recent ancestor hashes for BLOCKHASH, in increasing "
             "block-number order. Pass comma/space-separated 32-byte hex "
             "hashes. Defaults to empty.",
    )
    parser.add_argument(
        "--env",
        default="",
        help="Optional simple environment values as comma- or whitespace-"
             "separated field=hex pairs, e.g. 'caller=0x1234,timestamp=0x2a'. "
             "Fields are address, self_balance, caller, call_value, origin, "
             "gas_price, coinbase, timestamp, number, prevrandao, gas_limit, "
             "base_fee, chain_id, slot_number. Defaults to zero for every field.",
    )
    parser.add_argument(
        "--gas",
        default="30000000",
        help="Gas limit for the run (M30). Accepts decimal or 0x-prefixed "
             "integer; must fit in u64. The dispatch loop charges each "
             "opcode's static base cost against this; underflow halts with "
             "halt_kind = 6. Defaults to 30,000,000.",
    )
    parser.add_argument(
        "--validate-tx-gas",
        action="store_true",
        help="Treat --gas as transaction gas and ask the runtime dispatcher "
             "to validate max(intrinsic gas, calldata floor) and deduct "
             "intrinsic gas before opcode execution. Defaults off for "
             "backwards-compatible opcode-runtime tests.",
    )
    parser.add_argument(
        "--tx-is-creation",
        action="store_true",
        help="With --validate-tx-gas, include the contract-creation intrinsic "
             "gas component. Defaults to a normal call transaction.",
    )
    parser.add_argument(
        "--state-header-rlp",
        default="",
        help="Optional parent header RLP for account-witness runtime context. "
             "Use @path to read raw bytes from a file, or pass a hex blob/CSV.",
    )
    parser.add_argument(
        "--witness-state",
        default="",
        help="Optional witness.state SSZ section for account-witness runtime "
             "context. Use @path to read raw bytes from a file.",
    )
    parser.add_argument(
        "--witness-codes",
        default="",
        help="Optional witness.codes SSZ section for EXTCODE* runtime context. "
             "Use @path to read raw bytes from a file.",
    )
    args = parser.parse_args()

    csv = sys.stdin.read() if args.bytecode == "-" else args.bytecode
    bytecode = parse_csv(csv)
    calldata = parse_calldata(args.calldata)
    storage_pairs = parse_storage(args.storage)
    blob_base_fee = _to_stack_bytes(args.blob_base_fee) if args.blob_base_fee.strip() else b"\x00" * 32
    blob_hashes = parse_blob_hashes(args.blob_hashes)
    current_block_number = int(args.block_number, 0)
    if current_block_number < 0 or current_block_number > 0xFFFFFFFFFFFFFFFF:
        raise ValueError("--block-number must fit in u64")
    block_hashes = parse_block_hashes(args.block_hashes)
    env_words = {field: b"\x00" * 32 for field in ENV_FIELDS}
    env_words.update(parse_env(args.env))
    gas_limit = int(args.gas, 0)
    if gas_limit < 0 or gas_limit > 0xFFFFFFFFFFFFFFFF:
        raise ValueError("--gas must fit in u64")
    state_header_rlp = parse_bytes_arg(args.state_header_rlp)
    witness_state = parse_bytes_arg(args.witness_state)
    witness_codes = parse_bytes_arg(args.witness_codes)
    if not state_header_rlp and (witness_state or witness_codes):
        raise ValueError("--witness-state/--witness-codes require --state-header-rlp")

    # Bytecode segment: 8B LE length prefix + bytes, padded to 8-byte boundary
    # so the calldata-length cell that follows is aligned.
    packed = struct.pack("<Q", len(bytecode)) + bytecode
    packed = pad_to_8(packed)

    # Calldata segment: 8B LE length prefix + bytes, padded to 8-byte boundary
    # so the storage-count cell that follows is aligned.
    packed += struct.pack("<Q", len(calldata)) + calldata
    packed = pad_to_8(packed)

    # M22 storage segment: 8B LE slot count + slot_count × 64-byte
    # (key, value) pairs, padded to 8-byte boundary so the entire
    # input file size is a multiple of 8 (ziskemu requires this).
    packed += struct.pack("<Q", len(storage_pairs))
    for key, value in storage_pairs:
        packed += key + value
    packed = pad_to_8(packed)

    # M28 blob-context trailer. All words use stack representation.
    packed += blob_base_fee
    packed += struct.pack("<Q", len(blob_hashes))
    for blob_hash in blob_hashes:
        packed += blob_hash

    # M29 BLOCKHASH context: current block number + bounded recent
    # ancestor hashes. The dispatcher clamps the count to 256.
    packed += struct.pack("<Q", current_block_number)
    packed += struct.pack("<Q", len(block_hashes))
    for block_hash in block_hashes:
        packed += block_hash
    packed = pad_to_8(packed)

    # M29/M34 environment trailer: 13 `EvmEnv` stack words plus SLOTNUM.
    for field in ENV_FIELDS:
        packed += env_words[field]

    # M30 gas-limit trailer: 8B LE u64, read by the runtime prologue into
    # env.gasRemaining (env+568).
    packed += struct.pack("<Q", gas_limit)

    # M35 optional transaction intrinsic-gas validation controls.
    packed += struct.pack("<Q", 1 if args.validate_tx_gas else 0)
    packed += struct.pack("<Q", 1 if args.tx_is_creation else 0)

    # M31 account-witness context trailer. The three length cells are always
    # present so old callers get deterministic zero-context behavior.
    packed += struct.pack("<Q", len(state_header_rlp))
    packed += struct.pack("<Q", len(witness_state))
    packed += struct.pack("<Q", len(witness_codes))
    packed += state_header_rlp + witness_state + witness_codes
    packed = pad_to_8(packed)

    if args.output == "-":
        sys.stdout.buffer.write(packed)
    else:
        with open(args.output, "wb") as f:
            f.write(packed)

    return 0


if __name__ == "__main__":
    sys.exit(main())
