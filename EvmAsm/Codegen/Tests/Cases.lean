/-
  EvmAsm.Codegen.Tests.Cases

  Per-opcode regression test registry. Each `OpcodeTestCase` is a
  bytecode + expected output bytes; the bash runner
  (`scripts/codegen-opcodes-check.sh`) iterates the list, emitting
  one ELF per case via `lake exe codegen --test-case <name>` and
  diffing the first 32 bytes of `ziskemu`'s public output against
  `expectedOutHex`.

  Adding a regression test = appending one record to
  `opcodeTestCases` below.
-/

import EvmAsm.Codegen.Programs

namespace EvmAsm.Codegen.Tests

open EvmAsm.Codegen

private def byteCsv (bytes : List String) : String :=
  String.intercalate ", " bytes

private def repeatedPush1Bytecode (n : Nat) (value : String) : String :=
  byteCsv ((List.range n).flatMap (fun _ => ["0x60", value]) ++ ["0x00"])

private def push20RepeatedBytecode (value : String) (suffix : List String) : String :=
  byteCsv (["0x73"] ++ List.replicate 20 value ++ suffix)

private def callToRepeatedTargetBytecode (value : String) (suffix : List String) : String :=
  byteCsv ((List.range 5).flatMap (fun _ => ["0x60", "0x00"]) ++
    ["0x73"] ++ List.replicate 20 value ++ ["0x60", "0xff", "0xf1"] ++ suffix)

private def staticcallToRepeatedTargetBytecode (value : String) (suffix : List String) : String :=
  byteCsv ((List.range 4).flatMap (fun _ => ["0x60", "0x00"]) ++
    ["0x73"] ++ List.replicate 20 value ++ ["0x60", "0xff", "0xfa"] ++ suffix)

private def extcodecopyRepeatedTargetBytecode (value size : String) (suffix : List String) : String :=
  byteCsv
    (["0x60", size, "0x60", "0x00", "0x60", "0x00"] ++
      ["0x73"] ++ List.replicate 20 value ++ ["0x3c"] ++ suffix)

private def callPrecompileBytecode
    (target inSize : String) (suffix : List String) : String :=
  byteCsv
    (["0x60", "0x00", "0x60", "0x00", "0x60", inSize, "0x60", "0x00",
      "0x60", "0x00", "0x60", target, "0x60", "0xff", "0xf1"] ++ suffix)

private def callPrecompileBytecodeWithPrefix
    (prelude : List String) (target inSize : String) (suffix : List String) : String :=
  byteCsv
    (prelude ++ ["0x60", "0x00", "0x60", "0x00", "0x60", inSize, "0x60", "0x00",
      "0x60", "0x00", "0x60", target, "0x60", "0xff", "0xf1"] ++ suffix)

private def callPrecompileBytecodeWithTargetBytes
    (targetBytes : List String) (inSize : String) (suffix : List String) : String :=
  byteCsv
    (["0x60", "0x00", "0x60", "0x00", "0x60", inSize, "0x60", "0x00",
      "0x60", "0x00"] ++ targetBytes ++ ["0x60", "0xff", "0xf1"] ++ suffix)

private def staticcallPrecompileBytecode
    (target inSize : String) (suffix : List String) : String :=
  byteCsv
    (["0x60", "0x00", "0x60", "0x00", "0x60", inSize, "0x60", "0x00",
      "0x60", target, "0x60", "0xff", "0xfa"] ++ suffix)

/-- One per-opcode regression test wrapped around the M5b dispatcher
    (`tinyInterpRegistry`). The bytecode bakes into `.data`; the
    expected output is the first 32 bytes of `OUTPUT_ADDR` (i.e. the
    EVM stack top after STOP, written by `evmAddEpilogue`). -/
structure OpcodeTestCase where
  /-- Identifier (becomes `gen-out/<name>.{s,o,elf,output}`). -/
  name           : String
  /-- EVM bytecode as a comma-separated `.byte` directive payload
      (e.g. `"0x60, 0xff, 0x60, 0x01, 0x01, 0x00"`). -/
  bytecode       : String
  /-- Expected first 32 bytes of `OUTPUT_ADDR` as 64 hex chars. -/
  expectedOutHex : String
  /-- Optional EVM calldata passed alongside the bytecode (M21).
      Accepted shapes: CSV (e.g. `"0x01, 0x02, 0x03"`) or hex blob
      (e.g. `"0xdeadbeef"`). Empty string = no calldata (M17
      no-op CALLDATA behavior for back-compat with pre-M21 cases). -/
  calldata       : String := ""
  /-- Optional pre-loaded EVM storage slots (M22). Format:
      parenthesized hex pairs `"(0x00, 0xdead) (0x01, 0xbeef)"`.
      Each key / value is interpreted as a u256 integer; the
      packer serializes them in EVM-stack byte order. Empty
      string = no preload (table starts empty; SSTORE may grow
      it; SLOAD against an unset key returns zero). -/
  storage        : String := ""
  /-- Optional BLOBBASEFEE value (M28). Format is a u256 hex integer;
      the runtime input packer serializes it in EVM-stack byte order.
      Empty string = zero blob base fee. -/
  blobBaseFee    : String := ""
  /-- Optional BLOBHASH versioned-hash list (M28). Format is comma or
      space-separated 32-byte hex blobs. Empty string = no blob hashes. -/
  blobHashes     : String := ""
  /-- Optional current block number for BLOCKHASH runtime context
      (M29). Decimal or 0x-prefixed u64 string. Empty string means
      use the packer's default current block 0. -/
  blockNumber    : String := ""
  /-- Optional recent ancestor hashes for BLOCKHASH runtime context
      (M29), in increasing block-number order, as comma/space-
      separated 32-byte hex hashes. Empty string = no recent hashes. -/
  blockHashes    : String := ""
  /-- Optional simple environment values. Format is comma- or
      whitespace-separated `field=hex` pairs accepted by
      `scripts/pack-bytecode.py --env`, e.g.
      `"caller=0x1234,timestamp=0x2a"`. Empty string = every simple
      env opcode reads zero, preserving the pre-env-trailer behavior. -/
  env            : String := ""
  /-- Optional expected halt-kind at `OUTPUT_ADDR + 32` (M23).
      16 hex chars = 8-byte LE u64 (e.g. `"0100000000000000"` for
      RETURN = 1, `"0200000000000000"` for REVERT = 2). Empty
      string = don't assert (back-compat for pre-M23 cases). The
      bash runner reads `OUTPUT_ADDR + 32..40` and compares only
      when this field is non-empty. -/
  expectedHaltKind : String := ""
  /-- Optional expected persistent log length at
      `OUTPUT_ADDR + 40` (M24). 16 hex chars = 8-byte LE u64.
      The dispatcher epilogue surfaces the FINAL persistent log
      length (post-revert if REVERT ran) here for every exit
      path. Test SSTORE commit / REVERT rollback via this. Empty
      string = don't assert. -/
  expectedPersistentLogLength : String := ""
  /-- Optional expected transient log length at
      `OUTPUT_ADDR + 48` (M24). 16 hex chars = 8-byte LE u64.
      Reset to 0 by REVERT. Test TSTORE commits / REVERT
      clears via this. Empty string = don't assert. -/
  expectedTransientLogLength : String := ""
  /-- Optional expected post-state slot data at
      `OUTPUT_ADDR + 56` (M25). Hex string of arbitrary
      length; runner reads `len/2` bytes from `OUTPUT[56]`
      and compares. Layout:
        - bytes 56..64: u64 LE `numModifiedPersistentSlots` (≤ 3)
        - bytes 64..(64 + N*64): N × (slotKey:32, current:32)
      Slots appear in **reverse write order** (most-recently-
      modified first). Bytes are in EVM-stack byte order
      (4 LE u64 limbs, low limb first) — same convention as
      M22's `--storage` packer and the existing storage-test
      `expectedOutHex` values. Empty string = don't assert. -/
  expectedPostStorage : String := ""
  /-- Optional expected receipt event-log count at
      `OUTPUT_ADDR + 56` (M26). 16 hex chars = 8-byte LE u64.
      This shares the storage post-state diagnostic window; tests
      should assert one surface or the other. Empty string = don't
      assert. -/
  expectedEventLogCount : String := ""
  /-- Optional expected prefix of the first event-log descriptor at
      `OUTPUT_ADDR + 64` (M26). Hex string of arbitrary length;
      runner reads `len/2` bytes and compares. Layout begins:
        - +0: u64 topic count
        - +8: u64 memory offset
        - +16: u64 memory size
        - +24: u64 copied data length
        - +32..160: four topic slots in stack-word byte order
        - +160..192: first up to 32 copied memory bytes
        - +192..224: ADDRESS context word
        - +224..256: CALLER context word
      Empty string = don't assert. -/
  expectedEventLogFirst : String := ""
  /-- Optional gas limit (M30), decimal or 0x-hex, passed to
      `pack-bytecode.py --gas`. Empty = use the packer default
      (30,000,000). Set a small value to exercise the out-of-gas path
      (the dispatch loop charges each opcode's static base cost; an
      underflow halts with `expectedHaltKind = 6`). -/
  gasLimit : String := ""
  /-- Optional expected RETURN/REVERT copied-byte count at
      `OUTPUT_ADDR + 248` (M31). 16 hex chars = 8-byte LE u64.
      This is capped to the dispatcher's extended return-data window. -/
  expectedReturnDataCopied : String := ""
  /-- Optional expected RETURN/REVERT requested byte count at
      `OUTPUT_ADDR + 64` (M31). 16 hex chars = 8-byte LE u64. -/
  expectedReturnDataLength : String := ""
  /-- Optional expected RETURN/REVERT byte prefix at
      `OUTPUT_ADDR + 72` (M31). Hex string of arbitrary length;
      runner reads exactly `len/2` bytes and compares. -/
  expectedReturnDataHex : String := ""
  /-- Optional expected SELFDESTRUCT staged beneficiary at
      `OUTPUT_ADDR + 56`. Hex string, normally 20 canonical big-endian address
      bytes. This shares the test-only storage/log diagnostic window, so cases
      should assert only one of those surfaces. -/
  expectedSelfdestructBeneficiary : String := ""

/-- Registry of test cases. M5a/M5b's two original bytecodes are
    migrated as `add_basic` / `add_chain`; M6b adds ~20 more — one
    per singleton opcode, one per parametric family, plus a kitchen-
    sink case that chains multiple opcodes.

    EVM convention reminder: stack values are 256-bit big-endian;
    `OUTPUT_ADDR` receives the post-STOP stack top as 32 bytes,
    interpreted as four little-endian u64 limbs. So `0x42` on the
    EVM stack surfaces as `42 00 00 00 00 00 00 00 ...` (low byte
    first in the LE limb encoding).

    Binary opcodes pop top (`a`) then second (`b`); the order
    matters for non-commutative ones (`SUB`, `DIV`, `MOD`, `SHR`,
    comparisons). For SUB specifically: pushes `a - b` where `a`
    was the top — so `PUSH1 0x03; PUSH1 0x05; SUB` yields `5 - 3 = 2`. -/
def opcodeTestCases : List OpcodeTestCase :=
  [ -- ## Baseline (migrated from M5a/M5b)
    -- PUSH1 0xff; PUSH1 0x01; ADD; STOP → 0x100
    { name           := "add_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x01, 0x01, 0x00"
      expectedOutHex := "0001000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x10; PUSH1 0x20; ADD; PUSH1 0x30; ADD; STOP → 0x60
    { name           := "add_chain"
      bytecode       := "0x60, 0x10, 0x60, 0x20, 0x01, 0x60, 0x30, 0x01, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
    -- ## Singletons (16, one per fixed-shape opcode)
  , -- PUSH1 0x03; PUSH1 0x05; SUB; STOP → 5 - 3 = 2
    { name           := "sub_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x03, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x04; MUL; STOP → 4 * 3 = 12 = 0x0c
    { name           := "mul_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x04, 0x02, 0x00"
      expectedOutHex := "0c00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x7f; PUSH1 0x00; SIGNEXTEND; STOP — byte 0 of 0x7f has
    -- high bit 0, so sign-extension is a no-op → 0x7f.
    { name           := "signextend_basic"
      bytecode       := "0x60, 0x7f, 0x60, 0x00, 0x0b, 0x00"
      expectedOutHex := "7f00000000000000000000000000000000000000000000000000000000000000" }
  , -- SIGNEXTEND(0, 0x80) extends the byte-0 sign bit through the word.
    { name           := "signextend_byte0_negative"
      bytecode       := "0x60, 0x80, 0x60, 0x00, 0x0b, 0x00"
      expectedOutHex := "80ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- SIGNEXTEND(1, 0x7fff) keeps a positive byte-1 value unchanged.
    { name           := "signextend_byte1_positive"
      bytecode       := "0x61, 0x7f, 0xff, 0x60, 0x01, 0x0b, 0x00"
      expectedOutHex := "ff7f000000000000000000000000000000000000000000000000000000000000" }
  , -- SIGNEXTEND(1, 0x8000) extends bit 15.
    { name           := "signextend_byte1_negative"
      bytecode       := "0x61, 0x80, 0x00, 0x60, 0x01, 0x0b, 0x00"
      expectedOutHex := "0080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- SIGNEXTEND(0, 0) stays zero.
    { name           := "signextend_zero"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x0b, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- SIGNEXTEND(31, max_word) targets the top byte, so the word is unchanged.
    { name           := "signextend_byte31_max_word"
      bytecode       := "0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x1f, 0x0b, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- SIGNEXTEND(32, 0x80) is out of range and must leave x unchanged.
    { name           := "signextend_byte32_noop"
      bytecode       := "0x60, 0x80, 0x60, 0x20, 0x0b, 0x00"
      expectedOutHex := "8000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x03; LT; STOP → 3 < 5 = 1
    { name           := "lt_basic"
      bytecode       := "0x60, 0x05, 0x60, 0x03, 0x10, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x05; GT; STOP → 5 > 3 = 1
    { name           := "gt_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x11, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH1 0x01; SLT; STOP — signed `a < b` with a=1, b=2 → 1
    { name           := "slt_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x01, 0x12, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x05; SGT; STOP — signed `a > b` with a=5, b=3 → 1
    { name           := "sgt_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x13, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; PUSH1 0x42; EQ; STOP → 1
    { name           := "eq_basic"
      bytecode       := "0x60, 0x42, 0x60, 0x42, 0x14, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; ISZERO; STOP → 1
    { name           := "iszero_basic"
      bytecode       := "0x60, 0x00, 0x15, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xff; AND; STOP → 0xff & 0x0f = 0x0f
    { name           := "and_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xff, 0x16, 0x00"
      expectedOutHex := "0f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xa0; OR; STOP → 0xa0 | 0x0f = 0xaf
    { name           := "or_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xa0, 0x17, 0x00"
      expectedOutHex := "af00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0f; PUSH1 0xff; XOR; STOP → 0xff ^ 0x0f = 0xf0
    { name           := "xor_basic"
      bytecode       := "0x60, 0x0f, 0x60, 0xff, 0x18, 0x00"
      expectedOutHex := "f000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; NOT; STOP → ~0 (32 bytes of 0xff)
    { name           := "not_basic"
      bytecode       := "0x60, 0x00, 0x19, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH32 0x0102…20; PUSH1 0x1f; BYTE; STOP — byte 31 (LSByte
    -- big-endian) of 0x0102…1f20 is 0x20.
    { name           := "byte_basic"
      bytecode       := "0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x60, 0x1f, 0x1a, 0x00"
      expectedOutHex := "2000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01; PUSH1 0x04; SHL; STOP — shift=4 on top, value=0x01
    -- → 0x01 << 4 = 0x10.
    { name           := "shl_basic"
      bytecode       := "0x60, 0x01, 0x60, 0x04, 0x1b, 0x00"
      expectedOutHex := "1000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x80; PUSH1 0x04; SHR; STOP — shift=4 on top, value=0x80
    -- → 0x80 >> 4 = 0x08.
    { name           := "shr_basic"
      bytecode       := "0x60, 0x80, 0x60, 0x04, 0x1c, 0x00"
      expectedOutHex := "0800000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; PUSH1 0x01; SAR; STOP — shift=1 on top, value=0xff
    -- (MSB clear → positive in 256-bit two's complement). 0xff >>>arith 1
    -- = 0x7f; SAR matches SHR on the positive path.
    { name           := "sar_basic_positive"
      bytecode       := "0x60, 0xff, 0x60, 0x01, 0x1d, 0x00"
      expectedOutHex := "7f00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH32 (2^256 - 1); PUSH1 0x01; SAR; STOP — value is -1 in two's
    -- complement (all 256 bits set). SAR sign-fills, so -1 >>>arith 1 = -1
    -- (all bits stay set). Exercises the sign-extension path.
    { name           := "sar_basic_negative"
      bytecode       := "0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x01, 0x1d, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH1 0x00; CLZ; STOP → all 256 bits are zero.
    { name           := "clz_zero"
      bytecode       := "0x60, 0x00, 0x1e, 0x00"
      expectedOutHex := "0001000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01; CLZ; STOP → single low bit set, so 255 leading zero bits.
    { name           := "clz_low_bit"
      bytecode       := "0x60, 0x01, 0x1e, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH32 0x0100...00; CLZ; STOP → top byte has seven leading zero bits.
    { name           := "clz_high_limb"
      bytecode       := "0x7f, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1e, 0x00"
      expectedOutHex := "0700000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; PUSH1 0xff; POP; STOP — POP removes 0xff, leaves 0x42
    { name           := "pop_basic"
      bytecode       := "0x60, 0x42, 0x60, 0xff, 0x50, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## Family representatives (3, one per parametric family)
  , -- PUSH32 0x0102…20; STOP — the 32 immediate bytes are read
    -- big-endian into the EVM word; surfaced LE in OUTPUT_ADDR.
    { name           := "push32_basic"
      bytecode       := "0x7f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x00"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201" }
  , -- PUSH0; STOP — explicit representative for the PUSH0 endpoint.
    { name           := "push0_basic"
      bytecode       := "0x5f, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01 repeated 1024 times; STOP. This reaches the
    -- protocol stack-depth limit exactly and proves the runtime dispatcher's
    -- static stack arena is large enough for a valid 1024-word stack.
    { name           := "push1_depth_1024"
      bytecode       := repeatedPush1Bytecode 1024 "0x01"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- The 1025th PUSH exceeds the EVM stack limit and halts before writing
    -- below `evm_stack_low`. Stack overflow is surfaced as halt_kind = 8.
    { name             := "push1_depth_1025_overflow"
      bytecode         := repeatedPush1Bytecode 1025 "0x01"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0800000000000000" }
  , -- PUSH1 0x42; DUP1; ADD; STOP — DUP1 makes stack [0x42, 0x42];
    -- ADD → 0x84.
    { name           := "dup1_basic"
      bytecode       := "0x60, 0x42, 0x80, 0x01, 0x00"
      expectedOutHex := "8400000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 1; ...; PUSH1 16; DUP16; STOP — DUP16 copies the deepest
    -- item in this 16-word stack, so the result is 1.
    { name           := "dup16_basic"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0x60, 0x07, 0x60, 0x08, 0x60, 0x09, 0x60, 0x0a, 0x60, 0x0b, 0x60, 0x0c, 0x60, 0x0d, 0x60, 0x0e, 0x60, 0x0f, 0x60, 0x10, 0x8f, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x02; SWAP1; SUB; STOP — SWAP1 yields top=5,
    -- second=2; SUB → 5 - 2 = 3.
    { name           := "swap1_basic"
      bytecode       := "0x60, 0x05, 0x60, 0x02, 0x90, 0x03, 0x00"
      expectedOutHex := "0300000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 1; ...; PUSH1 17; SWAP16; STOP — SWAP16 exchanges top with
    -- the deepest item in this 17-word stack, so the surfaced top is 1.
    { name           := "swap16_basic"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0x60, 0x07, 0x60, 0x08, 0x60, 0x09, 0x60, 0x0a, 0x60, 0x0b, 0x60, 0x0c, 0x60, 0x0d, 0x60, 0x0e, 0x60, 0x0f, 0x60, 0x10, 0x60, 0x11, 0x9f, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
    -- ## Kitchen sink (cross-family chain)
  , -- PUSH1 0x03; PUSH1 0x05; MUL; PUSH1 0x10; SUB; STOP
    -- MUL: 5*3=15=0x0f. SUB: 0x10 - 0x0f = 0x01.
    { name           := "arith_mix"
      bytecode       := "0x60, 0x03, 0x60, 0x05, 0x02, 0x60, 0x10, 0x03, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
    -- ## M7 memory opcodes (MLOAD / MSTORE / MSTORE8)
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x00; MLOAD; STOP
    -- MSTORE writes 0x42 big-endian to memory[0..32]; MLOAD reads it
    -- back to the stack. EVM word = 0x42, on the stack as four LE u64
    -- limbs with limb 0 = 0x42 (decimal 66).
    { name           := "mstore_mload"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; PUSH1 0x00; MSTORE8; PUSH1 0x00; MLOAD; STOP
    -- MSTORE8 writes one byte (0xff) at memory[0]. MLOAD reads 32 bytes
    -- big-endian → EVM word = 0xff · 2^248. As LE limbs that's
    -- [0, 0, 0, 0xff00000000000000]; limb 3 written to bytes 24..31
    -- in LE order ends with 0xff at byte 31.
    { name           := "mstore8_basic"
      bytecode       := "0x60, 0xff, 0x60, 0x00, 0x53, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "00000000000000000000000000000000000000000000000000000000000000ff" }
  , -- PUSH1 0x40; MLOAD; MSIZE; STOP
    -- MLOAD touches memory[0x40..0x60), so MSIZE reports the rounded
    -- active size 0x60.
    { name           := "mload_updates_msize"
      bytecode       := "0x60, 0x40, 0x51, 0x59, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
    -- ## M12 simple environment opcodes (ADDRESS, CALLER, …)
    -- The evm_env data region is zero-initialised by the dispatcher's
    -- .data section. Each test confirms the handler routes through
    -- evm_env_load + x12 advances + 32 bytes land on the stack.
  , -- ADDRESS; STOP — routes byte 0x30 to evm_env_load .x20 .x15 .address.
    -- Reads 32 zero bytes from evm_env + 0 and pushes them.
    { name           := "address_zero"
      bytecode       := "0x30, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- CALLER; DUP1; ADD; STOP — exercises a non-trivial post-ENV stack
    -- flow. CALLER pushes 0 (zero-init env). DUP1 yields [0, 0].
    -- ADD → 0. Confirms env handler advances x12 correctly so DUP1/ADD
    -- find their operand.
    { name           := "caller_via_dup_add"
      bytecode       := "0x33, 0x80, 0x01, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- TIMESTAMP; NUMBER; SUB; STOP — exercises two distinct env field
    -- offsets back-to-back. Both fields zero-init → SUB yields 0.
    -- Confirms different opcode bytes resolve to different env cells
    -- (handler-table dispatch, not aliasing).
    { name           := "env_field_offset_distinct"
      bytecode       := "0x42, 0x43, 0x03, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
    -- ## M29 BLOCKHASH runtime context
    -- Current block number = 500. Recent hashes are supplied in
    -- increasing block-number order for blocks 497, 498, 499.
  , -- BLOCKHASH(499) returns the parent hash.
    { name           := "blockhash_parent"
      bytecode       := "0x61, 0x01, 0xf3, 0x40, 0x00"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201"
      blockNumber    := "500"
      blockHashes    := "0x1111111111111111111111111111111111111111111111111111111111111111,0x2222222222222222222222222222222222222222222222222222222222222222,0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" }
  , -- BLOCKHASH(498) selects the older in-window ancestor.
    { name           := "blockhash_historical"
      bytecode       := "0x61, 0x01, 0xf2, 0x40, 0x00"
      expectedOutHex := "2222222222222222222222222222222222222222222222222222222222222222"
      blockNumber    := "500"
      blockHashes    := "0x1111111111111111111111111111111111111111111111111111111111111111,0x2222222222222222222222222222222222222222222222222222222222222222,0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" }
  , -- BLOCKHASH(current) returns 0 even with recent hashes loaded.
    { name           := "blockhash_current_zero"
      bytecode       := "0x61, 0x01, 0xf4, 0x40, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      blockNumber    := "500"
      blockHashes    := "0x1111111111111111111111111111111111111111111111111111111111111111,0x2222222222222222222222222222222222222222222222222222222222222222,0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" }
  , -- BLOCKHASH(future) returns 0.
    { name           := "blockhash_future_zero"
      bytecode       := "0x61, 0x01, 0xf5, 0x40, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      blockNumber    := "500"
      blockHashes    := "0x1111111111111111111111111111111111111111111111111111111111111111,0x2222222222222222222222222222222222222222222222222222222222222222,0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" }
  , -- BLOCKHASH(496) is older than the supplied recent-hash table, so
    -- the runtime path returns 0 instead of reading outside the table.
    { name           := "blockhash_missing_zero"
      bytecode       := "0x61, 0x01, 0xf0, 0x40, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      blockNumber    := "500"
      blockHashes    := "0x1111111111111111111111111111111111111111111111111111111111111111,0x2222222222222222222222222222222222222222222222222222222222222222,0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" }
  , -- CALLER; STOP with nonzero runtime env. The packer appends the
    -- simple-env trailer and the runtime dispatcher copies it into
    -- evm_env before executing bytecode.
    { name           := "caller_from_input_env"
      bytecode       := "0x33, 0x00"
      expectedOutHex := "3412000000000000000000000000000000000000000000000000000000000000"
      env            := "caller=0x1234" }
  , -- TIMESTAMP; STOP with nonzero runtime env.
    { name           := "timestamp_from_input_env"
      bytecode       := "0x42, 0x00"
      expectedOutHex := "2a00000000000000000000000000000000000000000000000000000000000000"
      env            := "timestamp=0x2a" }
  , -- BASEFEE; STOP with nonzero runtime env. This is distinct from
    -- BLOBBASEFEE's separate M28 trailer slot at env+512.
    { name           := "basefee_from_input_env"
      bytecode       := "0x48, 0x00"
      expectedOutHex := "efbe000000000000000000000000000000000000000000000000000000000000"
      env            := "base_fee=0xbeef" }
  , -- SLOTNUM; STOP with nonzero runtime env. EIP-7843 exposes the
    -- consensus-layer slot number through opcode 0x4b.
    { name           := "slotnum_from_input_env"
      bytecode       := "0x4b, 0x00"
      expectedOutHex := "2a00000000000000000000000000000000000000000000000000000000000000"
      env            := "slot_number=0x2a" }
    -- ## M13 calldata-context opcode (CALLDATASIZE)
    -- The calldata-length cell at evm_env + 424 is zero-initialised by the
    -- dispatcher's .data section, so CALLDATASIZE pushes 32 zero bytes.
    -- This confirms (a) byte 0x36 routes to evm_calldatasize, (b) the
    -- env-region size bump to 512 bytes makes offset 424 reachable.
  , -- CALLDATASIZE; STOP
    { name           := "calldatasize_zero"
      bytecode       := "0x36, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
    -- ## M14 control-flow opcode (JUMPDEST)
    -- JUMPDEST is an EVM no-op marker. The dispatcher emits empty body
    -- + .advanceAndRet 1, so x10 is bumped by 1 and the loop continues.
    -- This case confirms JUMPDEST doesn't corrupt the stack and the
    -- next opcode (PUSH1) executes correctly.
  , -- JUMPDEST; PUSH1 0x42; STOP — JUMPDEST is a no-op; PUSH1 0x42 lands
    -- the value on the stack; STOP halts. Expected: 0x42 in low limb.
    { name           := "jumpdest_basic"
      bytecode       := "0x5b, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
    -- ## M15 control-flow opcodes (PC, JUMP, JUMPI)
    -- These use the dispatcher's preserved code-base register x21
    -- (initialised in the prologue) to compute PC values and jump
    -- targets. JUMP/JUMPI validate against execution-specs-style valid
    -- destinations: the target must be a JUMPDEST byte outside PUSH data.
  , -- PC; STOP — PC at offset 0 = 0. Expected: 0 in low limb.
    { name           := "pc_at_zero"
      bytecode       := "0x58, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; POP; PC; STOP — PC opcode at offset 3 after the
    -- 2-byte PUSH1 and 1-byte POP. Expected: 3 in low limb.
    { name           := "pc_after_push"
      bytecode       := "0x60, 0x42, 0x50, 0x58, 0x00"
      expectedOutHex := "0300000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x04; JUMP; INVALID; JUMPDEST; PUSH1 0xff; STOP
    -- Layout: 0=PUSH1, 1=0x04, 2=JUMP, 3=INVALID (0xfe), 4=JUMPDEST,
    -- 5=PUSH1, 6=0xff, 7=STOP. JUMP target = 4 (the JUMPDEST byte).
    -- Skips the INVALID at byte 3, lands on JUMPDEST, executes PUSH1
    -- 0xff. Expected: 0xff in low limb.
    { name           := "jump_forward"
      bytecode       := "0x60, 0x04, 0x56, 0xfe, 0x5b, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01; PUSH1 0x06; JUMPI; INVALID; JUMPDEST; PUSH1 0xff; STOP
    -- Bytecode layout: 0=PUSH1 1=0x01(cond) 2=PUSH1 3=0x06(dest) 4=JUMPI
    -- 5=INVALID(0xfe) 6=JUMPDEST 7=PUSH1 8=0xff 9=STOP.
    -- Stack after both PUSHes: [0x01, 0x06] with 0x06 on top. JUMPI pops
    -- dest=0x06 (top) then cond=0x01 (below). cond != 0 → jump to byte 6,
    -- the JUMPDEST. Then PUSH1 0xff. Expected: 0xff in low limb.
    { name           := "jumpi_taken"
      bytecode       := "0x60, 0x01, 0x60, 0x06, 0x57, 0xfe, 0x5b, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; PUSH1 0xff; JUMPI; PUSH1 0x42; STOP
    -- dest=0xff (top), cond=0x00 (below). cond == 0 → fall through.
    -- Next opcode is PUSH1 0x42. Expected: 0x42 in low limb.
    -- Confirms JUMPI advances x10 by 1 on the cond=0 branch instead
    -- of jumping to the (out-of-bounds) dest.
    { name           := "jumpi_not_taken"
      bytecode       := "0x60, 0x00, 0x60, 0xff, 0x57, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      -- M15.5: confirm the not-taken JUMPI sentinel path does NOT
      -- spuriously trip the validity check — it halts normally (STOP,
      -- halt_kind 0) with 0x42, not the invalid-jump halt_kind 4.
      expectedHaltKind := "0000000000000000" }
    -- ## M15.5 JUMPDEST-validity (Level 1): invalid jumps exceptionally
    -- halt with halt_kind = 4 and empty (zero) return data.
  , -- PUSH1 0x00; JUMP — dest = 0 → code[0] = 0x60 (PUSH1), not 0x5b.
    -- Invalid jump → .exit_invalid → halt_kind 4, result = 0.
    { name             := "jump_invalid_dest"
      bytecode         := "0x60, 0x00, 0x56"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0400000000000000" }
  , -- PUSH1 0x01 (cond); PUSH1 0x00 (dest); JUMPI — cond != 0 so the
    -- jump is taken to dest = 0; code[0] = 0x60, not 0x5b → invalid.
    -- Exercises the JUMPI taken-path validity load (halt_kind 4).
    { name             := "jumpi_taken_invalid"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x57"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0400000000000000" }
  , -- PUSH1 0x04; JUMP; PUSH1 0x5b; STOP. Byte 4 is 0x5b,
    -- but it is the PUSH1 immediate, so it is not a valid JUMPDEST.
    { name             := "jump_pushdata_jumpdest_invalid"
      bytecode         := "0x60, 0x04, 0x56, 0x60, 0x5b, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0400000000000000" }
  , -- Taken JUMPI to byte 6, a PUSH1 immediate 0x5b, is invalid.
    { name             := "jumpi_taken_pushdata_jumpdest_invalid"
      bytecode         := "0x60, 0x01, 0x60, 0x06, 0x57, 0x60, 0x5b, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0400000000000000" }
  , -- Not-taken JUMPI does not validate the destination, even when that
    -- destination points at a PUSH immediate 0x5b; it falls through normally.
    { name             := "jumpi_not_taken_pushdata_dest_ignored"
      bytecode         := "0x60, 0x00, 0x60, 0x06, 0x57, 0x60, 0x5b, 0x00"
      expectedOutHex   := "5b00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
    -- ## M16 hash opcode (KECCAK256 via ECALL bridge to Zisk accelerator)
    -- KECCAK256 pops offset (top of stack) and size (next word), hashes the
    -- memory[offset..offset+size] region, pushes the 32-byte digest.
    -- The handler is all-raw-asm in `.custom` tail (no verified Program).
    -- The dispatcher epilogue ships the `zkvm_keccak256` subroutine + a
    -- 200-byte `zk3_state:` data block.
  , -- PUSH1 0x00; PUSH1 0x00; KECCAK256; STOP — hashes empty bytes.
    -- Expected: standard keccak256("") =
    -- c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
    { name           := "keccak256_empty"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x20, 0x00"
      expectedOutHex := "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" }
  , -- MSTORE8 pre-expands memory to one word, then KECCAK256 hashes one
    -- byte. Total gas at the exact threshold:
    -- PUSH1*4 (12) + MSTORE8 static (3) + memory expansion (3)
    -- + KECCAK static (30) + KECCAK word gas (6) = 54.
    { name           := "keccak256_word_gas_sufficient"
      bytecode       := "0x60, 0xab, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0x20, 0x00"
      expectedOutHex := "468fc9c005382579139846222b7b0aebc9182ba073b2455938a86d9753bfb078"
      gasLimit       := "54" }
  , -- One gas short of the same one-byte KECCAK path. The fixed opcode
    -- charge succeeds, then the new 6-gas word charge routes to OOG.
    { name             := "keccak256_word_gas_oog"
      bytecode         := "0x60, 0xab, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0x20, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "53" }
  , -- Hash 33 zero bytes from initially empty memory. KECCAK charges two
    -- input words (12) plus two-word memory expansion (6), in addition
    -- to two PUSHes (6) and the fixed KECCAK base (30): total 54.
    { name           := "keccak256_33_bytes_memory_gas_sufficient"
      bytecode       := "0x60, 0x21, 0x60, 0x00, 0x20, 0x00"
      expectedOutHex := "f39a869f62e75cf5f0bf914688a6b289caf2049435d8e68c5c5e6d05e44913f3"
      gasLimit       := "54" }
  , -- Zero-size KECCAK does not expand memory, so a high offset limb is
    -- accepted and still hashes the empty byte string.
    { name           := "keccak256_zero_size_high_offset_ok"
      bytecode       := "0x60, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00"
      expectedOutHex := "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
      gasLimit       := "36" }
  , -- A non-zero high size limb represents an unbounded hash range for
    -- this u64-addressed runtime and is reported as OOG before hashing.
    { name             := "keccak256_high_size_oog"
      bytecode         := "0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0x20, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "36" }
    -- ## M26 LOG opcodes (LOG0-LOG4) — bounded event capture.
    -- LOGn pops (2+n) 256-bit words, advances PC, and appends a
    -- 256-byte descriptor to the dispatcher's receipt-event buffer.
  , -- PUSH1 0x11; PUSH1 0x22; LOG0; PUSH1 0x33; STOP — LOG0 pops the
    -- two pushed words; PUSH1 0x33 lands on the now-empty stack.
    -- Also checks descriptor header: topics=0, offset=0x22,
    -- size=0x11, copied data length=0x11.
    { name                   := "log0_pop"
      bytecode               := "0x60, 0x11, 0x60, 0x22, 0xa0, 0x60, 0x33, 0x00"
      expectedOutHex         := "3300000000000000000000000000000000000000000000000000000000000000"
      expectedEventLogCount  := "0100000000000000"
      expectedEventLogFirst  := "0000000000000000220000000000000011000000000000001100000000000000" }
  , -- PUSH1 0x01..0x06; LOG4; PUSH1 0xff; STOP — LOG4 pops the six
    -- pushed words (offset + size + 4 topics); PUSH1 0xff lands on
    -- the now-empty stack. Confirms byte 0xa4 routes correctly and
    -- stack delta is +192. The descriptor records offset=6,
    -- size=5, and topics 4,3,2,1 in stack-pop order.
    { name                   := "log4_pop"
      bytecode               := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0xa4, 0x60, 0xff, 0x00"
      expectedOutHex         := "ff00000000000000000000000000000000000000000000000000000000000000"
      expectedEventLogCount  := "0100000000000000"
      expectedEventLogFirst  := "04000000000000000600000000000000050000000000000005000000000000000400000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000" }
  , -- MSTORE8 writes 0xab at memory[0]; LOG2 then captures offset=0,
    -- size=1, topics 0x11 and 0x22, and data prefix byte 0xab.
    { name                   := "log2_captures_topic_and_data"
      bytecode               := "0x60, 0xab, 0x60, 0x00, 0x53, 0x60, 0x22, 0x60, 0x11, 0x60, 0x01, 0x60, 0x00, 0xa2, 0x60, 0x00, 0x00"
      expectedOutHex         := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedEventLogCount  := "0100000000000000"
      expectedEventLogFirst  := "02000000000000000000000000000000010000000000000001000000000000001100000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ab00000000000000000000000000000000000000000000000000000000000000" }
  , -- MSTORE8 pre-expands memory, then LOG0 captures one byte.
    -- Total gas: PUSH1*4 (12) + MSTORE8 static+mem (6) + LOG0
    -- static (375) + one data byte (8) + final PUSH1 (3) = 404.
    { name                  := "log0_data_gas_sufficient"
      bytecode              := "0x60, 0xab, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xa0, 0x60, 0x42, 0x00"
      expectedOutHex        := "4200000000000000000000000000000000000000000000000000000000000000"
      expectedEventLogCount := "0100000000000000"
      gasLimit              := "404" }
  , -- One gas short of the same LOG0 data-byte charge. The LOG exits
    -- OOG before appending an event descriptor.
    { name                  := "log0_data_gas_oog"
      bytecode              := "0x60, 0xab, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xa0, 0x60, 0x42, 0x00"
      expectedOutHex        := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind      := "0600000000000000"
      expectedEventLogCount := "0000000000000000"
      gasLimit              := "400" }
  , -- LOG1 with empty data still charges one topic: PUSH1*3 (9),
    -- LOG static (375), LOG topic (375), final PUSH1 (3) = 762.
    { name                  := "log1_topic_gas_sufficient"
      bytecode              := "0x60, 0x11, 0x60, 0x00, 0x60, 0x00, 0xa1, 0x60, 0x42, 0x00"
      expectedOutHex        := "4200000000000000000000000000000000000000000000000000000000000000"
      expectedEventLogCount := "0100000000000000"
      gasLimit              := "762" }
  , -- A non-zero high size limb represents an unbounded data range for
    -- this u64-addressed runtime and is reported as OOG before capture.
    { name                  := "log0_high_size_oog"
      bytecode              := "0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0xa0, 0x00"
      expectedOutHex        := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind      := "0600000000000000"
      expectedEventLogCount := "0000000000000000"
      gasLimit              := "381" }
  , -- Seventeen empty LOG0s exceed the static 16-entry cap. The 17th
    -- handler exits with halt_kind=4 and leaves the visible event
    -- count at 16; it must not silently drop the event and continue.
    { name                   := "log0_overflow_status"
      bytecode               := "0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x60, 0x00, 0x60, 0x00, 0xa0, 0x00"
      expectedOutHex         := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind       := "0400000000000000"
      expectedEventLogCount  := "1000000000000000" }
    -- ## M17 / M22 / M24 transient storage (TLOAD/TSTORE)
    -- M24 graduated TLOAD/TSTORE from M17 no-ops to real Option A
    -- transient storage: a separate append-log at 0xa0830000.
    -- Coverage is in the M24 test block at the end of
    -- `opcodeTestCases` (test `tstore_tload_round_trip`, which
    -- additionally asserts the transient log_length surface).
    -- ## M18 trivial no-op handlers (94.6% coverage milestone)
    -- 19 opcodes across 4 builders: haltHandlers (4), pushZeroHandlers
    -- (4), popPushZeroHandlers (6), copyNoopHandlers (5). One
    -- representative test per builder + an INVALID smoke.
  , -- PUSH1 0xff; PUSH1 0x11; PUSH1 0x22; RETURN
    -- RETURN(offset=0x22, size=0x11) reads 0x11 bytes from
    -- memory[0x22..0x33]. Memory hasn't been written, so all bytes
    -- are zero; OUTPUT[0..0x11] = 0, OUTPUT[0x11..32] zero-filled.
    -- Confirms RETURN's data path with no prior MSTORE + the size <
    -- 32 zero-fill. halt_kind = 1.
    --
    -- (Pre-M23 this test asserted the M18 no-op behavior: the
    -- remaining stack top 0xff surfaced via evmAddEpilogue. Updated
    -- in M23 to reflect the new real-RETURN semantics.)
    { name             := "return_pop2_halt"
      bytecode         := "0x60, 0xff, 0x60, 0x11, 0x60, 0x22, 0xf3"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- PUSH1 0xff; PUSH1 0x42; INVALID. M23.5: INVALID is an exceptional
    -- halt — it surfaces zero result data (no return data) and tags
    -- halt_kind = 3, instead of the pre-M23.5 behavior of leaking the
    -- stack top (0x42) via evmAddEpilogue with halt_kind = 0.
    { name             := "invalid_halt"
      bytecode         := "0x60, 0xff, 0x60, 0x42, 0xfe"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0300000000000000" }
  , -- PUSH1 0xff; SELFDESTRUCT. M23.5: SELFDESTRUCT is a normal halt
    -- with no return data — zero result + halt_kind = 5 (distinct from
    -- STOP=0 and INVALID=3). Pops 1 word (recipient address).
    { name             := "selfdestruct_halt"
      bytecode         := "0x60, 0xff, 0xff"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0500000000000000" }
  , -- SELFDESTRUCT still routes through the shared one-word stack-underflow
    -- guard before touching the beneficiary staging scratch.
    { name             := "selfdestruct_empty_stack_underflow"
      bytecode         := "0xff"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , -- SELFDESTRUCT stages the low-160 beneficiary address for later
    -- EIP-6780 gas/state children. The diagnostic exposes canonical
    -- big-endian address bytes.
    { name                            := "selfdestruct_stage_beneficiary"
      bytecode                        := "0x73, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0x00, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x11, 0x22, 0x33, 0xff"
      expectedOutHex                  := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind                := "0500000000000000"
      expectedSelfdestructBeneficiary := "11223344556677889900aabbccddeeff00112233" }
  , -- SELFDESTRUCT now charges the EIP-2929 cold account-access delta for
    -- a non-precompile beneficiary before staging the state effect.
    -- PUSH1 costs 3, SELFDESTRUCT base is 5000, and the cold delta is 2500,
    -- so 7503 exactly fits.
    { name                            := "selfdestruct_cold_beneficiary_gas"
      bytecode                        := "0x60, 0xff, 0xff"
      expectedOutHex                  := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind                := "0500000000000000"
      gasLimit                        := "7503"
      expectedSelfdestructBeneficiary := "00000000000000000000000000000000000000ff" }
  , -- With one gas less, the dynamic cold beneficiary charge OOGs before
    -- the staged SELFDESTRUCT flag is set.
    { name             := "selfdestruct_cold_beneficiary_oog"
      bytecode         := "0x60, 0xff, 0xff"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "7502" }
  , -- Active precompile beneficiaries are initially warm, so only the PUSH1
    -- and SELFDESTRUCT static costs are needed in the current handler.
    { name                            := "selfdestruct_precompile_beneficiary_warm"
      bytecode                        := "0x60, 0x01, 0xff"
      expectedOutHex                  := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind                := "0500000000000000"
      gasLimit                        := "5003"
      expectedSelfdestructBeneficiary := "0000000000000000000000000000000000000001" }
  , -- ## M30 gas metering (first slice)
    -- GAS; STOP with an explicit 1000-gas limit. The dispatch loop
    -- charges GAS's own static cost (BASE = 2) BEFORE h_GAS runs, so
    -- GAS pushes the post-charge remaining 998 = 0x3e6; STOP (cost 0)
    -- surfaces it. (Replaces the pre-M30 `gas_push_zero` no-op test.)
    { name           := "gas_opcode_sufficient"
      bytecode       := "0x5a, 0x00"
      expectedOutHex := "e603000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "1000" }
  , -- PUSH1 0x01; STOP with a 2-gas limit. PUSH1's static cost is 3 > 2,
    -- so the dispatch loop's gas charge underflows on the very first
    -- opcode → out-of-gas exceptional halt (halt_kind = 6, zero result).
    { name             := "gas_opcode_out_of_gas"
      bytecode         := "0x60, 0x01, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2" }
    -- ## M31 memory-expansion gas (cost(w) = 3·w + ⌊w²/512⌋)
  , -- PUSH1 0x42 (sentinel); PUSH1 0x00 (value); PUSH2 0x0400 (offset=1024);
    -- MSTORE; STOP. MSTORE writes [1024, 1056) → 33 words; expansion from 0
    -- = cost(33) − cost(0) = (3·33 + ⌊1089/512⌋) − 0 = 99 + 2 = 101.
    -- Total gas = PUSH1(3)+PUSH1(3)+PUSH2(3)+MSTORE static(3)+expansion(101)
    -- = 113. With gasLimit = 113 it just fits; STOP surfaces the sentinel 0x42.
    { name           := "mem_expansion_sufficient"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x61, 0x04, 0x00, 0x52, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "113" }
  , -- Same bytecode, one gas short (112): the dispatch loop charges the
    -- pushes + MSTORE static (12), leaving 100 < the 101-gas expansion →
    -- out-of-gas inside the MSTORE preBody (halt_kind = 6, zero result).
    { name             := "mem_expansion_oog"
      bytecode         := "0x60, 0x42, 0x60, 0x00, 0x61, 0x04, 0x00, 0x52, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "112" }
  , -- Two MSTOREs at the SAME offset. The first expands to 33 words (101 gas);
    -- the second finds the high-water already at/above its range and charges
    -- ZERO expansion. Total = 3+3+3 + (3+101) + 3+3 + (3+0) + STOP(0) = 122.
    -- Passing at gasLimit = 122 proves the second access is not double-charged
    -- (a double charge would need 223 and OOG here).
    { name           := "mem_expansion_no_double_charge"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x61, 0x04, 0x00, 0x52, 0x60, 0x00, 0x61, 0x04, 0x00, 0x52, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "122" }
    -- ## Stack underflow classification
    -- Stack consumers with too few words route to halt_kind = 7 before
    -- their verified bodies perform unchecked stack loads.
  , { name             := "pop_empty_stack_underflow"
      bytecode         := "0x50, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "add_one_item_underflow"
      bytecode         := "0x60, 0x01, 0x01, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "dup16_short_stack_underflow"
      bytecode         := "0x60, 0x01, 0x8f, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "swap16_short_stack_underflow"
      bytecode         := "0x60, 0x01, 0x60, 0x02, 0x9f, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "mstore_one_item_underflow"
      bytecode         := "0x60, 0x00, 0x52, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "return_one_item_underflow"
      bytecode         := "0x60, 0x00, 0xf3, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "mcopy_two_items_underflow"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "create2_three_items_underflow"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "staticcall_five_items_underflow"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "call_six_items_underflow"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , { name             := "log4_five_items_underflow"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xa4, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0700000000000000" }
  , -- BLOBBASEFEE; STOP with blob_base_fee = 0x1234. Amsterdam
    -- execution-specs computes this from block_env.excess_blob_gas;
    -- the runtime dispatcher receives the already-computed value in
    -- the input trailer and exposes it through evm_env.
    { name           := "blobbasefee_from_input"
      bytecode       := "0x4a, 0x00"
      blobBaseFee    := "0x1234"
      expectedOutHex := "3412000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; BLOBHASH; STOP with one versioned hash. The handler
    -- reads tx_env.blob_versioned_hashes[0].
    { name           := "blobhash_index_zero"
      bytecode       := "0x60, 0x00, 0x49, 0x00"
      blobHashes     := "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201" }
  , -- PUSH1 0x01; BLOBHASH; STOP with one versioned hash. Per
    -- execution-specs, out-of-range indexes push zero.
    { name           := "blobhash_out_of_range"
      bytecode       := "0x60, 0x01, 0x49, 0x00"
      blobHashes     := "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xab; BALANCE; STOP without an account-witness trailer.
    -- The witness-backed runtime handler preserves the old no-context
    -- fallback and overwrites the address with balance 0.
    { name           := "balance_pop_push_zero"
      bytecode       := "0x60, 0xab, 0x31, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xab; EXTCODESIZE; STOP without an account-witness trailer.
    -- The witness-backed runtime handler preserves the old no-context
    -- fallback and overwrites the address with code length 0.
    { name           := "extcodesize_no_context_zero"
      bytecode       := "0x60, 0xab, 0x3b, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- Account-access gas: no witness context still charges the cold
    -- BALANCE delta before zero-fallback. PUSH20(3)+BALANCE warm floor(100)
    -- + cold delta(2500)+GAS(2) leaves 395 from a 3000-gas limit.
    { name           := "balance_cold_access_gas_no_context"
      bytecode       := push20RepeatedBytecode "0xaa" ["0x31", "0x5a", "0x00"]
      expectedOutHex := "8b01000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , -- The current ADDRESS is seeded warm by runtime setup, so BALANCE
    -- charges only the 100-gas warm floor before GAS. With gasLimit=3000:
    -- PUSH20(3)+BALANCE(100)+GAS(2) leaves 2895.
    { name           := "balance_seeded_address_warm_gas_no_context"
      bytecode       := push20RepeatedBytecode "0xaa" ["0x31", "0x5a", "0x00"]
      expectedOutHex := "4f0b000000000000000000000000000000000000000000000000000000000000"
      env            := "address=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      gasLimit       := "3000" }
  , -- One gas short for the cold delta after PUSH20 and the static warm
    -- floor: 2602 - 3 - 100 = 2499 < 2500, so the helper exits OOG.
    { name             := "balance_cold_access_oog_no_context"
      bytecode         := push20RepeatedBytecode "0xaa" ["0x31", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2602" }
  , -- EXTCODESIZE uses the same account-access table and cold delta as
    -- BALANCE, even when the witness-context fallback returns zero.
    { name           := "extcodesize_cold_access_gas_no_context"
      bytecode       := push20RepeatedBytecode "0xbb" ["0x3b", "0x5a", "0x00"]
      expectedOutHex := "8b01000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , { name           := "extcodesize_seeded_address_warm_gas_no_context"
      bytecode       := push20RepeatedBytecode "0xbb" ["0x3b", "0x5a", "0x00"]
      expectedOutHex := "4f0b000000000000000000000000000000000000000000000000000000000000"
      env            := "address=0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
      gasLimit       := "3000" }
  , { name             := "extcodesize_cold_access_oog_no_context"
      bytecode         := push20RepeatedBytecode "0xbb" ["0x3b", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2602" }
  , -- EXTCODEHASH shares the EXTCODESIZE account-witness path but must
    -- still charge account access before zero-fallback.
    { name           := "extcodehash_cold_access_gas_no_context"
      bytecode       := push20RepeatedBytecode "0xcc" ["0x3f", "0x5a", "0x00"]
      expectedOutHex := "8b01000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , { name           := "extcodehash_seeded_address_warm_gas_no_context"
      bytecode       := push20RepeatedBytecode "0xcc" ["0x3f", "0x5a", "0x00"]
      expectedOutHex := "4f0b000000000000000000000000000000000000000000000000000000000000"
      env            := "address=0xcccccccccccccccccccccccccccccccccccccccc"
      gasLimit       := "3000" }
  , { name             := "extcodehash_cold_access_oog_no_context"
      bytecode         := push20RepeatedBytecode "0xcc" ["0x3f", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2602" }
  , -- PUSH1 0x01; PUSH1 0x02; PUSH1 0x03; MCOPY; PUSH1 0x42; STOP
    -- MCOPY pops 3 args; PUSH1 0x42 lands on the empty stack.
    { name           := "mcopy_pop3"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x5e, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- MSTORE8 writes 0xab at memory[0]; MCOPY(dest=1, src=0, len=1)
    -- copies that byte to memory[1]. MLOAD(0) observes bytes 0 and 1.
    { name           := "mcopy_copies_byte"
      bytecode       := "0x60, 0xab, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0x60, 0x01, 0x5e, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "000000000000000000000000000000000000000000000000000000000000abab" }
  , -- MCOPY(dest=0x40, src=0, len=1) expands memory to 0x60.
    { name           := "mcopy_msize_dest_range"
      bytecode       := "0x60, 0x01, 0x60, 0x00, 0x60, 0x40, 0x5e, 0x59, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
  , -- MCOPY(dest=0, src=0x40, len=1) expands memory to 0x60 from
    -- the read range as required by EIP-5656.
    { name           := "mcopy_msize_source_range"
      bytecode       := "0x60, 0x01, 0x60, 0x40, 0x60, 0x00, 0x5e, 0x59, 0x00"
      expectedOutHex := "6000000000000000000000000000000000000000000000000000000000000000" }
  , -- MCOPY with len=0 does not expand memory even with non-zero
    -- source and destination offsets.
    { name           := "mcopy_zero_length_keeps_msize"
      bytecode       := "0x60, 0x00, 0x60, 0x80, 0x60, 0xff, 0x5e, 0x59, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- Same shape as mcopy_msize_dest_range, then GAS. With gas=1000:
    -- three PUSH1s cost 9, MCOPY static costs 3, MCOPY dynamic costs
    -- copy=3 plus memory expansion 9, and GAS costs 2, leaving 974.
    { name           := "mcopy_gas_dest_range"
      bytecode       := "0x60, 0x01, 0x60, 0x00, 0x60, 0x40, 0x5e, 0x5a, 0x00"
      expectedOutHex := "ce03000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "1000" }
  , -- Source-only expansion has the same dynamic cost here: source grows
    -- memory to 0x60, then destination 0 is already covered.
    { name           := "mcopy_gas_source_range"
      bytecode       := "0x60, 0x01, 0x60, 0x40, 0x60, 0x00, 0x5e, 0x5a, 0x00"
      expectedOutHex := "ce03000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "1000" }
  , -- len=0 has no MCOPY dynamic gas: three PUSH1s + MCOPY static + GAS.
    { name           := "mcopy_gas_zero_length"
      bytecode       := "0x60, 0x00, 0x60, 0x80, 0x60, 0xff, 0x5e, 0x5a, 0x00"
      expectedOutHex := "da03000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "1000" }
  , -- MSTORE8 first makes active memory 0x60. MCOPY source 0 is already
    -- covered; destination 0x80 expands to 0xa0, so dynamic gas is 9.
    { name           := "mcopy_gas_dest_only_after_mstore8"
      -- M31: MSTORE8 at offset 64 now also pays its own memory-expansion gas
      -- (rounded = 96 B = 3 words → cost(3) = 9), so the GAS opcode surfaces
      -- 9 fewer than the pre-M31 expectation: 968 (0x3c8) → 959 (0x3bf).
      bytecode       := "0x60, 0xab, 0x60, 0x40, 0x53, 0x60, 0x01, 0x60, 0x00, 0x60, 0x80, 0x5e, 0x5a, 0x00"
      expectedOutHex := "bf03000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "1000" }
  , -- Gas=12 covers the three PUSH1s and MCOPY's static base charge,
    -- but not MCOPY's dynamic copy+memory charge, so the handler exits OOG.
    { name             := "mcopy_dynamic_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x40, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "12" }
  , -- len=0 skips memory expansion in execution-specs, so high source
    -- and destination limbs are accepted and MSIZE stays zero.
    { name           := "mcopy_zero_length_high_offsets_keeps_msize"
      bytecode       := "0x60, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x59, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- Non-zero high length is an unsupported memory range and exits OOG.
    { name             := "mcopy_high_length_out_of_gas"
      bytecode         := "0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0x60, 0x00, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
  , -- Non-zero length with a high source offset would require expanding
    -- beyond the runtime u64 memory surface.
    { name             := "mcopy_high_source_out_of_gas"
      bytecode         := "0x60, 0x01, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
  , -- Non-zero length with a high destination offset is likewise OOG.
    { name             := "mcopy_high_destination_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
  , -- Low-limb destination+length wraparound is rejected before copy.
    { name             := "mcopy_destination_end_wrap_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
  , -- Low-limb source+length wraparound is rejected before copy.
    { name             := "mcopy_source_end_wrap_out_of_gas"
      bytecode         := "0x60, 0x01, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x00, 0x5e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
    -- ## M19/M27 child-frame opcodes (CREATE/CALL/CALLCODE/
    -- DELEGATECALL/CREATE2/STATICCALL). CREATE-family and
    -- non-precompile CALL-family targets remain pop-N + push-zero
    -- no-ops. M27 adds a basic precompile frame surface for CALL /
    -- STATICCALL to addresses 0x01..0x04; those stubs push success =
    -- 1 so later PRs can hang per-precompile returndata bodies off
    -- the recognized branch.
    -- Three representative test cases spanning the net-pop spectrum
    -- (CREATE = 2, STATICCALL = 5, CALL = 6).
  , -- PUSH1 0x01; PUSH1 0x02; PUSH1 0x03; CREATE; PUSH1 0x42; STOP
    -- CREATE pops 3 (value, offset, size), pushes 1 (addr = 0). Net
    -- pop = 2 words = +64 bytes. Then PUSH1 0x42 lands on the
    -- now-1-deep stack; the address slot at the previous top is
    -- replaced by 0x42 via the new PUSH. Expected: 0x42.
    { name           := "create_pop3_push_zero"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0xf0, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- CREATE explicitly decodes top word as value: a high value limb is
    -- accepted by the address-derivation slice instead of being confused with
    -- high offset/size and reported as out-of-gas. With zero ADDRESS and
    -- nonce 0, CREATE derives keccak(rlp([0x00..00, 0]))[12:].
    { name             := "create_high_value_limb_derives_address"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x00"
      expectedOutHex   := "b18ea46f574a80cb7645b3e4915f34a3160477bd000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- CREATE with a nonzero runtime ADDRESS derives from that caller
    -- address. The pushed EVM word is the 160-bit address in stack byte order.
    { name             := "create_address_from_env_nonce_zero"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00"
      env              := "address=0x1234567890abcdef1234567890abcdef12345678"
      expectedOutHex   := "42f1db83cc7370b997a96db7b9ffe7c59c967087000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- CREATE size=1 charges static CREATE base plus EIP-3860 initcode
    -- word gas and memory expansion: 3 PUSH1s (9) + 32000 + 2 + 3.
    { name             := "create_initcode_len1_gas_exact"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00"
      expectedOutHex   := "b18ea46f574a80cb7645b3e4915f34a3160477bd000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "32014" }
  , -- One less gas reaches CREATE after the PUSH1s and static base, then
    -- fails while charging the new initcode/memory dynamic component.
    { name             := "create_initcode_len1_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "32013" }
  , -- At 33 bytes CREATE rounds initcode and memory expansion to two
    -- words: 3 PUSH1s (9) + 32000 + initcode word gas 4 + memory gas 6.
    { name             := "create_initcode_len33_gas_exact"
      bytecode         := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00"
      expectedOutHex   := "b18ea46f574a80cb7645b3e4915f34a3160477bd000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "32019" }
  , { name             := "create_initcode_len33_out_of_gas"
      bytecode         := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "32018" }
  , -- Amsterdam/EIP-7954 allows MAX_INIT_CODE_SIZE = 0x10000. CREATE address
    -- derivation does not hash initcode, so this probes the runtime memory
    -- envelope and gas path without needing child execution/deposit.
    { name             := "create_initcode_len65536_gas_exact"
      bytecode         := "0x63, 0x00, 0x01, 0x00, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00"
      expectedOutHex   := "b18ea46f574a80cb7645b3e4915f34a3160477bd000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "50441" }
  , -- CREATE offset is the second decoded word. For nonempty initcode,
    -- high offset limbs are outside the current runtime memory envelope.
    { name             := "create_high_offset_limb_out_of_gas"
      bytecode         := "0x60, 0x01, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0xf0, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
  , -- CREATE2 decodes salt after value/offset/size. High salt limbs are
    -- allowed and participate in EIP-1014 address derivation.
    { name             := "create2_high_salt_limb_derives_address"
      bytecode         := "0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "9e40e03a1444e5c7a2a23a0565ec2b2d2318b2a4000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- CREATE2 with nonzero ADDRESS and salt=1 over empty initcode derives
    -- the EIP-1014 address using keccak256(empty) as initcode_hash.
    { name             := "create2_address_from_env_salt_one_empty_initcode"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      env              := "address=0x1234567890abcdef1234567890abcdef12345678"
      expectedOutHex   := "178d3687bd025a14373c429091ba42d0e82d853d000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- CREATE2 size=1 charges static CREATE base, EIP-3860 initcode word
    -- gas, EIP-1014 hashcost, and memory expansion: 4 PUSH1s (12) +
    -- 32000 + 8 + 3.
    { name             := "create2_initcode_len1_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "38bf260bb3b098f0ff6ff250028ff8b42b2e1a4d000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "32023" }
  , -- One less gas fails in CREATE2's dynamic initcode charge before
    -- address derivation or later unsupported deployment slices.
    { name             := "create2_initcode_len1_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "32022" }
  , -- At 33 bytes CREATE2 rounds to two words for both EIP-3860 and
    -- EIP-1014 hashcost: 4 PUSH1s (12) + 32000 + 16 + memory gas 6.
    { name             := "create2_initcode_len33_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "05539a1fc4f022d6cdeb61c98ff5d21bf5d5d9b9000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "32034" }
  , { name             := "create2_initcode_len33_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "32033" }
  , -- CREATE2 size is the third decoded word. High size limbs are rejected
    -- before later address/precheck/deployment slices consume initcode.
    { name             := "create2_high_size_limb_out_of_gas"
      bytecode         := "0x60, 0x00, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf5, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000" }
  , -- CALL to inactive address 0x12; PUSH1 0xff; STOP
    -- CALL pops 7 (gas, to, value, in_off, in_size, out_off,
    -- out_size), pushes 1 (success = 0). Net pop = 6 = +192 bytes.
    -- Then PUSH1 0xff lands on the 1-deep stack and replaces the
    -- success slot. Expected: 0xff.
    { name           := "call_pop7_push_zero"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x12, 0x60, 0x07, 0xf1, 0x60, 0xff, 0x00"
      expectedOutHex := "ff00000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x01..0x06; STATICCALL; PUSH1 0xab; STOP
    -- STATICCALL pops 6 (gas, to, in_off, in_size, out_off,
    -- out_size), pushes 1 (success = 0). Net pop = 5 = +160 bytes.
    -- Confirms the third distinct ADDI immediate (160). Expected:
    -- 0xab.
    { name           := "staticcall_pop6_push_zero"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x60, 0x04, 0x60, 0x05, 0x60, 0x06, 0xfa, 0x60, 0xab, 0x00"
      expectedOutHex := "ab00000000000000000000000000000000000000000000000000000000000000" }
  , -- CALL-family account access: dispatcher static gas already charges
    -- the 100-gas warm floor, so a cold non-precompile target pays only the
    -- 2500 dynamic delta here. With gasLimit=3000, CALL leaves
    -- 3000 - 21(pushes) - 100 - 2500 - 2(GAS) = 377.
    { name           := "call_cold_access_gas_no_context"
      bytecode       := callToRepeatedTargetBytecode "0xaa" ["0x5a", "0x00"]
      expectedOutHex := "7901000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , -- The current ADDRESS is seeded warm before runtime execution, so the
    -- same target charges only CALL's 100-gas warm floor.
    { name           := "call_seeded_address_warm_access_gas_no_context"
      bytecode       := callToRepeatedTargetBytecode "0xaa" ["0x5a", "0x00"]
      expectedOutHex := "3d0b000000000000000000000000000000000000000000000000000000000000"
      env            := "address=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      gasLimit       := "3000" }
  , -- One gas short for the cold delta after the pushes and CALL warm floor.
    { name             := "call_cold_access_oog_no_context"
      bytecode         := callToRepeatedTargetBytecode "0xaa" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2620" }
  , -- STATICCALL has one fewer stack argument: 18 push gas, 100 warm floor,
    -- 2500 cold delta, then GAS leaves 380.
    { name           := "staticcall_cold_access_gas_no_context"
      bytecode       := staticcallToRepeatedTargetBytecode "0xbb" ["0x5a", "0x00"]
      expectedOutHex := "7c01000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , { name           := "staticcall_seeded_address_warm_access_gas_no_context"
      bytecode       := staticcallToRepeatedTargetBytecode "0xbb" ["0x5a", "0x00"]
      expectedOutHex := "400b000000000000000000000000000000000000000000000000000000000000"
      env            := "address=0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
      gasLimit       := "3000" }
  , { name             := "staticcall_cold_access_oog_no_context"
      bytecode         := staticcallToRepeatedTargetBytecode "0xbb" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2617" }
  , -- ECRECOVER currently remains an empty-returndata success stub,
    -- but now charges its fixed inner precompile gas of 3000. CALL
    -- total here is seven PUSH1s (21) + CALL warm static base (100)
    -- + ECRECOVER fixed gas (3000) = 3121.
    { name           := "call_ecrecover_precompile_fixed_gas_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3121" }
  , -- One gas less reaches the ECRECOVER branch after CALL's static
    -- charge, then fails in the inner precompile-gas helper.
    { name             := "call_ecrecover_precompile_fixed_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "3120" }
  , -- STATICCALL has six PUSH1s, so its exact threshold is 18 + 100
    -- + 3000 = 3118.
    { name           := "staticcall_ecrecover_precompile_fixed_gas_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3118" }
  , -- ECRECOVER staging uses buffer_read semantics. A one-byte input
    -- stages that byte and zero-fills the remaining hash/v/r/s bytes,
    -- while the current placeholder still succeeds with empty returndata.
    { name           := "call_ecrecover_stage_len1_success"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3124" }
  , -- 40 bytes reaches into the v word; bytes 40..128 are zero-filled.
    { name           := "call_ecrecover_stage_partial_v_success"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x28, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3127" }
  , -- 127 bytes copies through the s word and zero-fills exactly the
    -- final byte of the staged 128-byte ECRECOVER input.
    { name           := "staticcall_ecrecover_stage_partial_s_success"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x7f, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3130" }
  , -- The v gate accepts only the 32-byte integer 27 or 28. These
    -- cases write the low v byte at memory[63], stage 64 input bytes,
    -- and keep the current empty-returndata placeholder behavior.
    { name           := "call_ecrecover_v_zero_empty_returndata"
      bytecode       := "0x60, 0x00, 0x60, 0x3f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_v_26_empty_returndata"
      bytecode       := "0x60, 0x1a, 0x60, 0x3f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_v_27_placeholder_success"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_v_28_placeholder_success"
      bytecode       := "0x60, 0x1c, 0x60, 0x3f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_v_29_empty_returndata"
      bytecode       := "0x60, 0x1d, 0x60, 0x3f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , -- With valid v, r=0 or s=0 is a successful ECRECOVER call with
    -- empty returndata. A nonzero r/s pair still reaches the placeholder.
    { name           := "call_ecrecover_zero_r_empty_returndata"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x60, 0x01, 0x60, 0x7f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_zero_s_empty_returndata"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x60, 0x01, 0x60, 0x5f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_nonzero_r_s_placeholder_success"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x60, 0x01, 0x60, 0x5f, 0x53, 0x60, 0x01, 0x60, 0x7f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , -- ECRECOVER rejects r or s at/above the secp256k1 group order.
    -- Below-boundary cases keep reaching the placeholder success path.
    { name           := "call_ecrecover_r_order_empty_returndata"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41, 0x60, 0x40, 0x52, 0x60, 0x01, 0x60, 0x7f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_r_order_minus_one_placeholder_success"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x40, 0x60, 0x40, 0x52, 0x60, 0x01, 0x60, 0x7f, 0x53, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_s_order_empty_returndata"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x60, 0x01, 0x60, 0x5f, 0x53, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x41, 0x60, 0x60, 0x52, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , { name           := "call_ecrecover_s_order_minus_one_placeholder_success"
      bytecode       := "0x60, 0x1b, 0x60, 0x3f, 0x53, 0x60, 0x01, 0x60, 0x5f, 0x53, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36, 0x41, 0x40, 0x60, 0x60, 0x52, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "10000" }
  , -- CALL to basic precompile address 0x04 (IDENTITY) reaches the
    -- precompile-specific frame stub and pushes success = 1. Stack
    -- args are pushed bottom-to-top: out_size, out_off, in_size,
    -- in_off, value, to, gas.
    { name           := "call_identity_precompile_stub_success"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- The same zero-length IDENTITY CALL has seven PUSH1 opcodes
    -- (21 gas), CALL's warm static base (100), and the new inner
    -- precompile base charge (15). At gasLimit=136 it exactly fits.
    { name           := "call_identity_precompile_base_gas_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "136" }
  , -- One less unit reaches the IDENTITY body after CALL's static
    -- charge, then fails in the shared precompile inner-gas helper.
    { name             := "call_identity_precompile_base_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "135" }
  , -- IDENTITY charges 15 + 3 * ceil(input_size / 32). CALL also
    -- charges memory expansion for the one-word input range, so total =
    -- 21 PUSH gas + 100 CALL gas + 3 memory gas + 18 inner gas.
    { name           := "call_identity_precompile_gas_len1_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "142" }
  , -- 32 bytes is still one charged word, so the exact threshold
    -- matches the one-byte case.
    { name           := "call_identity_precompile_gas_len32_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x20, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "142" }
  , -- 33 bytes rounds up to two words for both CALL memory expansion and
    -- IDENTITY word gas.
    { name           := "call_identity_precompile_gas_len33_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "148" }
  , -- One less unit fails in the word-linear helper for the 33-byte
    -- IDENTITY case.
    { name             := "call_identity_precompile_gas_len33_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "147" }
  , -- A non-zero output window is charged as CALL memory expansion even
    -- when the IDENTITY returndata is empty.
    { name           := "call_identity_precompile_output_memory_gas_exact"
      bytecode       := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "139" }
  , { name             := "call_identity_precompile_output_memory_gas_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "138" }
  , -- STATICCALL to basic precompile address 0x04 reaches the same
    -- frame surface. Args: out_size, out_off, in_size, in_off, to,
    -- gas.
    { name           := "staticcall_identity_precompile_stub_success"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- IDENTITY via CALL copies three input bytes from memory[0..3)
    -- into caller output memory[0x40..0x43). POP drops the success
    -- word; RETURN exposes the copied bytes directly.
    { name             := "call_identity_precompile_copies_memory"
      bytecode         := "0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0xbb, 0x60, 0x01, 0x53, 0x60, 0xcc, 0x60, 0x02, 0x53, 0x60, 0x03, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x03, 0x60, 0x40, 0xf3"
      expectedOutHex   := "aabbcc0000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- STATICCALL to IDENTITY with output_size=2 and input_size=3
    -- copies only the short caller output buffer. Returning three
    -- bytes from the output region proves the third byte remains zero.
    { name             := "staticcall_identity_precompile_short_output"
      bytecode         := "0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0xbb, 0x60, 0x01, 0x53, 0x60, 0xcc, 0x60, 0x02, 0x53, 0x60, 0x02, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xfa, 0x50, 0x60, 0x03, 0x60, 0x40, 0xf3"
      expectedOutHex   := "aabb000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- STATICCALL to SHA256 over empty input writes the canonical
    -- sha256("") digest to caller memory.
    { name             := "staticcall_sha256_precompile_empty"
      bytecode         := "0x60, 0x20, 0x60, 0x40, 0x60, 0x00, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xfa, 0x50, 0x60, 0x20, 0x60, 0x40, 0xf3"
      expectedOutHex   := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
      expectedHaltKind := "0100000000000000" }
  , -- SHA256 empty input charges 60 inner gas; with six PUSH1s and
    -- STATICCALL's warm static base, total = 178.
    { name           := "staticcall_sha256_precompile_gas_empty_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "178" }
  , -- One byte and 32 bytes both charge one SHA256 word plus one
    -- CALL memory-expansion word: total = 193.
    { name           := "staticcall_sha256_precompile_gas_len1_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "193" }
  , { name           := "staticcall_sha256_precompile_gas_len32_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x20, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "193" }
  , -- 33 bytes charges two SHA256 words and two memory-expansion words.
    { name           := "staticcall_sha256_precompile_gas_len33_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "208" }
  , { name             := "staticcall_sha256_precompile_gas_len33_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "207" }
  , -- CALL to SHA256 over memory[0..3) = "abc".
    { name             := "call_sha256_precompile_abc"
      bytecode         := "0x60, 0x61, 0x60, 0x00, 0x53, 0x60, 0x62, 0x60, 0x01, 0x53, 0x60, 0x63, 0x60, 0x02, 0x53, 0x60, 0x20, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x20, 0x60, 0x40, 0xf3"
      expectedOutHex   := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
      expectedHaltKind := "0100000000000000" }
  , -- CALL to SHA256 with address 0x02 + 2^160. The EVM masks
    -- external addresses to the low 160 bits, so this must dispatch
    -- exactly like precompile address 0x02.
    { name             := "call_sha256_precompile_masked_high_address"
      bytecode         := "0x60, 0x61, 0x60, 0x00, 0x53, 0x60, 0x62, 0x60, 0x01, 0x53, 0x60, 0x63, 0x60, 0x02, 0x53, 0x60, 0x20, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x00, 0x74, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x20, 0x60, 0x40, 0xf3"
      expectedOutHex   := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
      expectedHaltKind := "0100000000000000" }
  , -- STATICCALL follows the same low-160 address masking rule.
    { name             := "staticcall_sha256_precompile_masked_high_address"
      bytecode         := "0x60, 0x61, 0x60, 0x00, 0x53, 0x60, 0x62, 0x60, 0x01, 0x53, 0x60, 0x63, 0x60, 0x02, 0x53, 0x60, 0x20, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x74, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x60, 0xff, 0xfa, 0x50, 0x60, 0x20, 0x60, 0x40, 0xf3"
      expectedOutHex   := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
      expectedHaltKind := "0100000000000000" }
  , -- CALLDATACOPY loads 200 bytes of 0xaa into memory, then CALL
    -- hashes it through SHA256. This covers the multi-block path.
    { name             := "call_sha256_precompile_aa200"
      bytecode         := "0x60, 0xc8, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x20, 0x60, 0x40, 0x60, 0xc8, 0x60, 0x00, 0x60, 0x00, 0x60, 0x02, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x20, 0x60, 0x40, 0xf3"
      calldata         := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex   := "605ed279d0a1af786c79054f9424d196ed6a1f0331100a923d711885d42099bb"
      expectedHaltKind := "0100000000000000" }
  , -- MODEXP with an empty input decodes all three length fields as zero.
    -- execution-specs charges the 500 minimum gas and returns empty output.
    { name           := "staticcall_modexp_empty_gas_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "618" }
  , -- One gas short reaches the MODEXP runtime body and fails on the
    -- precompile minimum-gas charge before reporting success.
    { name             := "staticcall_modexp_empty_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "617" }
  , -- A present but all-zero 96-byte MODEXP header has the same decoded
    -- lengths as empty input and also returns success with empty returndata.
    -- The nonempty input window still pays STATICCALL memory expansion gas.
    { name           := "staticcall_modexp_zero_header_success"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x60, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "627" }
  , -- MODEXP header with modulus_len=1 charges the decoded 500 minimum.
    -- Missing modulus bytes decode as zero, so the one-byte output is 0 and
    -- the precompile succeeds.
    { name           := "staticcall_modexp_modlen1_gas_exact"
      bytecode       := "0x60, 0x60, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x60, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      calldata       := "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "648" }
  , -- One gas short proves the nonzero decoded-header path charges before
    -- the output path runs.
    { name             := "staticcall_modexp_modlen1_out_of_gas"
      bytecode         := "0x60, 0x60, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x60, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      calldata         := "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "647" }
  , -- Small nonzero MODEXP succeeds through the bounded software path:
    -- 2^5 mod 13 = 6, returned as exactly modulus_len=1 byte.
    { name             := "staticcall_modexp_small_success_output"
      bytecode         := "0x60, 0x63, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x01, 0x60, 0x80, 0x60, 0x63, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x50, 0x60, 0x01, 0x60, 0x80, 0xf3"
      calldata         := "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000102050d"
      expectedOutHex   := "0600000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000"
      expectedReturnDataCopied := "0100000000000000"
      expectedReturnDataLength := "0100000000000000"
      expectedReturnDataHex    := "06" }
  , -- out_size=0 truncates the call-memory copy, but RETURNDATASIZE still
    -- reports the full MODEXP returndata length.
    { name           := "staticcall_modexp_small_returndatasize"
      bytecode       := "0x60, 0x63, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x80, 0x60, 0x63, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x50, 0x3d, 0x00"
      calldata       := "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000102050d"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- RETURNDATACOPY reads the retained MODEXP byte even when the call's
    -- direct output copy was truncated to zero bytes.
    { name             := "staticcall_modexp_small_returndatacopy"
      bytecode         := "0x60, 0x63, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x80, 0x60, 0x63, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x50, 0x60, 0x01, 0x60, 0x00, 0x60, 0x80, 0x3e, 0x60, 0x01, 0x60, 0x80, 0xf3"
      calldata         := "0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000102050d"
      expectedOutHex   := "0600000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- modulus_len=129 makes max_len=129, words=17, complexity=2*17^2=578,
    -- iterations=1, so MODEXP gas is 578 rather than the 500 minimum.
    { name           := "staticcall_modexp_modlen129_gas_exact"
      bytecode       := "0x60, 0x60, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x60, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      calldata       := "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000081"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "726" }
  , -- Component lengths above 1024 fail before the inner MODEXP gas charge:
    -- gas=148 covers CALLDATACOPY plus STATICCALL setup but is below 500.
    { name           := "staticcall_modexp_modlen1025_fails_before_gas"
      bytecode       := "0x60, 0x60, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x60, 0x60, 0x00, 0x60, 0x05, 0x60, 0xff, 0xfa, 0x00"
      calldata       := "0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000401"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "148" }
  , -- CALL to inactive near-zero address 0x12 routes as an absent
    -- account, not as a precompile body: success = 1, empty returndata.
    { name             := "call_inactive_precompile_0x12_absent_success"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x12, 0x60, 0x00, 0xf1, 0x00"
      expectedOutHex   := "0100000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- STATICCALL to inactive secp-adjacent address 0x101 follows the
    -- same absent-account path and succeeds with no returndata.
    { name             := "staticcall_inactive_precompile_0x101_absent_success"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x01, 0x60, 0x00, 0xfa, 0x00"
      expectedOutHex   := "0100000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- The inactive-address path leaves RETURNDATASIZE at zero.
    { name             := "call_inactive_precompile_0x12_empty_returndata"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x12, 0x60, 0x00, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- BN254 ADD is an Amsterdam active precompile at 0x06. The current
    -- backend wrapper safe-fails, but the runtime still charges the fixed
    -- 150 inner gas. With gasLimit=300: seven PUSH1s (21) + CALL warm
    -- static base (100) + BN254 ADD (150) + GAS (2) leaves 27.
    { name           := "call_bn254_add_fixed_gas_after_call"
      bytecode       := callPrecompileBytecode "0x06" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "1b00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "300" }
  , -- One gas short for CALL + BN254 ADD reaches the fixed-gas helper and OOGs.
    { name             := "call_bn254_add_fixed_gas_out_of_gas"
      bytecode         := callPrecompileBytecode "0x06" "0x00" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "270" }
  , -- Short input is accepted using execution-specs buffer_read zero padding;
    -- the current backend safe-fail surfaces CALL success word 0 and empty
    -- returndata, not an invalid-length dispatcher failure.
    { name             := "call_bn254_add_short_input_backend_failure"
      bytecode         := callPrecompileBytecode "0x06" "0x01" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "10000" }
  , -- BN254 MUL at 0x07 charges fixed 6000 gas. With gasLimit=6200:
    -- seven PUSH1s (21) + CALL warm static base (100) + MUL (6000) +
    -- GAS (2) leaves 77.
    { name           := "call_bn254_mul_fixed_gas_after_call"
      bytecode       := callPrecompileBytecode "0x07" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "4d00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "6200" }
  , { name             := "call_bn254_mul_fixed_gas_out_of_gas"
      bytecode         := callPrecompileBytecode "0x07" "0x00" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "6120" }
  , -- STATICCALL follows the same 0x07 active-precompile dispatch. Six PUSH1s
    -- (18) + STATICCALL warm static base (100) + MUL (6000) + GAS (2) leaves
    -- 80 from gasLimit=6200.
    { name           := "staticcall_bn254_mul_fixed_gas_after_call"
      bytecode       := staticcallPrecompileBytecode "0x07" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "5000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "6200" }
  , -- BN254 pairing charges 45000 for zero complete pairs. Seven PUSH1s (21),
    -- CALL warm static base (100), pairing gas (45000), and GAS (2) leave 77.
    { name           := "call_bn254_pairing_zero_pairs_gas_after_call"
      bytecode       := callPrecompileBytecode "0x08" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "4d00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "45200" }
  , -- One complete 192-byte pair costs 45000 + 34000, plus 18 gas for the
    -- 192-byte CALL input memory expansion. The current backend safe-fails,
    -- but gas after CALL proves the one-pair charge.
    { name           := "call_bn254_pairing_one_pair_gas_after_call"
      bytecode       := callPrecompileBytecode "0x08" "0xc0" ["0x5a", "0x00"]
      expectedOutHex := "3b00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "79200" }
  , -- Non-multiple length is rejected after the base gas is consumed, leaving
    -- empty returndata and normal halt after POP + RETURNDATASIZE.
    { name             := "call_bn254_pairing_nonmultiple_length_after_charge"
      bytecode         := callPrecompileBytecode "0x08" "0x01" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "50000" }
  , -- One gas short reaches the BN254 pairing gas helper and exits OOG.
    { name             := "call_bn254_pairing_base_gas_out_of_gas"
      bytecode         := callPrecompileBytecode "0x08" "0x00" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "45120" }
  , -- Valid-length input reaches the deterministic backend EFAIL wrapper, so
    -- CALL success is 0 and RETURNDATASIZE remains zero.
    { name             := "call_bn254_pairing_backend_failure_empty_returndata"
      bytecode         := callPrecompileBytecode "0x08" "0x00" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "100000" }
  , -- BLAKE2F invalid length fails before reading rounds, so only CALL static
    -- gas is consumed. With gasLimit=200: seven PUSH1s (21) + CALL warm
    -- static base (100) + GAS (2) leaves 77.
    { name           := "call_blake2f_invalid_length_no_rounds_charge"
      bytecode       := callPrecompileBytecode "0x09" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "4d00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "200" }
  , -- Exact 213-byte BLAKE2F input with all-zero payload has rounds=0. The
    -- nonempty input window still pays 21 gas for memory expansion; the
    -- current backend safe-fails, but gas after CALL proves no rounds charge.
    { name           := "call_blake2f_rounds_zero_fixed_gas_after_call"
      bytecode       := callPrecompileBytecode "0x09" "0xd5" ["0x5a", "0x00"]
      expectedOutHex := "3800000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "200" }
  , -- Store rounds byte data[3]=1. Prefix cost is two PUSH1s, MSTORE8, and
    -- one-word memory expansion; CALL then expands the 213-byte input window
    -- from 32 to 224 bytes. With rounds=1, gasLimit=200 leaves 46 after GAS.
    { name           := "call_blake2f_rounds_one_fixed_gas_after_call"
      bytecode       := callPrecompileBytecodeWithPrefix
        ["0x60", "0x01", "0x60", "0x03", "0x53"] "0x09" "0xd5" ["0x5a", "0x00"]
      expectedOutHex := "2e00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "200" }
  , -- One gas short reaches the BLAKE2F rounds charge and exits OOG.
    { name             := "call_blake2f_rounds_one_out_of_gas"
      bytecode         := callPrecompileBytecodeWithPrefix
        ["0x60", "0x01", "0x60", "0x03", "0x53"] "0x09" "0xd5" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "133" }
  , -- Final flag data[212]=2 is invalid after the rounds-gas phase and surfaces
    -- as normal precompile failure with empty returndata.
    { name             := "call_blake2f_invalid_final_flag_empty_returndata"
      bytecode         := callPrecompileBytecodeWithPrefix
        ["0x60", "0x02", "0x60", "0xd4", "0x53"] "0x09" "0xd5" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "10000" }
  , -- Valid-length input reaches the deterministic backend EFAIL wrapper, so
    -- CALL success is 0 and RETURNDATASIZE remains zero.
    { name             := "call_blake2f_backend_failure_empty_returndata"
      bytecode         := callPrecompileBytecode "0x09" "0xd5" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "10000" }
  , -- KZG point evaluation rejects non-192-byte input before fixed gas. With
    -- gasLimit=200: seven PUSH1s (21) + CALL warm static base (100) + GAS (2)
    -- leaves 77.
    { name           := "call_kzg_point_eval_invalid_length_no_fixed_gas"
      bytecode       := callPrecompileBytecode "0x0a" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "4d00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "200" }
  , -- Exact 192-byte KZG input charges fixed 50000 gas before versioned-hash
    -- validation, plus 18 gas for CALL input memory expansion. The all-zero
    -- payload has version byte 0, so it fails after the charge with the same
    -- gasRemaining as the Python execution-spec path.
    { name           := "call_kzg_point_eval_fixed_gas_after_call"
      bytecode       := callPrecompileBytecode "0x0a" "0xc0" ["0x5a", "0x00"]
      expectedOutHex := "3b00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "50200" }
  , -- One gas short reaches the fixed KZG gas helper and exits OOG.
    { name             := "call_kzg_point_eval_fixed_gas_out_of_gas"
      bytecode         := callPrecompileBytecode "0x0a" "0xc0" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "50120" }
  , -- Valid-length input reaches the deterministic backend EFAIL wrapper, so
    -- CALL success is 0 and RETURNDATASIZE remains zero.
    { name             := "call_kzg_point_eval_backend_failure_empty_returndata"
      bytecode         := callPrecompileBytecodeWithPrefix
        ["0x7f",
         "0x01", "0x80", "0xe5", "0x91", "0x63", "0xce", "0x24", "0x4b",
         "0xb4", "0xbb", "0x62", "0x11", "0xf4", "0x8c", "0x7b", "0x46",
         "0xf8", "0x8a", "0x4f", "0x40", "0x94", "0x3e", "0x84", "0xeb",
         "0x99", "0xbd", "0xc4", "0x1e", "0x12", "0x9b", "0xd2", "0x93",
         "0x60", "0x00", "0x52"] "0x0a" "0xc0" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "100000" }
  , -- Version byte 1 with a zero hash suffix still fails the execution-spec
    -- versioned-hash gate before the backend proof verifier.
    { name             := "call_kzg_point_eval_invalid_versioned_hash_empty_returndata"
      bytecode         := callPrecompileBytecodeWithPrefix
        ["0x60", "0x01", "0x60", "0x00", "0x53"] "0x0a" "0xc0" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "100000" }
  , -- P256VERIFY is active at address 0x100. Invalid length is checked after
    -- the fixed 6900 gas charge and returns successful empty returndata.
    { name           := "call_p256verify_invalid_length_after_charge"
      bytecode       := callPrecompileBytecodeWithTargetBytes
        ["0x61", "0x01", "0x00"] "0x00" ["0x5a", "0x00"]
      expectedOutHex := "4d00000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "7100" }
  , -- One gas short reaches the fixed P256VERIFY gas helper and exits OOG.
    { name             := "call_p256verify_fixed_gas_out_of_gas"
      bytecode         := callPrecompileBytecodeWithTargetBytes
        ["0x61", "0x01", "0x00"] "0xa0" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "7020" }
  , -- Valid-length input reaches the deterministic backend EFAIL wrapper, so
    -- CALL success is 0 and RETURNDATASIZE remains zero.
    { name             := "call_p256verify_backend_failure_empty_returndata"
      bytecode         := callPrecompileBytecodeWithTargetBytes
        ["0x61", "0x01", "0x00"] "0xa0" ["0x50", "0x3d", "0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "10000" }
  , -- BLS12 G1 ADD rejects invalid input length before any accelerator body.
    { name             := "call_bls12_g1_add_invalid_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0b, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 G1 ADD now invokes the backend wrapper. Current
    -- ziskemu safe-fails the backend route, so EVM observes precompile
    -- failure instead of the earlier placeholder success.
    { name             := "call_bls12_g1_add_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0b, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- G1 ADD charges fixed inner gas 375 after the valid-length gate.
    -- Seven PUSHes (21) + CALL warm static base (100) + 256-byte input
    -- memory expansion (24) + 375 = 520.
    { name             := "call_bls12_g1_add_fixed_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0b, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "520" }
  , -- One less gas reaches the valid G1 ADD path, then fails before
    -- invoking the backend wrapper.
    { name             := "call_bls12_g1_add_fixed_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0b, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "519" }
  , -- BLS12 G1 MSM rejects empty input.
    { name             := "staticcall_bls12_g1_msm_zero_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0c, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- BLS12 G1 MSM rejects non-160-multiple input.
    { name             := "call_bls12_g1_msm_non_multiple_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0xa1, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0c, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 G1 MSM now invokes the backend wrapper. Current
    -- ziskemu returns deterministic EFAIL, so EVM observes precompile failure.
    { name             := "staticcall_bls12_g1_msm_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0xa0, 0x60, 0x00, 0x60, 0x0c, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- One G1 MSM pair charges 1 * 12000 * discount(1) / 1000 = 12000.
    -- Six PUSHes (18) + STATICCALL warm static base (100) + 160-byte input
    -- memory expansion (15) + 12000 = 12133.
    { name             := "staticcall_bls12_g1_msm_one_pair_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0xa0, 0x60, 0x00, 0x60, 0x0c, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "12133" }
  , -- One less gas fails in the G1 MSM dynamic precompile charge.
    { name             := "staticcall_bls12_g1_msm_one_pair_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0xa0, 0x60, 0x00, 0x60, 0x0c, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "12132" }
  , -- BLS12 G2 ADD rejects invalid input length before any accelerator body.
    { name             := "call_bls12_g2_add_invalid_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0d, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 G2 ADD now invokes the backend wrapper. Current
    -- ziskemu returns deterministic EFAIL, so EVM observes precompile failure.
    { name             := "call_bls12_g2_add_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x02, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0d, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Exact gas reaches the G2 ADD backend and observes deterministic failure:
    -- seven PUSHes (21) + CALL warm static base (100) + 512-byte input memory
    -- expansion (48) + fixed G2 ADD gas (600) = 769.
    { name             := "call_bls12_g2_add_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x02, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0d, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "769" }
  , -- One less gas fails in the G2 ADD fixed precompile charge.
    { name             := "call_bls12_g2_add_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x02, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0d, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "768" }
  , -- BLS12 G2 MSM rejects empty input.
    { name             := "staticcall_bls12_g2_msm_zero_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0e, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- BLS12 G2 MSM rejects non-288-multiple input.
    { name             := "call_bls12_g2_msm_non_multiple_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x21, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0e, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 G2 MSM now invokes the backend wrapper. Current
    -- ziskemu returns deterministic EFAIL, so EVM observes precompile failure.
    { name             := "staticcall_bls12_g2_msm_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x20, 0x60, 0x00, 0x60, 0x0e, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Exact gas reaches the one-pair G2 MSM backend and observes failure:
    -- six PUSHes (18) + STATICCALL warm static base (100) + 288-byte input
    -- memory expansion (27) + one-pair G2 MSM gas (22500) = 22645.
    { name             := "staticcall_bls12_g2_msm_one_pair_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x20, 0x60, 0x00, 0x60, 0x0e, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "22645" }
  , -- One less gas fails in the G2 MSM dynamic precompile charge.
    { name             := "staticcall_bls12_g2_msm_one_pair_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x20, 0x60, 0x00, 0x60, 0x0e, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "22644" }
  , -- BLS12 pairing rejects empty input before invoking the backend.
    { name             := "call_bls12_pairing_zero_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0f, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 pairing invokes the backend wrapper. Current ziskemu
    -- returns deterministic EFAIL, so EVM observes precompile failure.
    { name             := "call_bls12_pairing_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0f, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Exact gas reaches one-pair BLS12 pairing and observes backend failure:
    -- seven PUSHes (21) + CALL warm static base (100) + 384-byte input memory
    -- expansion (36) + one-pair pairing gas (70300) = 70457.
    { name             := "call_bls12_pairing_one_pair_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0f, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "70457" }
  , -- One less gas fails in the BLS12 pairing dynamic precompile charge.
    { name             := "call_bls12_pairing_one_pair_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x0f, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "70456" }
  , -- BLS12 map-Fp-to-G1 rejects non-64-byte input.
    { name             := "staticcall_bls12_map_fp_to_g1_invalid_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x41, 0x60, 0x00, 0x60, 0x10, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 map-Fp-to-G1 invokes the backend wrapper and safe-fails.
    { name             := "staticcall_bls12_map_fp_to_g1_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x10, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Exact gas reaches map-Fp-to-G1 and observes backend failure:
    -- six PUSHes (18) + STATICCALL warm static base (100) + 64-byte input
    -- memory expansion (6) + fixed map gas (5500) = 5624.
    { name             := "staticcall_bls12_map_fp_to_g1_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x10, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "5624" }
  , -- One less gas fails in the map-Fp-to-G1 fixed precompile charge.
    { name             := "staticcall_bls12_map_fp_to_g1_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x40, 0x60, 0x00, 0x60, 0x10, 0x60, 0xff, 0xfa, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "5623" }
  , -- BLS12 map-Fp2-to-G2 rejects non-128-byte input.
    { name             := "call_bls12_map_fp2_to_g2_invalid_length_fails"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x81, 0x60, 0x00, 0x60, 0x00, 0x60, 0x11, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Valid-length BLS12 map-Fp2-to-G2 invokes the backend wrapper and safe-fails.
    { name             := "call_bls12_map_fp2_to_g2_valid_length_backend_failure"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x11, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- Exact gas reaches map-Fp2-to-G2 and observes backend failure:
    -- seven PUSHes (21) + CALL warm static base (100) + 128-byte input memory
    -- expansion (12) + fixed map gas (23800) = 23933.
    { name             := "call_bls12_map_fp2_to_g2_gas_exact"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x11, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000"
      gasLimit         := "23933" }
  , -- One less gas fails in the map-Fp2-to-G2 fixed precompile charge.
    { name             := "call_bls12_map_fp2_to_g2_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x11, 0x60, 0xff, 0xf1, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "23932" }
  , -- CALL to IDENTITY records the full precompile returndata buffer,
    -- so RETURNDATASIZE reports the input size even when out_size is short.
    { name             := "call_identity_returndatasize_three"
      bytecode         := "0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0xbb, 0x60, 0x01, 0x53, 0x60, 0xcc, 0x60, 0x02, 0x53, 0x60, 0x01, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x3d, 0x00"
      expectedOutHex   := "0300000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0000000000000000" }
  , -- RETURNDATACOPY copies a bounded slice from the precompile return buffer.
    -- Here IDENTITY returned aa bb cc; copy return_data[1:3] to memory[0x80].
    { name             := "call_identity_returndatacopy_slice"
      bytecode         := "0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0xbb, 0x60, 0x01, 0x53, 0x60, 0xcc, 0x60, 0x02, 0x53, 0x60, 0x00, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x02, 0x60, 0x01, 0x60, 0x80, 0x3e, 0x60, 0x02, 0x60, 0x80, 0xf3"
      expectedOutHex   := "bbcc000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- RETURNDATACOPY can now read retained precompile bytes beyond the old
    -- 64-byte frame prefix. IDENTITY returns 128 bytes of 0xaa; copy byte 64.
    { name             := "call_identity_returndatacopy_byte64"
      bytecode         := "0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x01, 0x60, 0x40, 0x60, 0x80, 0x3e, 0x60, 0x01, 0x60, 0x80, 0xf3"
      calldata         := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex   := "aa00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- The shared precompile frame now retains 256 bytes, which is needed by
    -- EIP-2537 G2 return values. IDENTITY deterministically fills the frame;
    -- copy byte 255 through RETURNDATACOPY.
    { name             := "call_identity_returndatacopy_byte255"
      bytecode         := "0x61, 0x01, 0x00, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x61, 0x01, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x01, 0x60, 0xff, 0x60, 0x80, 0x3e, 0x60, 0x01, 0x60, 0x80, 0xf3"
      calldata         := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex   := "aa00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0100000000000000" }
  , -- execution-specs raises on RETURNDATACOPY reads past the buffer.
    { name             := "call_identity_returndatacopy_oob"
      bytecode         := "0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0xbb, 0x60, 0x01, 0x53, 0x60, 0xcc, 0x60, 0x02, 0x53, 0x60, 0x00, 0x60, 0x40, 0x60, 0x03, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x02, 0x60, 0x02, 0x60, 0x80, 0x3e, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0400000000000000" }
  , -- RETURNDATACOPY length zero charges only the opcode and setup path:
    -- zero-length IDENTITY CALL (136) + POP (2) + three PUSH1s (9) +
    -- RETURNDATACOPY static base (3) = 150.
    { name           := "call_identity_returndatacopy_gas_len0_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x00, 0x60, 0x00, 0x60, 0x80, 0x3e, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "150" }
  , -- One-byte RETURNDATACOPY charges one copy word and expands the
    -- destination memory window.
    { name           := "call_identity_returndatacopy_gas_len1_exact"
      bytecode       := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x01, 0x60, 0x00, 0x60, 0x80, 0x3e, 0x00"
      calldata       := "0xaa"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "186" }
  , -- Length 32 is still one copy word, so it has the same threshold as
    -- length 1 for this setup.
    { name           := "call_identity_returndatacopy_gas_len32_exact"
      bytecode       := "0x60, 0x20, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x20, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x20, 0x60, 0x00, 0x60, 0x80, 0x3e, 0x00"
      calldata       := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "186" }
  , -- Length 33 rounds to two copy words. Compared with length 32, both
    -- the setup CALLDATACOPY and RETURNDATACOPY charge one extra copy word.
    { name           := "call_identity_returndatacopy_gas_len33_exact"
      bytecode       := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x21, 0x60, 0x00, 0x60, 0x80, 0x3e, 0x00"
      calldata       := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "198" }
  , -- One less gas reaches RETURNDATACOPY but fails in its dynamic
    -- copy/memory gas path before writing.
    { name             := "call_identity_returndatacopy_gas_len33_out_of_gas"
      bytecode         := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x60, 0x00, 0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x60, 0x04, 0x60, 0xff, 0xf1, 0x50, 0x60, 0x21, 0x60, 0x00, 0x60, 0x80, 0x3e, 0x00"
      calldata         := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "197" }
    -- ## MULMOD (0x09) -- total runtime body. EVM pops `a` (top), then
    -- `b`, then `N`; if `N = 0` the result is zero, otherwise
    -- `(a * b) % N`.
  , -- PUSH1 0x00; PUSH1 0x05; PUSH1 0x07; MULMOD; STOP -- N=0 => 0.
    { name           := "mulmod_zero_modulus"
      bytecode       := "0x60, 0x00, 0x60, 0x05, 0x60, 0x07, 0x09, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0d; PUSH1 0x05; PUSH1 0x07; MULMOD; STOP -- (7*5)%13 = 9.
    { name           := "mulmod_small_nonzero"
      bytecode       := "0x60, 0x0d, 0x60, 0x05, 0x60, 0x07, 0x09, 0x00"
      expectedOutHex := "0900000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x0b; PUSH9 2^64; PUSH25 2^192; MULMOD; STOP.
    -- Product is 2^256, so this covers the high-product path:
    -- 2^256 % 11 = 9.
    { name           := "mulmod_high_product_nonzero"
      bytecode       := "0x60, 0x0b, 0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x78, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00"
      expectedOutHex := "0900000000000000000000000000000000000000000000000000000000000000" }
  , -- ## EXP (0x0a) — real verified body via selfCallingHandlers
    -- (evmExpComposed, _fixed_fixed x6→x22 counter fix). EVM EXP pops
    -- `a` (base, top of stack) then `exponent`; result = a ** exponent.
    -- Top of stack = last-pushed = x12+0 = base; second = exponent.
    --
    -- PUSH1 0x03; PUSH1 0x02; EXP; STOP — base=2 (top), exponent=3 → 2**3 = 8.
    -- Exercises the conditional-multiply path (exponent 3 = ...011 has
    -- set bits → mul_callable is JAL'd for both squaring and cond-mul,
    -- the path that clobbered x6 before the fix).
    { name           := "exp_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x02, 0x0a, 0x00"
      expectedOutHex := "0800000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; PUSH1 0x05; EXP; STOP — base=5 (top), exponent=0 → 5**0 = 1.
    -- Exponent 0 has no set bits, so the loop only squares (result stays
    -- at the prologue's accumulator init of 1) across all 256 bits — a
    -- strong exercise of the per-limb counter reload across all 4 limbs
    -- (the exact x22 state that mul_callable used to corrupt as x6).
    { name           := "exp_zero"
      bytecode       := "0x60, 0x00, 0x60, 0x05, 0x0a, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; PUSH1 0x00; EXP; STOP - 0**0 follows Python/EVM pow
    -- semantics and produces 1.
    { name           := "exp_zero_zero"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x0a, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x05; PUSH1 0x00; EXP; STOP - 0**5 = 0.
    { name           := "exp_zero_positive"
      bytecode       := "0x60, 0x05, 0x60, 0x00, 0x0a, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH9 2^64; PUSH1 0x00; EXP; STOP - high-limb exponent path:
    -- 0**(2^64) = 0. A low-limb-only exponent implementation would
    -- incorrectly see exponent zero and return 1.
    { name           := "exp_zero_high_exponent"
      bytecode       := "0x68, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x00, 0x0a, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH17 2^128; PUSH1 0x01; EXP; STOP - 1**large = 1.
    { name           := "exp_one_large_exponent"
      bytecode       := "0x70, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x60, 0x01, 0x0a, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH32 max_word; EXP; STOP - (2^256-1)^2 = 1 mod 2^256.
    { name           := "exp_max_word_squared"
      bytecode       := "0x60, 0x02, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x0a, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH32 2^255; EXP; STOP - (2^255)^2 = 0 mod 2^256.
    { name           := "exp_two_255_squared"
      bytecode       := "0x60, 0x02, 0x7f, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- EXP gas: exponent zero charges only PUSH1*2 + EXP base = 16.
    { name           := "exp_gas_zero_exponent_exact"
      bytecode       := "0x60, 0x00, 0x60, 0x05, 0x0a, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "16" }
  , -- EXP gas: one exponent byte adds 50, so PUSH1*2 + EXP = 66.
    { name           := "exp_gas_one_byte_exact"
      bytecode       := "0x60, 0x01, 0x60, 0x02, 0x0a, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "66" }
  , -- One gas short of the one-byte exponent dynamic charge exits OOG before
    -- the EXP body writes a result.
    { name             := "exp_gas_one_byte_oog"
      bytecode         := "0x60, 0x01, 0x60, 0x02, 0x0a, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "65" }
  , -- EXP gas: all 32 exponent bytes non-zero adds 1600, so
    -- PUSH32 + PUSH1 + EXP = 1616.
    { name           := "exp_gas_max_exponent_exact"
      bytecode       := "0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x60, 0x01, 0x0a, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "1616" }
    -- ## M8 unsigned division opcodes
    -- (SDIV / SMOD deferred: their verified bodies use a saved-ra-ret
    -- pattern that bypasses the dispatcher's standard wrapper tail;
    -- integrating them needs a trampoline approach planned as the
    -- next codegen PR.)
  , -- PUSH1 0x02; PUSH1 0x0a; DIV; STOP — 10 / 2 = 5
    { name           := "div_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00"
      expectedOutHex := "0500000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x03; PUSH1 0x0a; MOD; STOP — 10 % 3 = 1
    { name           := "mod_basic"
      bytecode       := "0x60, 0x03, 0x60, 0x0a, 0x06, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
    -- ## M9 signed division opcodes (trampoline wrapper for saved-ra-ret)
  , -- PUSH1 0x02; PUSH1 0x05; SDIV; STOP — signed 5 / 2 = 2 (positive path)
    { name           := "sdiv_basic"
      bytecode       := "0x60, 0x02, 0x60, 0x05, 0x05, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x02; PUSH1 0x01; NOT; SDIV; STOP
    -- Stack at SDIV: top = NOT(1) = -2 (= 0xff..fe), second = 2.
    -- EVM SDIV pops `a` (top) then `b`; computes `a / b` in two's
    -- complement. -2 / 2 = -1 (= 0xff..ff).
    { name           := "sdiv_negative"
      bytecode       := "0x60, 0x02, 0x60, 0x01, 0x19, 0x05, 0x00"
      expectedOutHex := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
  , -- PUSH1 0x05; PUSH1 0x01; NOT; SMOD; STOP
    -- Stack at SMOD: top = -2, second = 5. EVM SMOD: a % b with
    -- sign(result) = sign(a). -2 % 5 = -2 (= 0xff..fe).
    { name           := "smod_negative"
      bytecode       := "0x60, 0x05, 0x60, 0x01, 0x19, 0x07, 0x00"
      expectedOutHex := "feffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" }
    -- ## M10 self-calling opcodes (inline mod_callable / mul_callable)
  , -- PUSH1 0x04; PUSH1 0x03; PUSH1 0x02; ADDMOD; STOP — (2+3) % 4 = 1
    -- ADDMOD pops `a` (top), then `b`, then `N`. So stack
    -- [N=4, b=3, a=2] yields (a+b) mod N = 5 mod 4 = 1.
    { name           := "addmod_basic"
      bytecode       := "0x60, 0x04, 0x60, 0x03, 0x60, 0x02, 0x08, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; PUSH1 0x03; PUSH1 0x02; ADDMOD; STOP — divisor=0 ⇒ 0
    { name           := "addmod_div_zero"
      bytecode       := "0x60, 0x00, 0x60, 0x03, 0x60, 0x02, 0x08, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x07; PUSH1 0x01; PUSH1 0x00; NOT; ADDMOD; STOP
    -- (2^256 - 1 + 1) % 7 = 2, exercising the ADD carry contribution.
    { name           := "addmod_carry_pow256_mod_7"
      bytecode       := "0x60, 0x07, 0x60, 0x01, 0x60, 0x00, 0x19, 0x08, 0x00"
      expectedOutHex := "0200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH17 (2^128 + 1); PUSH1 0x01; PUSH1 0x00; NOT; ADDMOD; STOP
    -- 2^256 % (2^128 + 1) = 1, covering a multi-limb modulus carry case.
    { name           := "addmod_carry_pow256_mod_2_128_plus_1"
      bytecode       := "0x70, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x60, 0x01, 0x60, 0x00, 0x19, 0x08, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x07; PUSH1 0x07; PUSH1 0x00; NOT; ADDMOD; STOP
    -- (2^256 - 1 + 7) % 7 = 1, exercising carry plus final subtract.
    { name           := "addmod_carry_reduced_sum_subtracts_n"
      bytecode       := "0x60, 0x07, 0x60, 0x07, 0x60, 0x00, 0x19, 0x08, 0x00"
      expectedOutHex := "0100000000000000000000000000000000000000000000000000000000000000" }
  , -- Carry-path ADDMOD with live stack words below the arguments.
    -- The deepest sentinel lands at the old `x12 + 224` temporary frame offset;
    -- after ADDMOD and five POPs it must still be the top stack word.
    { name           := "addmod_carry_preserves_deep_stack"
      bytecode       := "0x60, 0xaa, 0x60, 0x66, 0x60, 0x55, 0x60, 0x44, 0x60, 0x33, 0x60, 0x07, 0x60, 0x01, 0x60, 0x00, 0x19, 0x08, 0x50, 0x50, 0x50, 0x50, 0x50, 0x00"
      expectedOutHex := "aa00000000000000000000000000000000000000000000000000000000000000" }
    -- ## M21 real calldata (CALLDATASIZE / CALLDATALOAD / CALLDATACOPY)
    -- The dispatcher prologue now populates env.callDataPtrOff (416)
    -- and env.callDataLenOff (424) from the ziskemu `-i` input file.
    -- These three cases confirm the wiring end-to-end:
    --   1. CALLDATASIZE reads len from env.
    --   2. CALLDATALOAD reads 32 BE bytes from calldata.
    --   3. CALLDATACOPY copies calldata bytes into EVM memory; the
    --      follow-up MLOAD round-trips them back to the stack.
  , -- CALLDATASIZE; STOP with calldata = 0xdeadbeef (4 bytes).
    -- Expected: size = 4 in the low limb's low byte → "04 00...00".
    { name           := "calldatasize_with_input"
      bytecode       := "0x36, 0x00"
      calldata       := "0xdeadbeef"
      expectedOutHex := "0400000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; CALLDATALOAD; STOP with calldata = 32 bytes
    -- 0x0102…20 (same content as push32_basic). CALLDATALOAD reads
    -- 32 BE bytes from calldata[0..32] into the EVM word, then the
    -- OUTPUT_ADDR copy surfaces the 4 LE u64 limbs verbatim — the
    -- byte sequence matches push32_basic exactly.
    { name           := "calldataload_basic"
      bytecode       := "0x60, 0x00, 0x35, 0x00"
      calldata       := "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
      expectedOutHex := "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201" }
  , -- PUSH1 0x04 (size); PUSH1 0x00 (offset); PUSH1 0x00 (destOffset);
    -- CALLDATACOPY; PUSH1 0x00; MLOAD; STOP with calldata = 0xdeadbeef.
    -- Copies 4 bytes into memory[0..4]; MLOAD reads memory[0..32] BE
    -- → u256 = 0xdeadbeef << 224 (high 4 BE bytes are deadbeef, rest
    -- zero). In limbs: limb 3 = 0xdeadbeef00000000, others 0. Output
    -- LE bytes of limb 3 = 00 00 00 00 ef be ad de.
    { name           := "calldatacopy_basic"
      bytecode       := "0x60, 0x04, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x51, 0x00"
      calldata       := "0xdeadbeef"
      expectedOutHex := "00000000000000000000000000000000000000000000000000000000efbeadde" }
  , -- CALLDATACOPY one byte exact gas: PUSH1*3 (9) + static (3) +
    -- copy word (3) + memory expansion to one word (3) + final PUSH1 (3) = 21.
    { name           := "calldatacopy_gas_len1_exact"
      bytecode       := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x42, 0x00"
      calldata       := "0xaa"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "21" }
  , -- CALLDATACOPY 33 bytes exact gas: PUSH1*3 (9) + static (3) +
    -- copy two words (6) + memory expansion to two words (6) + final PUSH1 (3) = 27.
    { name           := "calldatacopy_gas_len33_exact"
      bytecode       := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x42, 0x00"
      calldata       := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "27" }
  , -- One gas short of the one-word copy charge exits before memory/body mutation.
    { name             := "calldatacopy_copy_gas_oog"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x42, 0x00"
      calldata         := "0xaa"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "14" }
    -- ## M33 real CODESIZE / CODECOPY (running-bytecode region)
    -- These read the running bytecode from `env.codeSize` (env+496, the
    -- exact length seeded by both dispatcher prologues) and the preserved
    -- code base in `x21`. No witness / external-account state is needed.
  , -- CODESIZE; STOP; then 3 trailing data bytes — total code length 5.
    -- CODESIZE pushes the FULL length (including the never-executed
    -- trailing bytes) → 5. Low limb LE = 05 00 …
    { name           := "codesize_basic"
      bytecode       := "0x38, 0x00, 0xaa, 0xbb, 0xcc"
      expectedOutHex := "0500000000000000000000000000000000000000000000000000000000000000" }
  , -- CODECOPY one in-bounds byte, then MLOAD it back.
    --   PUSH1 0x01 (size); PUSH1 0x0b (offset=11); PUSH1 0x1f (dest=31);
    --   CODECOPY; PUSH1 0x00; MLOAD; STOP; <data byte 0xab at offset 11>.
    -- code[11]=0xab is copied to memory[31]; MLOAD(0) reads it as the
    -- least-significant byte of the loaded word → V = 0xab. Low limb
    -- LE = ab 00 …
    { name           := "codecopy_basic"
      bytecode       := "0x60, 0x01, 0x60, 0x0b, 0x60, 0x1f, 0x39, 0x60, 0x00, 0x51, 0x00, 0xab"
      expectedOutHex := "ab00000000000000000000000000000000000000000000000000000000000000" }
  , -- CODECOPY entirely past len(code) → zero-fill, then MLOAD = 0.
    --   PUSH1 0x20 (size=32); PUSH1 0xff (offset=255, well past len=11);
    --   PUSH1 0x00 (dest=0); CODECOPY; PUSH1 0x00; MLOAD; STOP.
    -- Every source byte is out of bounds, so memory[0..32] is zero-filled.
    { name           := "codecopy_zero_pad"
      bytecode       := "0x60, 0x20, 0x60, 0xff, 0x60, 0x00, 0x39, 0x60, 0x00, 0x51, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- CODECOPY 33 bytes exact gas: PUSH1*3 (9) + static (3) +
    -- copy two words (6) + memory expansion to two words (6) + final PUSH1 (3) = 27.
    { name           := "codecopy_gas_len33_exact"
      bytecode       := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x39, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "27" }
  , -- One gas short of the one-word CODECOPY copy charge exits before copying.
    { name             := "codecopy_copy_gas_oog"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x39, 0x60, 0x42, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "14" }
    -- ## Runtime EXTCODECOPY gas
    -- No witness context is present in these codegen probes, so EXTCODECOPY
    -- takes its deterministic zero-fill path after charging static warm-floor,
    -- warm/cold account access, copy-word gas, and destination memory expansion.
  , -- EXTCODECOPY one byte exact gas: PUSH1*4 (12) + static (100) +
    -- cold access (2500) + copy one word (3) + memory expansion to one word
    -- (3) + final PUSH1 (3) = 2621.
    { name           := "extcodecopy_gas_len1_exact"
      bytecode       := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x3c, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "2621" }
  , -- EXTCODECOPY 33 bytes exact gas: PUSH1*4 (12) + static (100) +
    -- cold access (2500) + copy two words (6) + memory expansion to two
    -- words (6) + final PUSH1 (3) = 2627.
    { name           := "extcodecopy_gas_len33_exact"
      bytecode       := "0x60, 0x21, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x3c, 0x60, 0x42, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "2627" }
  , -- One gas short of the one-word copy charge exits before memory/body mutation.
    { name             := "extcodecopy_copy_gas_oog"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x3c, 0x60, 0x42, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "114" }
  , -- len=0 isolates account access gas. Cold non-precompile address:
    -- PUSH1*3 + PUSH20 = 12, EXTCODECOPY static = 100, cold delta = 2500,
    -- GAS = 2, so gasLimit 3000 leaves 386 = 0x182.
    { name           := "extcodecopy_cold_access_gas_no_context"
      bytecode       := extcodecopyRepeatedTargetBytecode "0xcc" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "8201000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , -- The dispatcher seeds ADDRESS as warm, so the same target skips the
    -- 2500 cold delta: 3000 - 12 - 100 - 2 = 2886 = 0xb46.
    { name           := "extcodecopy_seeded_address_warm_gas_no_context"
      bytecode       := extcodecopyRepeatedTargetBytecode "0xcc" "0x00" ["0x5a", "0x00"]
      expectedOutHex := "460b000000000000000000000000000000000000000000000000000000000000"
      env            := "address=0xcccccccccccccccccccccccccccccccccccccccc"
      gasLimit       := "3000" }
  , -- Active precompile addresses are treated as warm without table insertion.
    { name           := "extcodecopy_precompile_warm_gas_no_context"
      bytecode       := "0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x01, 0x3c, 0x5a, 0x00"
      expectedOutHex := "460b000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "3000" }
  , -- One gas short of the cold account-access delta exits before zero-fill
    -- or witness mutation.
    { name             := "extcodecopy_cold_access_oog_no_context"
      bytecode         := extcodecopyRepeatedTargetBytecode "0xcc" "0x00" ["0x00"]
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2611" }
    -- ## M22 real storage (SLOAD / SSTORE via pre-loaded slot table)
    -- The dispatcher prologue copies the input file's storage segment
    -- into a writable `evm_slot_table` (16 KiB, 256 slots × 64 B) and
    -- records the count in `env.slotTableCountOff = 448`. SLOAD /
    -- SSTORE inline-asm bodies scan the table linearly:
    --   1. round_trip      — SSTORE then SLOAD with empty preload.
    --   2. preloaded_match — SLOAD against a preloaded key.
    --   3. preloaded_no_match — SLOAD against an absent key → 0.
    --   4. overwrites_preload — SSTORE replaces a preloaded value.
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; PUSH1 0x00; SLOAD; STOP
    -- SSTORE pops key=0x00 (top) then value=0x42; appends slot.
    -- SLOAD pops key=0x00; reads value=0x42 back.
    { name           := "sstore_then_sload_round_trip"
      bytecode       := "0x60, 0x42, 0x60, 0x00, 0x55, 0x60, 0x00, 0x54, 0x00"
      expectedOutHex := "4200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; SLOAD; STOP with preload [(0x00, 0xdead)].
    -- 0xdead in limb 0 LE = ad de 00 00 00 00 00 00.
    { name           := "sload_preloaded_match"
      bytecode       := "0x60, 0x00, 0x54, 0x00"
      storage        := "(0x00, 0xdead)"
      expectedOutHex := "adde000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0xff; SLOAD; STOP with preload [(0x00, 0xdead)].
    -- key 0xff doesn't match preloaded 0x00 → SLOAD pushes zero.
    { name           := "sload_preloaded_no_match"
      bytecode       := "0x60, 0xff, 0x54, 0x00"
      storage        := "(0x00, 0xdead)"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x00; SLOAD; STOP. PUSH1 costs 3, SLOAD pays 100 static
    -- plus the 2000 cold storage-key delta, STOP costs 0.
    { name           := "sload_cold_gas_exact"
      bytecode       := "0x60, 0x00, 0x54, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "2103" }
  , -- One gas short of the first cold SLOAD must halt out-of-gas.
    { name             := "sload_cold_gas_out_of_gas"
      bytecode         := "0x60, 0x00, 0x54, 0x00"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "2102" }
  , -- Repeating the same storage key is warm: PUSH1/SLOAD/POP/PUSH1/SLOAD
    -- costs 3 + 2100 + 2 + 3 + 100 = 2208, not another cold 2000 delta.
    { name           := "sload_repeat_same_key_warm_gas_exact"
      bytecode       := "0x60, 0x00, 0x54, 0x50, 0x60, 0x00, 0x54, 0x00"
      expectedOutHex := "0000000000000000000000000000000000000000000000000000000000000000"
      gasLimit       := "2208" }
  , -- PUSH1 value; PUSH1 key; SSTORE; STOP. Clean zero -> nonzero
    -- SSTORE costs 2100 cold access + 20000 STORAGE_SET.
    { name                        := "sstore_cold_gas_exact"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedPersistentLogLength := "0100000000000000"
      gasLimit                    := "22106" }
  , -- One gas short of the first cold SSTORE must halt out-of-gas before append.
    { name                        := "sstore_cold_gas_out_of_gas"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0600000000000000"
      expectedPersistentLogLength := "0000000000000000"
      gasLimit                    := "22105" }
  , -- Clean nonzero -> nonzero update with a preloaded original costs
    -- 2100 cold access + (5000 - 2100) storage write gas.
    { name                        := "sstore_preloaded_nonzero_update_gas_exact"
      bytecode                    := "0x61, 0xbe, 0xef, 0x60, 0x00, 0x55, 0x00"
      storage                     := "(0x00, 0xdead)"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedPersistentLogLength := "0200000000000000"
      gasLimit                    := "5006" }
  , -- The second SSTORE to the same key is warm and dirty: first write costs
    -- 3 + 3 + 22100, second write costs 3 + 3 + 100, STOP costs 0.
    { name                        := "sstore_repeat_same_key_warm_gas_exact"
      bytecode                    := "0x60, 0x11, 0x60, 0x00, 0x55, 0x60, 0x22, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedPersistentLogLength := "0200000000000000"
      gasLimit                    := "22212" }
  , -- PUSH2 0xbeef; PUSH1 0x00; SSTORE; PUSH1 0x00; SLOAD; STOP with
    -- preload [(0x00, 0xdead)]. SSTORE finds a matching key and
    -- appends a new current-value entry. SLOAD reads back 0xbeef.
    -- 0xbeef in limb 0 LE = ef be 00 00 00 00 00 00.
    { name           := "sstore_overwrites_preload"
      bytecode       := "0x61, 0xbe, 0xef, 0x60, 0x00, 0x55, 0x60, 0x00, 0x54, 0x00"
      storage        := "(0x00, 0xdead)"
      expectedOutHex := "efbe000000000000000000000000000000000000000000000000000000000000" }
    -- ## M23 real RETURN / REVERT with returndata buffer + halt-kind
    -- Both opcodes graduate from M18 halt no-ops to real bodies that:
    --   - pop (offset, size)
    --   - copy memory[offset..offset+min(size,32)] to OUTPUT_ADDR[0..32]
    --     for old tests and diagnostics
    --   - write halt_kind (1 = RETURN, 2 = REVERT) to OUTPUT_ADDR + 32
    --   - record requested length at OUTPUT+64, copied length at OUTPUT+248,
    --     and copy up to 176 returned bytes at OUTPUT+72
    --   - halt via .exit_no_epilogue (skipping evmAddEpilogue's stack-top copy)
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x20; PUSH1 0x00; RETURN.
    -- MSTORE writes BE(0x42) to memory[0..32] (= 31 zero bytes then 0x42).
    -- RETURN(offset=0, size=32) copies that to OUTPUT[0..32].
    { name                     := "return_word_basic"
      bytecode                 := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3"
      expectedOutHex           := "0000000000000000000000000000000000000000000000000000000000000042"
      expectedHaltKind         := "0100000000000000"
      expectedReturnDataCopied := "2000000000000000"
      expectedReturnDataLength := "2000000000000000"
      expectedReturnDataHex    := "0000000000000000000000000000000000000000000000000000000000000042" }
  , -- PUSH1 0xff; PUSH1 0x00; MSTORE8; PUSH1 0x01; PUSH1 0x00; RETURN.
    -- MSTORE8 writes 1 byte (0xff) at memory[0]; rest of memory zero.
    -- RETURN(offset=0, size=1) copies 1 byte; OUTPUT[1..32] is zero-filled
    -- by the body's pre-copy SD pass. Exercises the size < 32 path.
    { name                     := "return_small_pads_zeros"
      bytecode                 := "0x60, 0xff, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xf3"
      expectedOutHex           := "ff00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0100000000000000"
      expectedReturnDataCopied := "0100000000000000"
      expectedReturnDataLength := "0100000000000000"
      expectedReturnDataHex    := "ff" }
  , -- PUSH1 0; PUSH1 0; RETURN. Empty returndata records zero lengths.
    { name                     := "return_empty_data"
      bytecode                 := "0x60, 0x00, 0x60, 0x00, 0xf3"
      expectedOutHex           := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0100000000000000"
      expectedReturnDataCopied := "0000000000000000"
      expectedReturnDataLength := "0000000000000000" }
  , -- RETURN over one fresh memory byte charges memory expansion:
    -- two PUSH1s (6) + RETURN static (0) + one memory word (3).
    { name                     := "return_memory_gas_len1_exact"
      bytecode                 := "0x60, 0x01, 0x60, 0x00, 0xf3"
      expectedOutHex           := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0100000000000000"
      expectedReturnDataCopied := "0100000000000000"
      expectedReturnDataLength := "0100000000000000"
      expectedReturnDataHex    := "00"
      gasLimit                 := "9" }
  , -- One less gas reaches RETURN, then fails before emitting returndata.
    { name             := "return_memory_gas_len1_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0xf3"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "8" }
  , -- At 33 bytes, RETURN rounds memory expansion to two words.
    { name                     := "return_memory_gas_len33_exact"
      bytecode                 := "0x60, 0x21, 0x60, 0x00, 0xf3"
      expectedOutHex           := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0100000000000000"
      expectedReturnDataCopied := "2100000000000000"
      expectedReturnDataLength := "2100000000000000"
      gasLimit                 := "12" }
  , -- MSTORE8 writes marker bytes at memory[0] and memory[40]; RETURN(size=41)
    -- keeps the old first-32-byte prefix while exposing the full 41-byte payload.
    { name                     := "return_long_data_window"
      bytecode                 := "0x60, 0xaa, 0x60, 0x00, 0x53, 0x60, 0xbb, 0x60, 0x28, 0x53, 0x60, 0x29, 0x60, 0x00, 0xf3"
      expectedOutHex           := "aa00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0100000000000000"
      expectedReturnDataCopied := "2900000000000000"
      expectedReturnDataLength := "2900000000000000"
      expectedReturnDataHex    := "aa000000000000000000000000000000000000000000000000000000000000000000000000000000bb" }
  , -- REVERT(size=1) preserves one-byte revert data and marks halt_kind=2.
    { name                     := "revert_small_data"
      bytecode                 := "0x60, 0xee, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xfd"
      expectedOutHex           := "ee00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0200000000000000"
      expectedReturnDataCopied := "0100000000000000"
      expectedReturnDataLength := "0100000000000000"
      expectedReturnDataHex    := "ee" }
  , -- REVERT charges the same memory expansion as RETURN before producing
    -- revert data.
    { name                     := "revert_memory_gas_len1_exact"
      bytecode                 := "0x60, 0x01, 0x60, 0x00, 0xfd"
      expectedOutHex           := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0200000000000000"
      expectedReturnDataCopied := "0100000000000000"
      expectedReturnDataLength := "0100000000000000"
      expectedReturnDataHex    := "00"
      gasLimit                 := "9" }
  , -- One less gas must OOG before REVERT rollback/output semantics run.
    { name             := "revert_memory_gas_len1_out_of_gas"
      bytecode         := "0x60, 0x01, 0x60, 0x00, 0xfd"
      expectedOutHex   := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind := "0600000000000000"
      gasLimit         := "8" }
  , -- REVERT(size=41) uses the same extended data path as RETURN while
    -- preserving revert status and rollback behavior.
    { name                     := "revert_long_data_window"
      bytecode                 := "0x60, 0xcc, 0x60, 0x00, 0x53, 0x60, 0xdd, 0x60, 0x28, 0x53, 0x60, 0x29, 0x60, 0x00, 0xfd"
      expectedOutHex           := "cc00000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind         := "0200000000000000"
      expectedReturnDataCopied := "2900000000000000"
      expectedReturnDataLength := "2900000000000000"
      expectedReturnDataHex    := "cc000000000000000000000000000000000000000000000000000000000000000000000000000000dd" }
  , -- PUSH1 0x42; PUSH1 0x00; MSTORE; PUSH1 0x20; PUSH1 0x00; REVERT.
    -- Same data path as return_word_basic but byte 0xfd (REVERT) instead
    -- of 0xf3 (RETURN). Returndata bytes identical; halt_kind differs.
    -- This is the test that proves RETURN and REVERT are distinguishable.
    { name                     := "revert_word_basic"
      bytecode                 := "0x60, 0x42, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xfd"
      expectedOutHex           := "0000000000000000000000000000000000000000000000000000000000000042"
      expectedHaltKind         := "0200000000000000"
      expectedReturnDataCopied := "2000000000000000"
      expectedReturnDataLength := "2000000000000000"
      expectedReturnDataHex    := "0000000000000000000000000000000000000000000000000000000000000042" }
    -- ## M24 storage on Option A — append-log + journal + real TLOAD/TSTORE
    -- Three tests exercise the new machinery via the OUTPUT[40..48]
    -- (persistent log length) and OUTPUT[48..56] (transient log
    -- length) surfaces written by `.exit_no_epilogue`:
    --   1. SSTORE then REVERT → persistent log rolls back to checkpoint=0
    --   2. SSTORE then STOP   → persistent log commits at length=1
    --   3. TSTORE + TLOAD     → real round-trip + transient length=1
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; PUSH1 0x00; PUSH1 0x00; REVERT.
    -- SSTORE appends entry (log_length 0→1). REVERT body restores
    -- persistent log_length from checkpoint (= 0). Returndata is
    -- empty (size=0); halt_kind=2. Persistent log_length back to 0.
    { name                        := "sstore_revert_rolls_back"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xfd"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0200000000000000"
      expectedPersistentLogLength := "0000000000000000" }
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; STOP.
    -- SSTORE appends entry (log_length 0→1). STOP commits — no
    -- rollback. Result is the post-SSTORE stack top (stack empty,
    -- evm_stack_top region is .zero-initialised so the 32 bytes
    -- read are all zero). Halt_kind=0. Persistent log_length=1.
    { name                        := "sstore_no_revert_commits"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0000000000000000"
      expectedPersistentLogLength := "0100000000000000" }
  , -- PUSH1 0x42; PUSH1 0x00; TSTORE; PUSH1 0x00; TLOAD; STOP.
    -- TSTORE appends transient entry (transient_log_length 0→1).
    -- TLOAD scans transient log, finds entry, pushes 0x42 onto stack.
    -- STOP surfaces stack top = 0x42. **Proves TLOAD/TSTORE moved
    -- off the M17 no-op into real Option A semantics.**
    { name                       := "tstore_tload_round_trip"
      bytecode                   := "0x60, 0x42, 0x60, 0x00, 0x5d, 0x60, 0x00, 0x5c, 0x00"
      expectedOutHex             := "4200000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind           := "0000000000000000"
      expectedTransientLogLength := "0100000000000000" }
    -- ## M25 post-state slot serializer (modified slots at OUTPUT+56)
    -- The dispatcher epilogue walks the persistent log from end,
    -- dedups against already-emitted slotKeys, and writes
    --   OUTPUT[56..64] = numModifiedPersistentSlots (u64 LE, ≤ 3)
    --   OUTPUT[64..]   = N × (slotKey:32, current:32)
    -- in **reverse write order** (most-recently-modified first).
    -- Bytes are in EVM-stack byte order (4 LE u64 limbs).
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; STOP.
    -- Empty preload. After SSTORE: 1 entry (key=0, value=0x42).
    -- Stack empty after SSTORE → result = 32 zeros (from .zero
    -- evm_stack region). Confirms basic post-state emission.
    { name                        := "sstore_post_state_single_slot"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0000000000000000"
      expectedPersistentLogLength := "0100000000000000"
      expectedPostStorage         := "010000000000000000000000000000000000000000000000000000000000000000000000000000004200000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x42; PUSH1 0x00; SSTORE; PUSH1 0x00; PUSH1 0x00; REVERT.
    -- SSTORE appends (length 0→1). REVERT rolls back length → 0.
    -- The dedup loop sees empty log and exits early, writing only
    -- the count cell = 0. **Proves rollback also clears the slot
    -- data surface.**
    { name                        := "sstore_revert_post_state_empty"
      bytecode                    := "0x60, 0x42, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xfd"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0200000000000000"
      expectedPersistentLogLength := "0000000000000000"
      expectedPostStorage         := "0000000000000000" }
  , -- PUSH1 0x11; PUSH1 0x01; SSTORE; PUSH1 0x22; PUSH1 0x02; SSTORE; STOP.
    -- Two unique slots. Dedup walks from end so entry[0] in OUTPUT
    -- = (key=0x02, value=0x22); entry[1] = (key=0x01, value=0x11).
    -- **Asserts the reverse-write-order convention.**
    { name                        := "sstore_two_slots_post_state"
      bytecode                    := "0x60, 0x11, 0x60, 0x01, 0x55, 0x60, 0x22, 0x60, 0x02, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0000000000000000"
      expectedPersistentLogLength := "0200000000000000"
      expectedPostStorage         := "02000000000000000200000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000" }
  , -- PUSH1 0x11; PUSH1 0x00; SSTORE; PUSH1 0x22; PUSH1 0x00; SSTORE; STOP.
    -- Same key twice. Log holds 2 raw entries; dedup picks the
    -- most-recent (key=0, current=0x22). Output count = 1.
    -- **Proves dedup keeps the latest value per key.**
    { name                        := "sstore_dup_keeps_latest"
      bytecode                    := "0x60, 0x11, 0x60, 0x00, 0x55, 0x60, 0x22, 0x60, 0x00, 0x55, 0x00"
      expectedOutHex              := "0000000000000000000000000000000000000000000000000000000000000000"
      expectedHaltKind            := "0000000000000000"
      expectedPersistentLogLength := "0200000000000000"
      expectedPostStorage         := "010000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000000000" }
  ]

/-- Find a test case by name. -/
def lookupTestCase (name : String) : Option OpcodeTestCase :=
  opcodeTestCases.find? (fun tc => tc.name == name)

/-- All test case names, one per line — emitted by
    `--list-test-cases` for the bash runner to enumerate. -/
def testCaseNames : List String :=
  opcodeTestCases.map OpcodeTestCase.name

/-- Build a `BuildUnit` that runs `tc.bytecode` through the M5b
    dispatcher (`tinyInterpRegistry`). The exit body is
    `evmAddEpilogue`, which copies the 32 bytes at `[x12]` (the post-
    STOP stack top) to `OUTPUT_ADDR`. -/
def buildTestCaseUnit (tc : OpcodeTestCase) : BuildUnit :=
  buildDispatchUnit tinyInterpRegistry evmAddEpilogue tc.bytecode

end EvmAsm.Codegen.Tests
