/-
  EvmAsm.Codegen.Programs.BalStorageChangeValues

  `bal_storage_change_values` (bead bmvmx.1.6.1) — parse a BAL AccountChanges'
  `storage_changes` into PARALLEL (slot key, final post-value) arrays. This is the
  value-bearing companion to `bal_recipient_storage_keys` (which yields only the
  keys); the post-values are needed by the execution-vs-BAL storage consistency
  check (bmvmx.1.6.2): the verdict will compare these against the exec storage
  log's final per-slot values to reject a BAL that execution would not produce.

  AccountChanges = RLP `[address, storage_changes, storage_reads, balance_changes,
  nonce_changes, code_changes]`. Each `storage_changes` entry is
  `[slot_key, [ [tx_index, new_value] ... ]]`; the slot's POST value is the
  `new_value` of the LAST (highest tx_index) tuple — the others are intermediate
  writes superseded within the block.

  Both keys and values are emitted as 32-byte big-endian, left-padded.

  ## Deliberately lenient slot payloads

  Slot keys and post values here accept any RLP payload of length at most 32 and
  zero-left-pad it; this reader deliberately does not require a shortest scalar
  encoding or call `rlp_content_to_u256_be`.  The local normalization is safe
  only because the supplied BAL bytes are committed into the rebuilt header via
  its BAL hash, and `block_hash_from_header` compares that header commitment
  with the payload block hash.  A non-canonical supplied payload therefore
  cannot survive the block-hash binding even when it normalizes to the same
  32-byte key/value as a canonical payload.

  This is a cross-file dependency, not a property of this reader.  The binding
  is conditional on `bv_block_hash_check_enabled`; see #10771 and #10777.
  Do not tighten or rely on this acceptance without re-auditing that gate.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_storage_change_values

    Calling convention:
      a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
      a2 = out keys ptr   (count × 32-byte big-endian slot keys)
      a3 = out values ptr (count × 32-byte big-endian post values)
    Returns:
      a0 = count of (key, value) pairs written (0 on parse failure — conservative).

    For each `storage_changes` entry: key = item 0; value = item 1 of the LAST
    tuple of item 1. Lists are consumed with cursor walks so each entry/tuple is
    visited once. -/
def balStorageChangeValues_prog : Program :=
  [ .ADDI .x2 .x2 (-128 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.bscv_vptr (GuestAddrs.bal_storage_change_values + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bscv_vptr (GuestAddrs.bal_storage_change_values + 68)),
    .SD .x5 .x13 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_change_values + 88)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 92)),
    .MV .x19 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 100)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 104)),
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 112)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 116)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_change_values + 128)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 132)),
    .MV .x19 .x10,
    .MV .x20 .x11,
    .MV .x21 .x0,
    .BEQ .x19 .x20 (brOff (GuestAddrs.bal_storage_change_values + 536) (GuestAddrs.bal_storage_change_values + 148)),
    .MV .x10 .x19,
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 160)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 164)),
    .MV .x19 .x10,
    .SUB .x23 .x10 .x12,
    .MV .x24 .x12,
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_change_values + 188)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 192)),
    .MV .x25 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 200)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 204)),
    .MV .x26 .x10,
    .SUB .x6 .x10 .x12,
    .MV .x29 .x12,
    .LI .x30 (32 : Word),
    .BLTU .x30 .x29 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 224)),
    .SLLI .x5 .x21 (5 : BitVec 6),
    .ADD .x31 .x18 .x5,
    .MV .x5 .x31,
    .LI .x30 (32 : Word),
    .BEQ .x30 .x0 (20 : BitVec 13),
    .SB .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .LI .x30 (32 : Word),
    .SUB .x30 .x30 .x29,
    .ADD .x5 .x31 .x30,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x6 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .MV .x10 .x26,
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 312)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 316)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_change_values + 328)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 332)),
    .BEQ .x10 .x11 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 336)),
    .MV .x26 .x10,
    .MV .x27 .x11,
    .BEQ .x26 .x27 (36 : BitVec 13),
    .MV .x10 .x26,
    .MV .x11 .x27,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 360)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 364)),
    .MV .x26 .x10,
    .SUB .x23 .x10 .x12,
    .MV .x24 .x12,
    .JAL .x0 (-32 : BitVec 21),
    .MV .x10 .x23,
    .MV .x11 .x24,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_change_values + 392)),
    .BNE .x12 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 396)),
    .MV .x25 .x11,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 404)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 408)),
    .MV .x11 .x25,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_change_values + 416)),
    .BNE .x11 .x0 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 420)),
    .SUB .x6 .x10 .x12,
    .MV .x29 .x12,
    .LI .x30 (32 : Word),
    .BLTU .x30 .x29 (brOff (GuestAddrs.bal_storage_change_values + 544) (GuestAddrs.bal_storage_change_values + 436)),
    .AUIPC .x5 (laHi GuestAddrs.bscv_vptr (GuestAddrs.bal_storage_change_values + 440)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bscv_vptr (GuestAddrs.bal_storage_change_values + 440)),
    .LD .x31 .x5 (0 : BitVec 12),
    .SLLI .x5 .x21 (5 : BitVec 6),
    .ADD .x31 .x31 .x5,
    .MV .x5 .x31,
    .LI .x30 (32 : Word),
    .BEQ .x30 .x0 (20 : BitVec 13),
    .SB .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x30 .x30 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .LI .x30 (32 : Word),
    .SUB .x30 .x30 .x29,
    .ADD .x5 .x31 .x30,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x6 (0 : BitVec 12),
    .SB .x5 .x30 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.bal_storage_change_values + 148) (GuestAddrs.bal_storage_change_values + 532)),
    .MV .x10 .x21,
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (128 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `balStorageChangeValues_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def balStorageChangeValues_relocs : RelocTable :=
  [ (17, .la .x5 "bscv_vptr"),
    (22, .jal .x1 "rlp_walk_init"),
    (25, .jal .x1 "rlp_walk_next"),
    (28, .jal .x1 "rlp_walk_next"),
    (32, .jal .x1 "rlp_walk_init"),
    (40, .jal .x1 "rlp_walk_next"),
    (47, .jal .x1 "rlp_walk_init"),
    (50, .jal .x1 "rlp_walk_next"),
    (78, .jal .x1 "rlp_walk_next"),
    (82, .jal .x1 "rlp_walk_init"),
    (90, .jal .x1 "rlp_walk_next"),
    (98, .jal .x1 "rlp_walk_init"),
    (101, .jal .x1 "rlp_walk_next"),
    (104, .jal .x1 "rlp_walk_next"),
    (110, .la .x5 "bscv_vptr") ]

def balStorageChangeValuesFunction : String :=
  "bal_storage_change_values:\n" ++ emitProgramR balStorageChangeValues_prog balStorageChangeValues_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `balStorageChangeValues_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem balStorageChangeValuesFunction_eq_prog :
    balStorageChangeValuesFunction = "bal_storage_change_values:\n" ++ emitProgramR balStorageChangeValues_prog balStorageChangeValues_relocs := rfl

#guard balStorageChangeValuesFunction.startsWith "bal_storage_change_values:\n"
#guard balStorageChangeValues_prog.length = 152
/-- Scratch data for `bal_storage_change_values`. -/
def balStorageChangeValuesData : String :=
  ".balign 8\n" ++
  "bscv_vptr:\n  .zero 8\n"

/-- `zisk_bal_storage_change_values`: probe over a hand-encoded AccountChanges
    with two storage_changes entries:
      slot 0x07 -> [[0, 0x11], [1, 0x22]]   (post value = 0x22, last tuple)
      slot 0x09 -> [[0, 0x33]]              (post value = 0x33)
    Output: +0 count (2); +8 key0[31] (0x07); +16 val0[31] (0x22 = last);
            +24 key1[31] (0x09); +32 val1[31] (0x33). -/
def ziskBalStorageChangeValuesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Build AccountChanges RLP at bscv_acct. storage_changes (item 1) =
  --   [ [07, [[80(=0),11],[01,22]]], [09, [[80,33]]] ]
  -- Encoded inner-first below; we hand-assemble the bytes.
  --   tuple [80,11] = c2 80 11 ; [01,22] = c2 01 22
  --   value_list0 [c2 80 11, c2 01 22] = c6 c2 80 11 c2 01 22
  --   entry0 [07, value_list0] = c8 07 c6 c2 80 11 c2 01 22
  --   tuple [80,33] = c2 80 33 ; value_list1 [c2 80 33] = c3 c2 80 33
  --   entry1 [09, value_list1] = c5 09 c3 c2 80 33
  --   storage_changes = [entry0, entry1] = d0 <entry0(9)> <entry1(6)>  (len 15 -> 0xcf? 9+6=15 -> 0xcf)
  --   actually 0xc0+15 = 0xcf
  --   account = [addr(94+20), storage_changes, c0, c0, c0, c0]
  -- We only need item 1 (storage_changes) parsed; build a minimal account.
  "  la t0, bscv_sc\n" ++
  -- storage_changes list: cf | c8 07 c6 c2 80 11 c2 01 22 | c5 09 c3 c2 80 33
  "  li t1, 0xcf; sb t1, 0(t0)\n" ++
  "  li t1, 0xc8; sb t1, 1(t0); li t1, 0x07; sb t1, 2(t0); li t1, 0xc6; sb t1, 3(t0)\n" ++
  "  li t1, 0xc2; sb t1, 4(t0); li t1, 0x80; sb t1, 5(t0); li t1, 0x11; sb t1, 6(t0)\n" ++
  "  li t1, 0xc2; sb t1, 7(t0); li t1, 0x01; sb t1, 8(t0); li t1, 0x22; sb t1, 9(t0)\n" ++
  "  li t1, 0xc5; sb t1, 10(t0); li t1, 0x09; sb t1, 11(t0); li t1, 0xc3; sb t1, 12(t0)\n" ++
  "  li t1, 0xc2; sb t1, 13(t0); li t1, 0x80; sb t1, 14(t0); li t1, 0x33; sb t1, 15(t0)\n" ++
  -- account = [ <20-byte addr>, storage_changes, c0, c0, c0, c0 ].
  -- addr header 0x94 + 20 zero bytes = 21 bytes; storage_changes = 16 bytes;
  -- four empty lists c0 = 4 bytes; payload = 21+16+4 = 41 (0x29). header f8 29.
  "  la t0, bscv_acct\n" ++
  "  li t1, 0xf8; sb t1, 0(t0); li t1, 0x29; sb t1, 1(t0)\n" ++
  "  li t1, 0x94; sb t1, 2(t0)\n" ++
  "  li t2, 20; addi t3, t0, 3\n" ++
  ".Lbscv_addr0:\n  beqz t2, .Lbscv_addr0d\n  sb zero, 0(t3); addi t3, t3, 1; addi t2, t2, -1; j .Lbscv_addr0\n" ++
  ".Lbscv_addr0d:\n" ++
  -- copy the 16-byte storage_changes blob to bscv_acct+23.
  "  la t1, bscv_sc; addi t2, t0, 23; li t3, 16; li t4, 0\n" ++
  ".Lbscv_sccopy:\n  beq t4, t3, .Lbscv_sccopyd\n  add t5, t1, t4; lbu t6, 0(t5); add t5, t2, t4; sb t6, 0(t5); addi t4, t4, 1; j .Lbscv_sccopy\n" ++
  ".Lbscv_sccopyd:\n" ++
  -- four empty lists 0xc0 at +39..+42.
  "  li t1, 0xc0; sb t1, 39(t0); sb t1, 40(t0); sb t1, 41(t0); sb t1, 42(t0)\n" ++
  "  la a0, bscv_acct; li a1, 43; la a2, bscv_okeys; la a3, bscv_ovals\n" ++
  "  jal ra, bal_storage_change_values\n" ++
  "  sd a0, 0(s0)\n" ++                                  -- count (expect 2)
  "  la t0, bscv_okeys; lbu t1, 31(t0); sd t1, 8(s0)\n" ++   -- key0[31] (0x07)
  "  la t0, bscv_ovals; lbu t1, 31(t0); sd t1, 16(s0)\n" ++  -- val0[31] (0x22)
  "  la t0, bscv_okeys; lbu t1, 63(t0); sd t1, 24(s0)\n" ++  -- key1[31] (0x09)
  "  la t0, bscv_ovals; lbu t1, 63(t0); sd t1, 32(s0)\n" ++  -- val1[31] (0x33)
  "  j .Lbscv_probe_done\n" ++
  balStorageChangeValuesFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lbscv_probe_done:"

def ziskBalStorageChangeValuesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bscv_sc:\n  .zero 64\n" ++
  "bscv_acct:\n  .zero 128\n" ++
  "bscv_okeys:\n  .zero 256\n" ++
  "bscv_ovals:\n  .zero 256\n" ++
  balStorageChangeValuesData


end EvmAsm.Codegen
