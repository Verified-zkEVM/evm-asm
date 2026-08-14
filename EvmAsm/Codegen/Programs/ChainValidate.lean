/-
  EvmAsm.Codegen.Programs.ChainValidate

  Chain-level header validators (predicates returning a
  (valid, bad_index) pair) carved out of
  `EvmAsm.Codegen.Programs.Chain` per the file-size hard cap.
  Hosts:

    K229  chain_validate_increasing_timestamps
    K230  chain_validate_consecutive_numbers
    K240  chain_validate_gas_used_under_limit

  Compose K20 `rlp_list_nth_item` + K34 `rlp_field_to_u64_strict` from
  `RlpRead.lean` + `Tx.lean`. `ChainValidate.lean` imports both.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.ChainValidateProgs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

def ziskChainValidateIncreasingTimestampsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_increasing_timestamps\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvit_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateIncreasingTimestampsFunction ++ "\n" ++
  ".Lcvit_pdone:"

def ziskChainValidateIncreasingTimestampsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvit_ts:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_validate_consecutive_numbers -- PR-K230

    Verify the chain has strictly consecutive block numbers:
    `headers[i+1].number == headers[i].number + 1`. Pure
    number-only check; analogue of K229 for the `number` field
    (field 8) instead of `timestamp` (field 11), and with `==
    prev + 1` instead of `> prev`.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : number field > 8 bytes BE -/
def chainValidateConsecutiveNumbers_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .SD .x20 .x0 (0 : BitVec 12),
    .LI .x5 (2 : Word),
    .BLTU .x8 .x5 (264 : BitVec 13),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (8 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 84)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 84)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 92)),
    .BNE .x10 .x0 (216 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 100)),
    .LD .x21 .x5 (0 : BitVec 12),
    .LD .x5 .x9 (0 : BitVec 12),
    .ADD .x6 .x18 .x5,
    .LI .x7 (1 : Word),
    .BEQ .x7 .x8 (208 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_child (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_child (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 128)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 140)),
    .SD .x5 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_prev (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_prev (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 152)),
    .SD .x5 .x21 (0 : BitVec 12),
    .SLLI .x28 .x7 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x6,
    .LI .x12 (8 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 184)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 184)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 192)),
    .BNE .x10 .x0 (116 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_num (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 200)),
    .LD .x28 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_prev (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_prev (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 212)),
    .LD .x29 .x5 (0 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .BNE .x29 .x28 (56 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_child (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_child (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 232)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 244)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 244)),
    .LD .x7 .x5 (0 : BitVec 12),
    .MV .x21 .x28,
    .SLLI .x30 .x7 (3 : BitVec 6),
    .ADD .x30 .x9 .x30,
    .LD .x31 .x30 (0 : BitVec 12),
    .ADD .x6 .x6 .x31,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-156 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 288)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 312)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvcn_iter_i (ChainValidateOfflineAddrs.chain_validate_consecutive_numbers + 312)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x6 (0 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainValidateConsecutiveNumbers_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainValidateConsecutiveNumbers_relocs : RelocTable :=
  [ (21, .la .x13 "cvcn_num"),
    (23, .jal .x1 "rlp_field_to_u64_strict"),
    (25, .la .x5 "cvcn_num"),
    (32, .la .x5 "cvcn_iter_child"),
    (35, .la .x5 "cvcn_iter_i"),
    (38, .la .x5 "cvcn_iter_prev"),
    (46, .la .x13 "cvcn_num"),
    (48, .jal .x1 "rlp_field_to_u64_strict"),
    (50, .la .x5 "cvcn_num"),
    (53, .la .x5 "cvcn_iter_prev"),
    (58, .la .x5 "cvcn_iter_child"),
    (61, .la .x5 "cvcn_iter_i"),
    (72, .la .x5 "cvcn_iter_i"),
    (78, .la .x5 "cvcn_iter_i") ]

def chainValidateConsecutiveNumbersFunction : String :=
  "chain_validate_consecutive_numbers:\n" ++ emitProgramR chainValidateConsecutiveNumbers_prog chainValidateConsecutiveNumbers_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainValidateConsecutiveNumbers_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainValidateConsecutiveNumbersFunction_eq_prog :
    chainValidateConsecutiveNumbersFunction = "chain_validate_consecutive_numbers:\n" ++ emitProgramR chainValidateConsecutiveNumbers_prog chainValidateConsecutiveNumbers_relocs := rfl

#guard chainValidateConsecutiveNumbersFunction.startsWith "chain_validate_consecutive_numbers:\n"
#guard chainValidateConsecutiveNumbers_prog.length = 93
def ziskChainValidateConsecutiveNumbersPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_consecutive_numbers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvcn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateConsecutiveNumbersFunction ++ "\n" ++
  ".Lcvcn_pdone:"

def ziskChainValidateConsecutiveNumbersDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvcn_num:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_validate_gas_used_under_limit -- PR-K240

    Per-header invariant: `gas_used <= gas_limit` (header fields
    10 and 9 respectively). The block validator already enforces
    `gas_used <= gas_limit` in K72 `check_gas_limit` for adjacent
    pairs; K240 lifts the standalone per-block constraint to an
    N-element chain.

    Vacuous on empty chain: valid=1, bad_index=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (valid: 1 = all OK)
      a4 (input)  : u64 out (bad_index = first violator, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse fail on some header
        2 : gas_used or gas_limit field > 8 bytes BE -/
def chainValidateGasUsedUnderLimit_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .SD .x20 .x0 (0 : BitVec 12),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x8 (224 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_iter_ptr (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_iter_ptr (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 72)),
    .SD .x5 .x18 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_iter_i (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_iter_i (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 84)),
    .SD .x5 .x21 (0 : BitVec 12),
    .SLLI .x28 .x21 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (10 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvgul_gas_used (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvgul_gas_used (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 116)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 124)),
    .BNE .x10 .x0 (156 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_iter_ptr (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_iter_ptr (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 132)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_iter_i (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 144)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_iter_i (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 144)),
    .LD .x21 .x5 (0 : BitVec 12),
    .SLLI .x28 .x21 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (9 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvgul_gas_limit (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 176)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvgul_gas_limit (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 176)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64_strict (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 184)),
    .BNE .x10 .x0 (96 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_iter_ptr (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_iter_ptr (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 192)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_iter_i (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 204)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_iter_i (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 204)),
    .LD .x21 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_gas_used (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 216)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_gas_used (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 216)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvgul_gas_limit (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 228)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvgul_gas_limit (ChainValidateOfflineAddrs.chain_validate_gas_used_under_limit + 228)),
    .LD .x7 .x5 (0 : BitVec 12),
    .BLTU .x7 .x6 (28 : BitVec 13),
    .SLLI .x28 .x21 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x29 .x28 (0 : BitVec 12),
    .ADD .x18 .x18 .x29,
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-196 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x20 .x21 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .SD .x20 .x21 (0 : BitVec 12),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainValidateGasUsedUnderLimit_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainValidateGasUsedUnderLimit_relocs : RelocTable :=
  [ (18, .la .x5 "cvgul_iter_ptr"),
    (21, .la .x5 "cvgul_iter_i"),
    (29, .la .x13 "cvgul_gas_used"),
    (31, .jal .x1 "rlp_field_to_u64_strict"),
    (33, .la .x5 "cvgul_iter_ptr"),
    (36, .la .x5 "cvgul_iter_i"),
    (44, .la .x13 "cvgul_gas_limit"),
    (46, .jal .x1 "rlp_field_to_u64_strict"),
    (48, .la .x5 "cvgul_iter_ptr"),
    (51, .la .x5 "cvgul_iter_i"),
    (54, .la .x5 "cvgul_gas_used"),
    (57, .la .x5 "cvgul_gas_limit") ]

def chainValidateGasUsedUnderLimitFunction : String :=
  "chain_validate_gas_used_under_limit:\n" ++ emitProgramR chainValidateGasUsedUnderLimit_prog chainValidateGasUsedUnderLimit_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainValidateGasUsedUnderLimit_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainValidateGasUsedUnderLimitFunction_eq_prog :
    chainValidateGasUsedUnderLimitFunction = "chain_validate_gas_used_under_limit:\n" ++ emitProgramR chainValidateGasUsedUnderLimit_prog chainValidateGasUsedUnderLimit_relocs := rfl

#guard chainValidateGasUsedUnderLimitFunction.startsWith "chain_validate_gas_used_under_limit:\n"
#guard chainValidateGasUsedUnderLimit_prog.length = 83
def ziskChainValidateGasUsedUnderLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_gas_used_under_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvgul_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateGasUsedUnderLimitFunction ++ "\n" ++
  ".Lcvgul_pdone:"

def ziskChainValidateGasUsedUnderLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_used:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_limit:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_i:\n" ++
  "  .zero 8"


/-! ## chain_validate_no_blob_txs -- PR-K258

    Per-header invariant: every header has `blob_gas_used == 0`
    (field 17 either missing or RLP-empty). Useful for proving a
    chain segment contains no blob-carrying transactions —
    callers wanting to skip blob-fee market evolution use this
    as a short-circuit.

    Field 17 missing (pre-Cancun header) counts as
    blob_gas_used == 0; mixed pre- and post-Cancun chains pass
    as long as no Cancun header actually used blob gas.

    Vacuous on empty chain: valid=1, bad_index=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (valid: 1 = all blob_gas_used==0)
      a4 (input)  : u64 out (bad_index = first violator, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse fail on some header (post-Cancun shape error)
        2 : field 17 > 8 bytes BE -/
def chainValidateNoBlobTxsFunction : String :=
  "chain_validate_no_blob_txs:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvnbt_loop:\n" ++
  "  beq s5, s0, .Lcvnbt_done\n" ++
  "  la t0, cvnbt_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvnbt_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cvnbt_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  la t0, cvnbt_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvnbt_iter_i;   ld s5, 0(t0)\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcvnbt_no_field\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcvnbt_size_fail\n" ++
  "  la t0, cvnbt_field; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lcvnbt_violation\n" ++
  ".Lcvnbt_no_field:\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvnbt_loop\n" ++
  ".Lcvnbt_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvnbt_ret\n" ++
  ".Lcvnbt_size_fail:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 2\n" ++
  "  j .Lcvnbt_ret\n" ++
  ".Lcvnbt_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvnbt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateNoBlobTxsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_no_blob_txs\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvnbt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateNoBlobTxsFunction ++ "\n" ++
  ".Lcvnbt_pdone:"

def ziskChainValidateNoBlobTxsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvnbt_field:\n" ++
  "  .zero 8\n" ++
  "cvnbt_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvnbt_iter_i:\n" ++
  "  .zero 8"


/-! ## chain_validate_constant_gas_limit -- PR-K266

    Per-chain invariant: all headers share the same `gas_limit`
    (field 9). Useful as a sanity check for analytics windows
    over a stable-network segment; the EIP-1559 elastic-cap rule
    permits ±1/1024 drift per block, so this predicate flags any
    capacity change inside the window.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : gas_limit field > 8 bytes BE on some header -/
def chainValidateConstantGasLimitFunction : String :=
  "chain_validate_constant_gas_limit:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvcgl_done\n" ++
  "  # Extract headers[0].gas_limit into s5 (anchor)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 9\n" ++
  "  la a3, cvcgl_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvcgl_propagate\n" ++
  "  la t0, cvcgl_field; ld s5, 0(t0)\n" ++
  "  # Walk: child_ptr = headers[1]; i = 1\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvcgl_loop:\n" ++
  "  beq t2, s0, .Lcvcgl_done\n" ++
  "  la t0, cvcgl_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvcgl_iter_i;     sd t2, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 9\n" ++
  "  la a3, cvcgl_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvcgl_propagate\n" ++
  "  la t0, cvcgl_field; ld t3, 0(t0)\n" ++
  "  bne t3, s5, .Lcvcgl_pred_false\n" ++
  "  la t0, cvcgl_iter_child; ld t1, 0(t0)\n" ++
  "  la t0, cvcgl_iter_i;     ld t2, 0(t0)\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvcgl_loop\n" ++
  ".Lcvcgl_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvcgl_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvcgl_ret\n" ++
  ".Lcvcgl_propagate:\n" ++
  "  la t0, cvcgl_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvcgl_ret\n" ++
  ".Lcvcgl_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvcgl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateConstantGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_constant_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvcgl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateConstantGasLimitFunction ++ "\n" ++
  ".Lcvcgl_pdone:"

def ziskChainValidateConstantGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvcgl_field:\n" ++
  "  .zero 8\n" ++
  "cvcgl_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvcgl_iter_i:\n" ++
  "  .zero 8"


/-! ## chain_validate_basefee_non_decreasing -- PR-K267

    Per-pair invariant: `basefee[i] <= basefee[i+1]` for all
    `0 <= i < N-1` (header field 15, London+). Useful for
    spotting persistent fee-pressure windows (sustained block
    saturation) and as a building block for fee-market analytics.

    Mirrors K229 chain_validate_increasing_timestamps in shape;
    differs by field (15 vs 11) and predicate (<= vs <).

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index = i where bf[i-1] > bf[i])
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : basefee field > 8 bytes BE on some header -/
def chainValidateBasefeeNonDecreasingFunction : String :=
  "chain_validate_basefee_non_decreasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvbnd_done\n" ++
  "  # Extract headers[0].basefee into s5 (prev_bf)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 15\n" ++
  "  la a3, cvbnd_bf\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvbnd_propagate\n" ++
  "  la t0, cvbnd_bf; ld s5, 0(t0)\n" ++
  "  # child_ptr starts at headers[1]; i = 1\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvbnd_loop:\n" ++
  "  beq t2, s0, .Lcvbnd_done\n" ++
  "  la t0, cvbnd_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvbnd_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvbnd_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 15\n" ++
  "  la a3, cvbnd_bf\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvbnd_propagate\n" ++
  "  la t0, cvbnd_bf;         ld t3, 0(t0)\n" ++
  "  la t0, cvbnd_iter_prev;  ld t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lcvbnd_pred_false\n" ++
  "  la t0, cvbnd_iter_child; ld t1, 0(t0)\n" ++
  "  la t0, cvbnd_iter_i;     ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvbnd_loop\n" ++
  ".Lcvbnd_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvbnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvbnd_ret\n" ++
  ".Lcvbnd_propagate:\n" ++
  "  la t0, cvbnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvbnd_ret\n" ++
  ".Lcvbnd_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvbnd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateBasefeeNonDecreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_basefee_non_decreasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvbnd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateBasefeeNonDecreasingFunction ++ "\n" ++
  ".Lcvbnd_pdone:"

def ziskChainValidateBasefeeNonDecreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvbnd_bf:\n" ++
  "  .zero 8\n" ++
  "cvbnd_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvbnd_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvbnd_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_validate_basefee_non_increasing -- PR-K268

    Per-pair invariant: `basefee[i] >= basefee[i+1]` for all
    0 <= i < N-1 (header field 15, London+). Min-side mirror of
    K267 chain_validate_basefee_non_decreasing; useful for
    post-spike normalization windows (sustained under-target
    blocks).

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index = i where bf[i-1] < bf[i])
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : basefee field > 8 bytes BE on some header -/
def chainValidateBasefeeNonIncreasingFunction : String :=
  "chain_validate_basefee_non_increasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvbni_done\n" ++
  "  # Extract headers[0].basefee into s5 (prev_bf)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 15\n" ++
  "  la a3, cvbni_bf\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvbni_propagate\n" ++
  "  la t0, cvbni_bf; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvbni_loop:\n" ++
  "  beq t2, s0, .Lcvbni_done\n" ++
  "  la t0, cvbni_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvbni_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvbni_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 15\n" ++
  "  la a3, cvbni_bf\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvbni_propagate\n" ++
  "  la t0, cvbni_bf;         ld t3, 0(t0)\n" ++
  "  la t0, cvbni_iter_prev;  ld t4, 0(t0)\n" ++
  "  bltu t4, t3, .Lcvbni_pred_false\n" ++
  "  la t0, cvbni_iter_child; ld t1, 0(t0)\n" ++
  "  la t0, cvbni_iter_i;     ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvbni_loop\n" ++
  ".Lcvbni_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvbni_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvbni_ret\n" ++
  ".Lcvbni_propagate:\n" ++
  "  la t0, cvbni_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvbni_ret\n" ++
  ".Lcvbni_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvbni_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateBasefeeNonIncreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_basefee_non_increasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvbni_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateBasefeeNonIncreasingFunction ++ "\n" ++
  ".Lcvbni_pdone:"

def ziskChainValidateBasefeeNonIncreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvbni_bf:\n" ++
  "  .zero 8\n" ++
  "cvbni_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvbni_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvbni_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_validate_gas_limit_non_decreasing -- PR-K269

    Per-pair invariant: `gas_limit[i] <= gas_limit[i+1]` for all
    0 <= i < N-1 (header field 9). Useful for spotting
    capacity-expansion windows; gas_limit counterpart to K267
    chain_validate_basefee_non_decreasing.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : gas_limit field > 8 bytes BE on some header -/
def chainValidateGasLimitNonDecreasingFunction : String :=
  "chain_validate_gas_limit_non_decreasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvglnd_done\n" ++
  "  # Extract headers[0].gas_limit into s5 (prev)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 9\n" ++
  "  la a3, cvglnd_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvglnd_propagate\n" ++
  "  la t0, cvglnd_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvglnd_loop:\n" ++
  "  beq t2, s0, .Lcvglnd_done\n" ++
  "  la t0, cvglnd_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvglnd_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvglnd_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 9\n" ++
  "  la a3, cvglnd_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvglnd_propagate\n" ++
  "  la t0, cvglnd_field;        ld t3, 0(t0)\n" ++
  "  la t0, cvglnd_iter_prev;    ld t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lcvglnd_pred_false\n" ++
  "  la t0, cvglnd_iter_child;   ld t1, 0(t0)\n" ++
  "  la t0, cvglnd_iter_i;       ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvglnd_loop\n" ++
  ".Lcvglnd_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvglnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvglnd_ret\n" ++
  ".Lcvglnd_propagate:\n" ++
  "  la t0, cvglnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvglnd_ret\n" ++
  ".Lcvglnd_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvglnd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateGasLimitNonDecreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_gas_limit_non_decreasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvglnd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateGasLimitNonDecreasingFunction ++ "\n" ++
  ".Lcvglnd_pdone:"

def ziskChainValidateGasLimitNonDecreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvglnd_field:\n" ++
  "  .zero 8\n" ++
  "cvglnd_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvglnd_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvglnd_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_validate_gas_limit_non_increasing -- PR-K270

    Per-pair invariant: `gas_limit[i] >= gas_limit[i+1]` for all
    0 <= i < N-1 (header field 9). Min-side mirror of K269
    chain_validate_gas_limit_non_decreasing; useful for spotting
    capacity-contraction windows.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : gas_limit field > 8 bytes BE on some header -/
def chainValidateGasLimitNonIncreasingFunction : String :=
  "chain_validate_gas_limit_non_increasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvglni_done\n" ++
  "  # Extract headers[0].gas_limit into s5 (prev)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 9\n" ++
  "  la a3, cvglni_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvglni_propagate\n" ++
  "  la t0, cvglni_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvglni_loop:\n" ++
  "  beq t2, s0, .Lcvglni_done\n" ++
  "  la t0, cvglni_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvglni_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvglni_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 9\n" ++
  "  la a3, cvglni_field\n" ++
  "  jal ra, rlp_field_to_u64_strict\n" ++
  "  bnez a0, .Lcvglni_propagate\n" ++
  "  la t0, cvglni_field;        ld t3, 0(t0)\n" ++
  "  la t0, cvglni_iter_prev;    ld t4, 0(t0)\n" ++
  "  bltu t4, t3, .Lcvglni_pred_false\n" ++
  "  la t0, cvglni_iter_child;   ld t1, 0(t0)\n" ++
  "  la t0, cvglni_iter_i;       ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvglni_loop\n" ++
  ".Lcvglni_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvglni_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvglni_ret\n" ++
  ".Lcvglni_propagate:\n" ++
  "  la t0, cvglni_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvglni_ret\n" ++
  ".Lcvglni_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvglni_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateGasLimitNonIncreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_gas_limit_non_increasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvglni_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpFieldToU64StrictFunction ++ "\n" ++
  chainValidateGasLimitNonIncreasingFunction ++ "\n" ++
  ".Lcvglni_pdone:"

def ziskChainValidateGasLimitNonIncreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvglni_field:\n" ++
  "  .zero 8\n" ++
  "cvglni_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvglni_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvglni_iter_prev:\n" ++
  "  .zero 8"


/-! ## chain_validate_extra_data_length -- PR-K291

    Per-header invariant: `len(extra_data) <= 32` (field 12).
    The yellow paper / EIP-3675 cap the `extraData` field at 32
    bytes for all post-Homestead headers (mainnet protocol
    constraint). Useful as a per-block sanity check on
    RLP-decoded headers.

    Vacuous-true on N = 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header -/
def chainValidateExtraDataLength_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (0 : BitVec 12),
    .SD .x20 .x0 (0 : BitVec 12),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x8 (168 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvedl_iter_ptr (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvedl_iter_ptr (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 72)),
    .SD .x5 .x18 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvedl_iter_i (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvedl_iter_i (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 84)),
    .SD .x5 .x21 (0 : BitVec 12),
    .SLLI .x28 .x21 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (12 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvedl_offset (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvedl_offset (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 116)),
    .AUIPC .x14 (laHi GuestAddrs.cvedl_length (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 124)),
    .ADDI .x14 .x14 (laLo GuestAddrs.cvedl_length (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 124)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 132)),
    .BNE .x10 .x0 (88 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvedl_iter_ptr (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvedl_iter_ptr (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 140)),
    .LD .x18 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvedl_iter_i (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvedl_iter_i (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 152)),
    .LD .x21 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvedl_length (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 164)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvedl_length (ChainValidateOfflineAddrs.chain_validate_extra_data_length + 164)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BLTU .x7 .x6 (28 : BitVec 13),
    .SLLI .x28 .x21 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x29 .x28 (0 : BitVec 12),
    .ADD .x18 .x18 .x29,
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (-136 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x20 .x21 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (20 : BitVec 21),
    .SD .x20 .x21 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainValidateExtraDataLength_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainValidateExtraDataLength_relocs : RelocTable :=
  [ (18, .la .x5 "cvedl_iter_ptr"),
    (21, .la .x5 "cvedl_iter_i"),
    (29, .la .x13 "cvedl_offset"),
    (31, .la .x14 "cvedl_length"),
    (33, .jal .x1 "rlp_list_nth_item"),
    (35, .la .x5 "cvedl_iter_ptr"),
    (38, .la .x5 "cvedl_iter_i"),
    (41, .la .x5 "cvedl_length") ]

def chainValidateExtraDataLengthFunction : String :=
  "chain_validate_extra_data_length:\n" ++ emitProgramR chainValidateExtraDataLength_prog chainValidateExtraDataLength_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainValidateExtraDataLength_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainValidateExtraDataLengthFunction_eq_prog :
    chainValidateExtraDataLengthFunction = "chain_validate_extra_data_length:\n" ++ emitProgramR chainValidateExtraDataLength_prog chainValidateExtraDataLength_relocs := rfl

#guard chainValidateExtraDataLengthFunction.startsWith "chain_validate_extra_data_length:\n"
#guard chainValidateExtraDataLength_prog.length = 69
def ziskChainValidateExtraDataLengthPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_extra_data_length\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvedl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  chainValidateExtraDataLengthFunction ++ "\n" ++
  ".Lcvedl_pdone:"

def ziskChainValidateExtraDataLengthDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "cvedl_offset:\n" ++
  "  .zero 8\n" ++
  "cvedl_length:\n" ++
  "  .zero 8\n" ++
  "cvedl_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvedl_iter_i:\n" ++
  "  .zero 8"


end EvmAsm.Codegen
