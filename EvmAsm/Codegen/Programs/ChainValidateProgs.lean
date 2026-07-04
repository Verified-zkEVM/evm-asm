/-
  EvmAsm.Codegen.Programs.ChainValidateProgs

  chain_validate_increasing_timestamps (PR-K229), split out of
  ChainValidate.lean to keep that file within the 1500-line size cap.
  Hosts the FULL generated conversion block (verification-view `Program`,
  reloc side-table, the `*Function` string def, its `rfl` drift theorem and
  `#guard` pins) so the `check-asm-to-program` verbatim source-drift guard
  finds it in one file; the MANIFEST row points here. ChainValidate.lean
  imports this module for the probe prologues.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_validate_increasing_timestamps -- PR-K229

    Verify that an N-element header chain has strictly
    increasing `timestamp` fields: `headers[i+1].timestamp >
    headers[i].timestamp` for every adjacent pair. Pure
    timestamp-only check; no parent_hash / number / gas_limit
    invariants. The K174 pair check enforces this as part of
    the four-invariant bundle -- K229 is the tight standalone.

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
        2 : timestamp field > 8 bytes BE on some header -/
def chainValidateIncreasingTimestamps_prog : Program :=
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
    .BLTU .x8 .x5 (260 : BitVec 13),
    .LD .x11 .x9 (0 : BitVec 12),
    .MV .x10 .x18,
    .LI .x12 (11 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 84)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 84)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.chain_validate_increasing_timestamps + 92)),
    .BNE .x10 .x0 (212 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 100)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 100)),
    .LD .x21 .x5 (0 : BitVec 12),
    .LD .x5 .x9 (0 : BitVec 12),
    .ADD .x6 .x18 .x5,
    .LI .x7 (1 : Word),
    .BEQ .x7 .x8 (204 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_child (GuestAddrs.chain_validate_increasing_timestamps + 128)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_child (GuestAddrs.chain_validate_increasing_timestamps + 128)),
    .SD .x5 .x6 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 140)),
    .SD .x5 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_prev (GuestAddrs.chain_validate_increasing_timestamps + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_prev (GuestAddrs.chain_validate_increasing_timestamps + 152)),
    .SD .x5 .x21 (0 : BitVec 12),
    .SLLI .x28 .x7 (3 : BitVec 6),
    .ADD .x28 .x9 .x28,
    .LD .x11 .x28 (0 : BitVec 12),
    .MV .x10 .x6,
    .LI .x12 (11 : Word),
    .AUIPC .x13 (laHi GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 184)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 184)),
    .JAL .x1 (jalOff GuestAddrs.rlp_field_to_u64 (GuestAddrs.chain_validate_increasing_timestamps + 192)),
    .BNE .x10 .x0 (112 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_ts (GuestAddrs.chain_validate_increasing_timestamps + 200)),
    .LD .x28 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_prev (GuestAddrs.chain_validate_increasing_timestamps + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_prev (GuestAddrs.chain_validate_increasing_timestamps + 212)),
    .LD .x29 .x5 (0 : BitVec 12),
    .BGEU .x29 .x28 (56 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_child (GuestAddrs.chain_validate_increasing_timestamps + 228)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_child (GuestAddrs.chain_validate_increasing_timestamps + 228)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 240)),
    .LD .x7 .x5 (0 : BitVec 12),
    .MV .x21 .x28,
    .SLLI .x30 .x7 (3 : BitVec 6),
    .ADD .x30 .x9 .x30,
    .LD .x31 .x30 (0 : BitVec 12),
    .ADD .x6 .x6 .x31,
    .ADDI .x7 .x7 (1 : BitVec 12),
    .JAL .x0 (-152 : BitVec 21),
    .SD .x19 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 284)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 284)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x20 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 308)),
    .ADDI .x5 .x5 (laLo GuestAddrs.cvit_iter_i (GuestAddrs.chain_validate_increasing_timestamps + 308)),
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

/-- Reloc side-table for `chainValidateIncreasingTimestamps_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainValidateIncreasingTimestamps_relocs : RelocTable :=
  [ (21, .la .x13 "cvit_ts"),
    (23, .jal .x1 "rlp_field_to_u64"),
    (25, .la .x5 "cvit_ts"),
    (32, .la .x5 "cvit_iter_child"),
    (35, .la .x5 "cvit_iter_i"),
    (38, .la .x5 "cvit_iter_prev"),
    (46, .la .x13 "cvit_ts"),
    (48, .jal .x1 "rlp_field_to_u64"),
    (50, .la .x5 "cvit_ts"),
    (53, .la .x5 "cvit_iter_prev"),
    (57, .la .x5 "cvit_iter_child"),
    (60, .la .x5 "cvit_iter_i"),
    (71, .la .x5 "cvit_iter_i"),
    (77, .la .x5 "cvit_iter_i") ]

def chainValidateIncreasingTimestampsFunction : String :=
  "chain_validate_increasing_timestamps:\n" ++ emitProgramR chainValidateIncreasingTimestamps_prog chainValidateIncreasingTimestamps_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainValidateIncreasingTimestamps_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainValidateIncreasingTimestampsFunction_eq_prog :
    chainValidateIncreasingTimestampsFunction = "chain_validate_increasing_timestamps:\n" ++ emitProgramR chainValidateIncreasingTimestamps_prog chainValidateIncreasingTimestamps_relocs := rfl

#guard chainValidateIncreasingTimestampsFunction.startsWith "chain_validate_increasing_timestamps:\n"
#guard chainValidateIncreasingTimestamps_prog.length = 92

end EvmAsm.Codegen
