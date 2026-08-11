/-
  EvmAsm.Codegen.Programs.RlpFieldToU64StrictProgram

  Canonical-strict K34 wrapper program and its symbolic relocation table.
  Kept separate from the historical transaction helper slab so the hard
  Codegen/Programs file-size cap does not force either implementation to lose
  its explanatory comments.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Canonical-strict K34 wrapper. It preserves the original 32-byte ABI frame
    and `rfu_offset`/`rfu_length` scratch footprint, but delegates list
    selection and scalar decoding to their verified strict implementations.
    Both callees use the guest-linked symbolic relocation table. -/
def rlpFieldToU64StrictWrapper_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x13,
    .SD .x9 .x0 (0 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64_strict + 28)),
    .ADDI .x13 .x13 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64_strict + 28)),
    .AUIPC .x14 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64_strict + 36)),
    .ADDI .x14 .x14 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64_strict + 36)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item
      (GuestAddrs.rlp_field_to_u64_strict + 44)),
    .BNE .x10 .x0 (brOff (GuestAddrs.rlp_field_to_u64_strict + 116) (GuestAddrs.rlp_field_to_u64_strict + 48)),
    .AUIPC .x5 (laHi GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64_strict + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_offset (GuestAddrs.rlp_field_to_u64_strict + 52)),
    .LD .x10 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64_strict + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.rfu_length (GuestAddrs.rlp_field_to_u64_strict + 68)),
    .LD .x11 .x5 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict
      (GuestAddrs.rlp_field_to_u64_strict + 80)),
    .BNE .x11 .x0 (16 : BitVec 13),
    .SD .x9 .x10 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x5 (2 : Word),
    .BEQ .x11 .x5 (20 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def rlpFieldToU64Strict_prog : Program :=
  rlpFieldToU64StrictWrapper_prog

#guard rlpFieldToU64StrictWrapper_prog.length = 37
#guard rlpFieldToU64Strict_prog.length = 37

/-- Reloc side-table for the strict K34 wrapper. -/
def rlpFieldToU64Strict_relocs : RelocTable :=
  [ (7, .la .x13 "rfu_offset"),
    (9, .la .x14 "rfu_length"),
    (11, .jal .x1 "rlp_list_nth_item"),
    (13, .la .x5 "rfu_offset"),
    (17, .la .x5 "rfu_length"),
    (20, .jal .x1 "rlp_content_to_u64_strict") ]

/-- Canonical-strict K34 label for typed scalar callers. -/
def rlpFieldToU64StrictFunction : String :=
  "rlp_field_to_u64_strict:\n" ++
    emitProgramR rlpFieldToU64Strict_prog rlpFieldToU64Strict_relocs

theorem rlpFieldToU64StrictFunction_eq_prog :
    rlpFieldToU64StrictFunction =
      "rlp_field_to_u64_strict:\n" ++
        emitProgramR rlpFieldToU64Strict_prog rlpFieldToU64Strict_relocs := rfl

#guard rlpFieldToU64StrictFunction.startsWith "rlp_field_to_u64_strict:\n"

end EvmAsm.Codegen
