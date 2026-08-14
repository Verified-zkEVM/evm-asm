import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.IntrinsicGas
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Successful EIP-7702 authorizations are charged at least the Amsterdam
    regular base cost of 7,816 gas each (`gas.py:141-147`).  The per-transaction
    regular budget is `TX_MAX_GAS_LIMIT - TX_BASE = 16,765,216`
    (`transactions.py:63`, `gas.py:131`), so this table must hold 2,144
    entries.  Keeping this as a named protocol formula prevents the former
    fixture-sized 1,060 cap from becoming a silent false reject. -/
def teerSuccessfulAuthCapacity : Nat := 2144

def repeatAsm : Nat -> String -> String
  | 0, _ => ""
  | n + 1, s => s ++ repeatAsm n s

def rlpWalkSkipAsm (failLabel : String) (n : Nat) (cursorReg endReg : String) : String :=
  repeatAsm n <| "  mv a0, " ++ cursorReg ++ "; mv a1, " ++ endReg ++
    "; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "; mv " ++ cursorReg ++ ", a0\n"

def rlpWalkFieldAsm (failLabel : String) (n : Nat) (cursorReg endReg ptrReg lenReg : String) : String :=
  rlpWalkSkipAsm failLabel n cursorReg endReg ++
  "  mv a0, " ++ cursorReg ++ "; mv a1, " ++ endReg ++
  "; jal ra, rlp_walk_next; bnez a1, " ++ failLabel ++ "\n" ++
  "  sub " ++ ptrReg ++ ", a0, a2; mv " ++ lenReg ++ ", a2\n"

def txIntrinsicStateGas_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tis_to_buf (GuestAddrs.tx_intrinsic_state_gas + 56)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tis_to_buf (GuestAddrs.tx_intrinsic_state_gas + 56)),
    .AUIPC .x13 (laHi GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 64)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 64)),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_to_address (GuestAddrs.tx_intrinsic_state_gas + 72)),
    .BNE .x10 .x0 (80 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tis_type (GuestAddrs.tx_intrinsic_state_gas + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tis_type (GuestAddrs.tx_intrinsic_state_gas + 88)),
    .AUIPC .x13 (laHi GuestAddrs.tis_inner_off (GuestAddrs.tx_intrinsic_state_gas + 96)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tis_inner_off (GuestAddrs.tx_intrinsic_state_gas + 96)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_intrinsic_state_gas + 104)),
    .BNE .x10 .x0 (60 : BitVec 13),
    .LI .x20 (0 : Word),
    .MV .x10 .x20,
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .AUIPC .x5 (laHi GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 132)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tis_is_creation (GuestAddrs.tx_intrinsic_state_gas + 132)),
    .LD .x14 .x5 (0 : BitVec 12),
    .MV .x15 .x18,
    .JAL .x1 (jalOff GuestAddrs.eip8037_tx_state_gas (GuestAddrs.tx_intrinsic_state_gas + 148)),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (1 : Word),
    .SD .x18 .x0 (0 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (2 : Word),
    .SD .x18 .x0 (0 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txIntrinsicStateGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txIntrinsicStateGas_relocs : RelocTable :=
  [ (14, .la .x12 "tis_to_buf"),
    (16, .la .x13 "tis_is_creation"),
    (18, .jal .x1 "tx_extract_to_address"),
    (22, .la .x12 "tis_type"),
    (24, .la .x13 "tis_inner_off"),
    (26, .jal .x1 "tx_type_dispatch"),
    (33, .la .x5 "tis_is_creation"),
    (37, .jal .x1 "eip8037_tx_state_gas") ]

def txIntrinsicStateGasFunction : String :=
  "tx_intrinsic_state_gas:\n" ++ emitProgramR txIntrinsicStateGas_prog txIntrinsicStateGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txIntrinsicStateGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txIntrinsicStateGasFunction_eq_prog :
    txIntrinsicStateGasFunction = "tx_intrinsic_state_gas:\n" ++ emitProgramR txIntrinsicStateGas_prog txIntrinsicStateGas_relocs := rfl

#guard txIntrinsicStateGasFunction.startsWith "tx_intrinsic_state_gas:\n"

def ziskTxIntrinsicStateGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)\n" ++ "  addi a0, a4, 16\n" ++
  "  li a2, 0xa0010008\n" ++ "  jal ra, tx_intrinsic_state_gas\n" ++
  "  li t0, 0xa0010000\n" ++ "  sd a0, 0(t0)\n" ++ "  j .Ltisg_pdone\n" ++
  txIntrinsicStateGasFunction ++ "\n" ++ txExtractToAddressFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++ rlpWalkHelpersClosure ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++ eip8037TxStateGasFunction ++ "\n" ++ ".Ltisg_pdone:"

def ziskTxIntrinsicStateGasDataSection : String :=
  ".section .data\n.balign 8\n" ++
  "tea_type:\n  .zero 8\ntea_inner_off:\n  .zero 8\ntea_field_off:\n  .zero 8\ntea_field_len:\n  .zero 8\n" ++
  "tis_to_buf:\n  .zero 32\ntis_is_creation:\n  .zero 8\ntis_type:\n  .zero 8\ntis_inner_off:\n  .zero 8\ntis_auth_count:\n  .zero 8"


end EvmAsm.Codegen
