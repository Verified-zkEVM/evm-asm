/-
  EvmAsm.Codegen.Programs.SszWithdrawal

  ssz_withdrawal_to_rlp (bead evm-asm-fhsxz.2.4.2.1): bridge an SSZ Withdrawal
  to the withdrawal RLP that the Step-2 recompute consumes. The guest's
  ExecutionPayload carries withdrawals as fixed-size SSZ containers
    Withdrawal { index: uint64, validator_index: uint64,
                 address: Bytes20, amount: uint64 }   -- 44 bytes
  but `withdrawals_state_root` (via `withdrawal_decode`) consumes withdrawal
  RLP `rlp([index, validator_index, address, amount])`. This is the missing
  glue for wiring the verdict (.2.4.2) to the real SSZ guest input.

  Independent of the MPT engine — composes only the RLP encoders on main. u64
  fields are read byte-wise (LE) and reversed to big-endian (no-misaligned
  invariant: amount sits at offset 36 ≡ 4 mod 8), then encoded minimal via
  rlp_encode_uint_be; the address goes through rlp_encode_bytes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## swr_rev_le_be -- reverse `len` little-endian bytes to big-endian
    (local copy; a0 = src, a1 = len, a2 = dst; leaf). -/
def swrRevLeBe_prog : Program :=
  [ .ADD .x5 .x10 .x11,
    .MV .x6 .x12,
    .MV .x7 .x11,
    .BEQ .x7 .x0 (28 : BitVec 13),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .LBU .x28 .x5 (0 : BitVec 12),
    .SB .x6 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def swrRevLeBeFunction : String :=
  "swr_rev_le_be:\n" ++ emitProgram swrRevLeBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `swrRevLeBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem swrRevLeBeFunction_eq_prog :
    swrRevLeBeFunction = "swr_rev_le_be:\n" ++ emitProgram swrRevLeBe_prog := rfl

#guard swrRevLeBeFunction.startsWith "swr_rev_le_be:\n"
#guard swrRevLeBe_prog.length = 11
/-- `ssz_withdrawal_to_rlp`.
    a0 = SSZ Withdrawal ptr (44 bytes), a1 = out RLP buffer ptr,
    a2 = u64 out length ptr.  a0 (output) = 0. -/
def sszWithdrawalToRlp_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x19 (0 : Word),
    .ADDI .x10 .x8 (0 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 48)),
    .JAL .x1 (jalOff GuestAddrs.swr_rev_le_be (GuestAddrs.ssz_withdrawal_to_rlp + 56)),
    .AUIPC .x10 (laHi GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 60)),
    .ADDI .x10 .x10 (laLo GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 60)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 72)),
    .ADD .x12 .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.ssz_withdrawal_to_rlp + 84)),
    .ADD .x19 .x19 .x10,
    .ADDI .x10 .x8 (8 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 100)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 100)),
    .JAL .x1 (jalOff GuestAddrs.swr_rev_le_be (GuestAddrs.ssz_withdrawal_to_rlp + 108)),
    .AUIPC .x10 (laHi GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 112)),
    .ADDI .x10 .x10 (laLo GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 112)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 124)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 124)),
    .ADD .x12 .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.ssz_withdrawal_to_rlp + 136)),
    .ADD .x19 .x19 .x10,
    .ADDI .x10 .x8 (16 : BitVec 12),
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 152)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 152)),
    .ADD .x12 .x12 .x19,
    .AUIPC .x13 (laHi GuestAddrs.swr_flen (GuestAddrs.ssz_withdrawal_to_rlp + 164)),
    .ADDI .x13 .x13 (laLo GuestAddrs.swr_flen (GuestAddrs.ssz_withdrawal_to_rlp + 164)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_bytes (GuestAddrs.ssz_withdrawal_to_rlp + 172)),
    .AUIPC .x5 (laHi GuestAddrs.swr_flen (GuestAddrs.ssz_withdrawal_to_rlp + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.swr_flen (GuestAddrs.ssz_withdrawal_to_rlp + 176)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x19 .x19 .x6,
    .ADDI .x10 .x8 (36 : BitVec 12),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 200)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 200)),
    .JAL .x1 (jalOff GuestAddrs.swr_rev_le_be (GuestAddrs.ssz_withdrawal_to_rlp + 208)),
    .AUIPC .x10 (laHi GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 212)),
    .ADDI .x10 .x10 (laLo GuestAddrs.swr_be (GuestAddrs.ssz_withdrawal_to_rlp + 212)),
    .LI .x11 (8 : Word),
    .AUIPC .x12 (laHi GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 224)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 224)),
    .ADD .x12 .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_uint_be (GuestAddrs.ssz_withdrawal_to_rlp + 236)),
    .ADD .x19 .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.swr_prefix_len (GuestAddrs.ssz_withdrawal_to_rlp + 252)),
    .ADDI .x12 .x12 (laLo GuestAddrs.swr_prefix_len (GuestAddrs.ssz_withdrawal_to_rlp + 252)),
    .JAL .x1 (jalOff GuestAddrs.rlp_encode_list_prefix (GuestAddrs.ssz_withdrawal_to_rlp + 260)),
    .AUIPC .x5 (laHi GuestAddrs.swr_prefix_len (GuestAddrs.ssz_withdrawal_to_rlp + 264)),
    .ADDI .x5 .x5 (laLo GuestAddrs.swr_prefix_len (GuestAddrs.ssz_withdrawal_to_rlp + 264)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADD .x7 .x9 .x6,
    .AUIPC .x28 (laHi GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 280)),
    .ADDI .x28 .x28 (laLo GuestAddrs.swr_payload (GuestAddrs.ssz_withdrawal_to_rlp + 280)),
    .MV .x29 .x19,
    .BEQ .x29 .x0 (28 : BitVec 13),
    .LBU .x30 .x28 (0 : BitVec 12),
    .SB .x7 .x30 (0 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADD .x6 .x6 .x19,
    .SD .x18 .x6 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `sszWithdrawalToRlp_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def sszWithdrawalToRlp_relocs : RelocTable :=
  [ (12, .la .x12 "swr_be"),
    (14, .jal .x1 "swr_rev_le_be"),
    (15, .la .x10 "swr_be"),
    (18, .la .x12 "swr_payload"),
    (21, .jal .x1 "rlp_encode_uint_be"),
    (25, .la .x12 "swr_be"),
    (27, .jal .x1 "swr_rev_le_be"),
    (28, .la .x10 "swr_be"),
    (31, .la .x12 "swr_payload"),
    (34, .jal .x1 "rlp_encode_uint_be"),
    (38, .la .x12 "swr_payload"),
    (41, .la .x13 "swr_flen"),
    (43, .jal .x1 "rlp_encode_bytes"),
    (44, .la .x5 "swr_flen"),
    (50, .la .x12 "swr_be"),
    (52, .jal .x1 "swr_rev_le_be"),
    (53, .la .x10 "swr_be"),
    (56, .la .x12 "swr_payload"),
    (59, .jal .x1 "rlp_encode_uint_be"),
    (63, .la .x12 "swr_prefix_len"),
    (65, .jal .x1 "rlp_encode_list_prefix"),
    (66, .la .x5 "swr_prefix_len"),
    (70, .la .x28 "swr_payload") ]

def sszWithdrawalToRlpFunction : String :=
  "ssz_withdrawal_to_rlp:\n" ++ emitProgramR sszWithdrawalToRlp_prog sszWithdrawalToRlp_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `sszWithdrawalToRlp_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem sszWithdrawalToRlpFunction_eq_prog :
    sszWithdrawalToRlpFunction = "ssz_withdrawal_to_rlp:\n" ++ emitProgramR sszWithdrawalToRlp_prog sszWithdrawalToRlp_relocs := rfl

#guard sszWithdrawalToRlpFunction.startsWith "ssz_withdrawal_to_rlp:\n"
#guard sszWithdrawalToRlp_prog.length = 90
/-- `zisk_ssz_withdrawal_to_rlp`: probe.
    Input: bytes 8.. = the 44-byte SSZ Withdrawal.
    Output: OUTPUT+0 = RLP length (u64); OUTPUT+8 = withdrawal RLP bytes. -/
def ziskSszWithdrawalToRlpPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 8              # SSZ withdrawal ptr\n" ++
  "  li a1, 0xa0010008           # out at OUTPUT+8\n" ++
  "  li a2, 0xa0010000           # out_len at OUTPUT+0\n" ++
  "  jal ra, ssz_withdrawal_to_rlp\n" ++
  "  j .Lswr_pdone\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  swrRevLeBeFunction ++ "\n" ++
  sszWithdrawalToRlpFunction ++ "\n" ++
  ".Lswr_pdone:"

def ziskSszWithdrawalToRlpDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "swr_flen:\n  .zero 8\n" ++
  "swr_prefix_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "swr_be:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "swr_payload:\n  .zero 128"

def ziskSszWithdrawalToRlpProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSszWithdrawalToRlpPrologue
  dataAsm     := ziskSszWithdrawalToRlpDataSection
}

/-! ## bv_sum_withdrawals_to_address -- EIP-4895 withdrawal credit to an address.

    Sum the wei credited by all SSZ withdrawals whose 20-byte address equals a
    target address. Mirrors execution-specs apply_withdrawals: each withdrawal
    credits `amount (Gwei) * 1e9` wei to its address. Used to make the
    coinbase/recipient post-balance checks withdrawal-aware on EIP-7928/4895
    withdrawal blocks (see bead evm-asm-uyu11.1), so the strict
    `post == pre + fee/value (+ withdrawal credit)` check stays sound instead of
    being skipped.

    SSZ Withdrawal layout (44 bytes): index u64 @0, validator_index u64 @8,
    address 20 B @16, amount u64 LE (Gwei) @36.

    Calling convention:
      a0 (input)  : target address ptr (20 bytes)
      a1 (input)  : SSZ withdrawals base ptr (44 bytes per entry)
      a2 (input)  : withdrawal count
      a3 (input)  : output u256 ptr (32 bytes, BE; receives the summed wei)
      ra (input)  : return
      a0 (output) : 0 ok, 1 on u256 overflow (mul or add) -/
def bvSumWithdrawalsToAddressFunction : String :=
  "bv_sum_withdrawals_to_address:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # target address ptr (20B)\n" ++
  "  mv s1, a1                   # SSZ withdrawals base\n" ++
  "  mv s2, a2                   # withdrawal count\n" ++
  "  mv s3, a3                   # out u256 BE\n" ++
  "  sd zero, 0(s3); sd zero, 8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  li s4, 0                    # i\n" ++
  ".Lbsw_loop:\n" ++
  "  beq s4, s2, .Lbsw_ok\n" ++
  "  li t0, 44; mul t0, s4, t0; add t1, s1, t0   # entry ptr\n" ++
  "  addi t2, t1, 16             # entry address @ +16\n" ++
  "  mv t3, s0; li t4, 20\n" ++
  ".Lbsw_addr_cmp:\n" ++
  "  beqz t4, .Lbsw_match\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lbsw_next\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1\n" ++
  "  j .Lbsw_addr_cmp\n" ++
  ".Lbsw_match:\n" ++
  "  li t0, 44; mul t0, s4, t0; add t1, s1, t0   # re-derive entry ptr\n" ++
  "  la t2, bsw_amount\n" ++
  "  sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2)\n" ++
  "  addi a0, t1, 36; li a1, 8; la a2, bsw_amount; addi a2, a2, 24\n" ++
  "  jal ra, swr_rev_le_be       # amount_gwei LE@36 -> BE in low 8 bytes\n" ++
  "  la a0, bsw_amount; li a1, 1000000000; la a2, bsw_wei\n" ++
  "  jal ra, u256_mul_u64_be     # wei = amount_gwei * 1e9\n" ++
  "  bnez a0, .Lbsw_overflow\n" ++
  "  mv a0, s3; la a1, bsw_wei; mv a2, s3\n" ++
  "  jal ra, u256_add_be         # acc += wei\n" ++
  "  bnez a0, .Lbsw_overflow\n" ++
  ".Lbsw_next:\n" ++
  "  addi s4, s4, 1; j .Lbsw_loop\n" ++
  ".Lbsw_ok:\n" ++
  "  li a0, 0; j .Lbsw_ret\n" ++
  ".Lbsw_overflow:\n" ++
  "  li a0, 1\n" ++
  ".Lbsw_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_bv_sum_withdrawals_to_address`: probe.
    Input payload (after the zisk 8-byte length prefix, i.e. machine 0x40000000+8):
      user +0  : target address (20 bytes)
      user +24 : withdrawal count (u64)
      user +32 : SSZ withdrawals (44 bytes each)
    Output: OUTPUT+0 = status (u64); OUTPUT+8 = summed wei (u256 BE). -/
def ziskBvSumWithdrawalsToAddressPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  addi a0, t0, 8              # target address ptr (user +0)\n" ++
  "  ld a2, 32(t0)               # count (user +24)\n" ++
  "  addi a1, t0, 40             # SSZ withdrawals base (user +32)\n" ++
  "  li a3, 0xa0010008           # out u256 @ OUTPUT+8\n" ++
  "  jal ra, bv_sum_withdrawals_to_address\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status @ OUTPUT+0\n" ++
  "  j .Lbsw_pdone\n" ++
  swrRevLeBeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  bvSumWithdrawalsToAddressFunction ++ "\n" ++
  ".Lbsw_pdone:"

def ziskBvSumWithdrawalsToAddressDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n  .zero 40\n" ++         -- u256_mul_u64_be accumulator scratch
  "bsw_amount:\n  .zero 32\n" ++
  "bsw_wei:\n  .zero 32"

def ziskBvSumWithdrawalsToAddressProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBvSumWithdrawalsToAddressPrologue
  dataAsm     := ziskBvSumWithdrawalsToAddressDataSection
}

end EvmAsm.Codegen
