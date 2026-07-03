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
def sszWithdrawalToRlpFunction : String :=
  "ssz_withdrawal_to_rlp:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # ssz withdrawal\n" ++
  "  mv s1, a1                   # out\n" ++
  "  mv s2, a2                   # out_len\n" ++
  "  li s3, 0                    # payload cursor\n" ++
  "  # field 0: index (u64 LE @0)\n" ++
  "  addi a0, s0, 0; li a1, 8; la a2, swr_be\n" ++
  "  jal ra, swr_rev_le_be\n" ++
  "  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s3, s3, a0\n" ++
  "  # field 1: validator_index (u64 LE @8)\n" ++
  "  addi a0, s0, 8; li a1, 8; la a2, swr_be\n" ++
  "  jal ra, swr_rev_le_be\n" ++
  "  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s3, s3, a0\n" ++
  "  # field 2: address (20 B @16)\n" ++
  "  addi a0, s0, 16; li a1, 20\n" ++
  "  la a2, swr_payload; add a2, a2, s3; la a3, swr_flen\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  la t0, swr_flen; ld t1, 0(t0); add s3, s3, t1\n" ++
  "  # field 3: amount (u64 LE @36)\n" ++
  "  addi a0, s0, 36; li a1, 8; la a2, swr_be\n" ++
  "  jal ra, swr_rev_le_be\n" ++
  "  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  add s3, s3, a0\n" ++
  "  # list prefix + copy payload after it\n" ++
  "  mv a0, s3; mv a1, s1; la a2, swr_prefix_len\n" ++
  "  jal ra, rlp_encode_list_prefix\n" ++
  "  la t0, swr_prefix_len; ld t1, 0(t0)\n" ++
  "  add t2, s1, t1; la t3, swr_payload; mv t4, s3\n" ++
  ".Lswr_cp:\n" ++
  "  beqz t4, .Lswr_cpd\n" ++
  "  lbu t5, 0(t3); sb t5, 0(t2)\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1\n" ++
  "  j .Lswr_cp\n" ++
  ".Lswr_cpd:\n" ++
  "  add t1, t1, s3; sd t1, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

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
