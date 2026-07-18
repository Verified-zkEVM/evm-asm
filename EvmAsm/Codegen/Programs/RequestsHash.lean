/-
  EvmAsm.Codegen.Programs.RequestsHash

  RISC-V helper for the EIP-7685 execution header `requests_hash`:
  `sha256(concat(sha256(type_byte || request_payload) for non-empty request
  kinds in ascending type order))`.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def executionRequestsHashFunction : String :=
  "execution_requests_hash:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # SszExecutionRequests section\n" ++
  "  mv s1, a1                   # section length\n" ++
  "  mv s2, a2                   # output hash\n" ++
  "  li t0, 20; bltu s1, t0, .Lerh_fail\n" ++
  "  mv a0, s0; jal ra, bgv_u32le; mv s3, a0\n" ++
  "  addi a0, s0, 4; jal ra, bgv_u32le; mv s4, a0\n" ++
  "  addi a0, s0, 8; jal ra, bgv_u32le; mv s5, a0\n" ++
  "  addi a0, s0, 12; jal ra, bgv_u32le; mv s6, a0\n" ++
  "  addi a0, s0, 16; jal ra, bgv_u32le; mv s7, a0\n" ++
  -- hbo40: canonical SSZ requires the FIRST variable-field offset to EQUAL the fixed-part
  -- size exactly. SszExecutionRequests has 5 variable SszList fields -> fixed part = 5*4 = 20,
  -- so offset0 (s3) MUST be 20, not merely >= 20. remerkleable decode_bytes raises on any
  -- offset0 != 20 (a leading gap between the offset table and the deposits body), so the spec
  -- rejects it; the old lower-bound accepted a non-canonical
  -- false-accept. Exact-equality is soundness-additive: every valid block has offset0 == 20.
  "  li t0, 20; bne s3, t0, .Lerh_fail\n" ++
  "  bltu s4, s3, .Lerh_fail\n" ++
  "  bltu s5, s4, .Lerh_fail\n" ++
  "  bltu s6, s5, .Lerh_fail\n" ++
  "  bltu s7, s6, .Lerh_fail\n" ++
  "  bltu s1, s7, .Lerh_fail\n" ++
  -- vdfs9: each request body must be a whole number of fixed-size SSZ elements
  -- (DepositRequest=192, WithdrawalRequest=76, ConsolidationRequest=116,
  -- BuilderDepositRequest=184, BuilderExitRequest=68) within the SszList caps
  -- (2^13 / 2^4 / 2^1 / 2^6 / 2^4). A non-multiple body length or an over-cap count is
  -- a malformed execution_requests section that the spec's SSZ deserialization rejects;
  -- the body was previously hashed verbatim, so a prover-consistent malformed section
  -- (with header.requests_hash set to match) would have slipped through.
  "  sub t0, s4, s3; li t1, 192; remu t2, t0, t1; bnez t2, .Lerh_fail\n" ++
  "  divu t2, t0, t1; li t3, 8192; bgtu t2, t3, .Lerh_fail\n" ++
  "  sub t0, s5, s4; li t1, 76;  remu t2, t0, t1; bnez t2, .Lerh_fail\n" ++
  "  divu t2, t0, t1; li t3, 16;   bgtu t2, t3, .Lerh_fail\n" ++
  "  sub t0, s6, s5; li t1, 116; remu t2, t0, t1; bnez t2, .Lerh_fail\n" ++
  "  divu t2, t0, t1; li t3, 2;    bgtu t2, t3, .Lerh_fail\n" ++
  "  sub t0, s7, s6; li t1, 184; remu t2, t0, t1; bnez t2, .Lerh_fail\n" ++
  "  divu t2, t0, t1; li t3, 64;   bgtu t2, t3, .Lerh_fail\n" ++
  "  sub t0, s1, s7; li t1, 68; remu t2, t0, t1; bnez t2, .Lerh_fail\n" ++
  "  divu t2, t0, t1; li t3, 16;   bgtu t2, t3, .Lerh_fail\n" ++
  "  la s8, erh_digests          # next digest output\n" ++
  "  li s9, 0                    # digest count\n" ++
  "  # deposits: type 0x00, body [s3,s4)\n" ++
  "  sub s10, s4, s3; beqz s10, .Lerh_withdrawals\n" ++
  "  add a3, s0, s3; li a4, 0; jal ra, erh_hash_one\n" ++
  "  addi s8, s8, 32; addi s9, s9, 1\n" ++
  ".Lerh_withdrawals:\n" ++
  "  sub s10, s5, s4; beqz s10, .Lerh_consolidations\n" ++
  "  add a3, s0, s4; li a4, 1; jal ra, erh_hash_one\n" ++
  "  addi s8, s8, 32; addi s9, s9, 1\n" ++
  ".Lerh_consolidations:\n" ++
  "  sub s10, s6, s5; beqz s10, .Lerh_builder_deposits\n" ++
  "  add a3, s0, s5; li a4, 2; jal ra, erh_hash_one\n" ++
  "  addi s8, s8, 32; addi s9, s9, 1\n" ++
  ".Lerh_builder_deposits:\n" ++
  "  sub s10, s7, s6; beqz s10, .Lerh_builder_exits\n" ++
  "  add a3, s0, s6; li a4, 3; jal ra, erh_hash_one\n" ++
  "  addi s8, s8, 32; addi s9, s9, 1\n" ++
  ".Lerh_builder_exits:\n" ++
  "  sub s10, s1, s7; beqz s10, .Lerh_final\n" ++
  "  add a3, s0, s7; li a4, 4; jal ra, erh_hash_one\n" ++
  "  addi s8, s8, 32; addi s9, s9, 1\n" ++
  ".Lerh_final:\n" ++
  "  la a0, erh_digests; slli a1, s9, 5; mv a2, s2; jal ra, zkvm_sha256\n" ++
  "  li a0, 0; j .Lerh_ret\n" ++
  ".Lerh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lerh_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "erh_hash_one:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  la t0, erh_blob; sb a4, 0(t0)\n" ++
  "  addi t1, t0, 1; mv t2, a3; mv t3, s10\n" ++
  ".Lerh_copy:\n" ++
  "  beqz t3, .Lerh_hash\n" ++
  "  lbu t4, 0(t2); sb t4, 0(t1)\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lerh_copy\n" ++
  ".Lerh_hash:\n" ++
  "  la a0, erh_blob; addi a1, s10, 1; mv a2, s8; jal ra, zkvm_sha256\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16; ret"

def executionRequestsHashDataSection : String :=
  ".balign 32\n" ++
  "erh_digests:\n  .zero 160\n" ++
  ".balign 32\n" ++
  "erh_requests_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "erh_blob:\n  .zero 1572865\n"

def executionRequestsHashShaDataSection : String :=
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n"

end EvmAsm.Codegen
