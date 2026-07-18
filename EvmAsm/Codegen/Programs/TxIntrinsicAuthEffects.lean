/-
  EvmAsm.Codegen.Programs.TxIntrinsicAuthEffects

  EIP-7702 authorization-list effects used by the transaction intrinsic-state-
  gas path.  Kept separate from the state-gas emitter so each codegen source
  stays below the file-size guardrail.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.BlockVerdictBalFindAccount
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.Eip7702Authority
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasProg

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_verdict_eip7702_auth_nonstorage_effects

    EIP-7702 set_delegation increments each successfully authorized authority's
    nonce before message execution. That nonce change is not produced by CALL /
    CREATE execution, so append a nonce-only non-storage effect for every auth
    tuple whose recovered authority is present in the BAL and whose pre-state
    nonce matches the signed nonce. Code changes remain covered by the existing
    7702 code-comparator exception; this helper supplies only the balance/nonce
    effect used by the all-accounts non-storage comparators. -/
def eip7702AuthNonstorageEffectsFunction : String :=
  "eip7702_auth_nonstorage_effects:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # BAL ptr\n" ++
  "  mv s3, a3                   # BAL len\n" ++
  "  mv s4, a4                   # chain id\n" ++
  "  beqz s2, .Lteanse_done\n" ++
  "  mv a0, s0; mv a1, s1; la a2, teer_type; la a3, teer_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lteanse_done\n" ++
  "  la t0, teer_type; ld t1, 0(t0); li t2, 4; bne t1, t2, .Lteanse_done\n" ++
  "  la t0, teer_inner_off; ld t1, 0(t0); bgtu t1, s1, .Lteanse_done; add s5, s0, t1; sub s6, s1, t1\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteanse_done\n" ++
  "  mv s5, a0; mv s6, a1\n" ++
  rlpWalkFieldAsm ".Lteanse_done" 9 "s5" "s6" "s5" "s6" ++
  "  mv a0, s5; mv a1, s6; la a2, teer_auth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lteanse_done\n" ++
  "  la t0, teer_auth_count; ld s7, 0(t0)\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteanse_done\n" ++
  "  mv s5, a0; mv s6, a1; li s8, 0\n" ++
  ".Lteanse_loop:\n" ++
  "  beq s8, s7, .Lteanse_done\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_done\n" ++
  "  mv s5, a0; sub s9, a0, a2; mv s10, a2\n" ++
  "  mv a0, s9; mv a1, s10; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lteanse_next\n" ++
  "  sd a0, 104(sp); sd a1, 112(sp)\n" ++
  "  ld a0, 104(sp); ld a1, 112(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  sd a0, 104(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  mv t1, a0; beqz t1, .Lteanse_chain_ok; bne t1, s4, .Lteanse_next\n" ++
  ".Lteanse_chain_ok:\n" ++
  "  ld a0, 104(sp); ld a1, 112(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  sd a0, 104(sp); li t2, 20; bne a2, t2, .Lteanse_next\n" ++
  "  ld a0, 104(sp); ld a1, 112(sp); jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  sd a0, 104(sp); sub a0, a0, a2; mv a1, a2\n" ++
  "  jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lteanse_next\n" ++
  "  mv s11, a0; li t2, -1; beq s11, t2, .Lteanse_next\n" ++
  "  mv a0, s9; mv a1, s10; la a2, teer_authority; la a3, teer_recover_scratch\n" ++
  "  jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lteanse_next\n" ++
  "  mv a0, s2; mv a1, s3; la a2, teer_authority; la a3, teer_acct_ptr; la a4, teer_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lteanse_next\n" ++
  "  la t0, teer_acct_ptr; ld a0, 0(t0); la t0, teer_acct_len; ld a1, 0(t0); la a2, teer_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lteanse_next\n" ++
  "  la t0, teer_finals; ld t1, 40(t0); beqz t1, .Lteanse_next\n" ++
  "  ld t1, 48(t0); addi t2, s11, 1; bltu t1, t2, .Lteanse_next\n" ++
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, teer_authority; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, teer_pre_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  beqz a0, .Lteanse_have_pre\n" ++
  "  li t0, 1; bne a0, t0, .Lteanse_next\n" ++
  "  bnez s11, .Lteanse_next\n" ++
  "  la t0, teer_pre_acct; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0); sd zero, 32(t0)\n" ++
  "  j .Lteanse_record\n" ++
  ".Lteanse_have_pre:\n" ++
  -- Each authorization validates the authority's current nonce.  Earlier valid
  -- tuples in this transaction already recorded the increment, so use that
  -- latest effect when present instead of repeatedly comparing to header state.
  "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  la a0, teer_authority; la a1, teer_pre_acct\n" ++
  "  jal ra, nonstorage_effect_latest_nonce\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  "  la t0, teer_pre_acct; ld t1, 0(t0); bne t1, s11, .Lteanse_next\n" ++
  ".Lteanse_record:\n" ++
  "  la a0, teer_authority; la a1, teer_pre_acct; addi a1, a1, 8; mv a2, a1; mv a3, s11; addi a4, s11, 1\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  la t0, teer_finals; ld t1, 56(t0); beqz t1, .Lteanse_next\n" ++
  "  ld t1, 72(t0); bnez t1, .Lteanse_next\n" ++
  "  la t0, exec_code_effect_next; ld t1, 0(t0); addi t2, t1, 48; li t3, " ++ toString execCodeEffectLogCap ++ "; bgtu t2, t3, .Lteanse_code_overflow\n" ++
  "  la t3, exec_code_effect_log; add t3, t3, t1\n" ++
  "  sd zero, 0(t3); sd zero, 8(t3); sd zero, 16(t3); sd zero, 24(t3)\n" ++
  "  la t4, teer_authority; mv t5, t3; li t6, 20\n" ++
  ".Lteanse_code_addr:\n" ++
  "  beqz t6, .Lteanse_code_addr_done\n" ++
  "  lbu a0, 0(t4); sb a0, 0(t5); addi t4, t4, 1; addi t5, t5, 1; addi t6, t6, -1; j .Lteanse_code_addr\n" ++
  ".Lteanse_code_addr_done:\n" ++
  "  li t4, 1; sd t4, 32(t3); sd zero, 40(t3)\n" ++
  "  la t0, exec_code_effect_count; ld t4, 0(t0); addi t4, t4, 1; sd t4, 0(t0)\n" ++
  "  la t0, exec_code_effect_next; sd t2, 0(t0); j .Lteanse_next\n" ++
  ".Lteanse_code_overflow:\n" ++
  "  la t0, exec_code_effect_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Lteanse_next:\n" ++
  "  addi s8, s8, 1; j .Lteanse_loop\n" ++
  ".Lteanse_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

end EvmAsm.Codegen
