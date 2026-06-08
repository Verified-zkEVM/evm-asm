/-
  EvmAsm.Codegen.Programs.BlockVerdictDispatchTx

  `dispatch_tx_runtime_code`: the contract-recipient runtime gas-measurement tail
  extracted from `block_verdict` (BlockVerdict.lean, the former inline
  `.Lbv_contract_dispatch` block) into a reusable callable so the multi-transaction
  dispatch loop (evm-asm-fhsxz.2.4.2.57.11.6.2.2.2) can measure each transaction's
  runtime gas the same way the single-transaction path does.

  The body is a faithful lift of the inline contract-dispatch sequence: it stages
  the recipient's bytecode + the BAL recipient storage preload through
  `stage_runtime_payload_code`, runs the callable runtime dispatcher, and reads the
  resulting `gas_left` (evm_env[568]) and calldata floor. The only changes versus
  the inline form are (1) the witness-state ptr/len and the context-record ptr are
  passed in registers instead of read from the block_verdict input frame (`s0`), and
  (2) every conservative bail (`.Lbv_after_tx_gas_precharge` in the inline form)
  becomes a non-zero status return, while the success fall-through returns the gas
  result. The single-transaction call site stores the result into the existing
  `bv_runtime_*` cells exactly as before, so the verdict is byte-identical.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## dispatch_tx_runtime_code

    Measure one contract-recipient transaction's runtime gas by staging its
    bytecode + recipient storage preload and running the callable runtime
    dispatcher. Reaches the dispatcher only when execution is exact (the recipient
    code is self-contained — own storage only, no un-staged state); any miss or
    unsupported shape returns a non-zero status so the caller stays conservative
    (leaves `bvgr_runtime_count` short of the transaction count).

    Calling convention:
      a0 = context record ptr (192-byte simple_transfer_tx_context /
           multi_tx_nth_context layout; recipient address at +72)
      a1 = witness.state ptr   (block_verdict input frame +80)
      a2 = witness.state len   (block_verdict input frame +88)

    Reads the block-global data labels populated by block_verdict before any
    dispatch: `sv_this_rlp`/`sv_this_rlp_len`, `svf_codes_ptr`/`svf_codes_len`,
    `bv_bal_start`/`bv_bal_len`, `bv_exec_p`, plus the `bvcd_*` scratch cells,
    `cahsr_*`, `sahsr_u256`, `bv_runtime_payload`, `runtime_dispatcher_input_ptr`,
    `evm_env`, `runtime_tx_calldata_floor`.

    Returns:
      a0 = status: 0 = supported, gas measured; non-zero = unsupported / lookup
           miss / not self-contained (caller should stay conservative)
      a1 = gas_left (evm_env[568]) on status 0
      a2 = calldata_floor (runtime_tx_calldata_floor) on status 0

    Preserves the caller's s0..s3 (block_verdict holds its input frame in s0). -/
def dispatchTxRuntimeCodeFunction : String :=
  "dispatch_tx_runtime_code:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a1                    # witness.state ptr\n" ++
  "  mv s1, a2                    # witness.state len\n" ++
  "  mv s2, a0                    # context record ptr\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72\n" ++
  "  mv a3, s0; mv a4, s1\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add a0, t1, t3\n" ++
  "  la t2, cahsr_code_length; ld a1, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; sd a0, 0(t0); la t0, bvcd_code_len; sd a1, 0(t0)\n" ++
  "  jal ra, bytecode_is_self_contained\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72; la a3, bvcd_acct_ptr; la a4, bvcd_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  li t0, 2; beq a0, t0, .Ldtrc_unsupported\n" ++
  "  bnez a0, .Ldtrc_zero_storage\n" ++
  "  la t0, bvcd_acct_ptr; ld a0, 0(t0); la t0, bvcd_acct_len; ld a1, 0(t0); la a2, bvcd_keys\n" ++
  "  jal ra, bal_recipient_storage_keys\n" ++
  "  la t0, bvcd_key_count; sd a0, 0(t0); j .Ldtrc_read_storage\n" ++
  ".Ldtrc_zero_storage:\n" ++
  "  la t0, bvcd_key_count; sd zero, 0(t0)\n" ++
  ".Ldtrc_read_storage:\n" ++
  "  la t0, bvcd_i; sd zero, 0(t0)\n" ++
  ".Ldtrc_sloop:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); la t2, bvcd_key_count; ld t3, 0(t2); beq t1, t3, .Ldtrc_stage\n" ++
  "  slli t4, t1, 5; la t5, bvcd_keys; add a3, t5, t4\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  addi a2, s2, 72\n" ++
  "  mv a4, s0; mv a5, s1; mv a6, s0; mv a7, s1\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); slli t2, t1, 6; la t3, bvcd_preload; add t4, t3, t2\n" ++
  "  slli t2, t1, 5; la t3, bvcd_keys; add t5, t3, t2\n" ++
  "  li t6, 0\n" ++
  ".Ldtrc_kcopy:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_kdone\n" ++
  "  add t2, t5, t6; lbu t3, 0(t2); add t2, t4, t6; sb t3, 0(t2); addi t6, t6, 1; j .Ldtrc_kcopy\n" ++
  ".Ldtrc_kdone:\n" ++
  "  li t2, 5; beq a0, t2, .Ldtrc_vzero\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t5, sahsr_u256; li t6, 0\n" ++
  ".Ldtrc_vcopy:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_vdone\n" ++
  "  add t2, t5, t6; lbu t3, 0(t2); add t2, t4, t6; addi t2, t2, 32; sb t3, 0(t2); addi t6, t6, 1; j .Ldtrc_vcopy\n" ++
  ".Ldtrc_vzero:\n" ++
  "  li t6, 0\n" ++
  ".Ldtrc_vzloop:\n" ++
  "  li t2, 32; beq t6, t2, .Ldtrc_vdone\n" ++
  "  add t2, t4, t6; addi t2, t2, 32; sb zero, 0(t2); addi t6, t6, 1; j .Ldtrc_vzloop\n" ++
  ".Ldtrc_vdone:\n" ++
  "  la t0, bvcd_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Ldtrc_sloop\n" ++
  ".Ldtrc_stage:\n" ++
  "  mv a0, s2; la a1, bv_runtime_payload; la t2, bv_exec_p; ld a2, 0(t2)\n" ++
  "  la t0, bvcd_code_ptr; ld a3, 0(t0); la t0, bvcd_code_len; ld a4, 0(t0)\n" ++
  "  la a5, bvcd_preload; la t0, bvcd_key_count; ld a6, 0(t0)\n" ++
  "  jal ra, stage_runtime_payload_code\n" ++
  "  bnez a0, .Ldtrc_unsupported\n" ++
  "  la t4, runtime_dispatcher_input_ptr; la t5, bv_runtime_payload; addi t5, t5, 8; sd t5, 0(t4)\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  jal ra, runtime_dispatcher_call\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  la t4, runtime_dispatcher_input_ptr; sd zero, 0(t4)\n" ++
  "  la t2, evm_env; ld t3, 568(t2)\n" ++
  "  la t4, runtime_tx_calldata_floor; ld t5, 0(t4)\n" ++
  "  mv a1, t3                    # gas_left\n" ++
  "  mv a2, t5                    # calldata_floor\n" ++
  "  li a0, 0\n" ++
  "  j .Ldtrc_ret\n" ++
  ".Ldtrc_unsupported:\n" ++
  "  li a0, 1\n" ++
  ".Ldtrc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

end EvmAsm.Codegen
