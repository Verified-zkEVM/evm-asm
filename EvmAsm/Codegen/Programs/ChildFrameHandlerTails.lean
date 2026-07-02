/-
  EvmAsm.Codegen.Programs.ChildFrameHandlerTails

  Extracted from `ChildFrameHandlers.lean` to keep every file under the
  `FileSizeGuard` line cap. Holds the CALL/STATICCALL precompile tail builder
  plus delegation-access helper. The CREATE-family tail lives in
  `ChildFrameCreateTail.lean` and is re-exported through this import chain.
-/

import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Modexp
import EvmAsm.Codegen.Programs.CreateRuntime
import EvmAsm.Codegen.Programs.CreateSameTxCollision
import EvmAsm.Codegen.Programs.PrecompileRuntime
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.ChildFrameCreateTail
import EvmAsm.Rv64.Program
namespace EvmAsm.Codegen
open EvmAsm.Rv64

/-- Charge the EIP-7702 delegation target access for a CALL-family callee when
    the callee is a `0xef0100||addr` delegation marker. -/
def callDelegationAccessChargeAsm (tag : String) : String :=
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  ld a3, 592(x20)\n  ld a4, 600(x20)\n  ld a5, 608(x20)\n  ld a6, 616(x20)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  mv t2, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  -- not found / error -> not delegated -> no charge
  "  bnez t2, .Lcdac_done_" ++ tag ++ "\n" ++
  "  la t3, cahsr_code_length; ld t3, 0(t3); li t4, 23; bne t3, t4, .Lcdac_done_" ++ tag ++ "\n" ++
  "  ld t3, 608(x20); la t4, cahsr_code_offset; ld t4, 0(t4); add t3, t3, t4\n" ++  -- t3 = code ptr
  "  lbu t4, 0(t3); li t5, 0xef; bne t4, t5, .Lcdac_done_" ++ tag ++ "\n" ++
  "  lbu t4, 1(t3); li t5, 0x01; bne t4, t5, .Lcdac_done_" ++ tag ++ "\n" ++
  "  lbu t4, 2(t3); bnez t4, .Lcdac_done_" ++ tag ++ "\n" ++
  -- delegation marker: target = code[3..22] (20-byte canonical BE) at t3+3.
  -- runtime_access_account_charge reads 20 bytes from a0 (read-only), so pass it
  -- the in-place marker bytes; it debits 2500 + inserts on cold, 0 on warm.
  "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  addi a0, t3, 3\n  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  -- add the 100 warm-floor the helper omits, so total = 2600 cold / 100 warm.
  "  ld t0, 568(x20)\n  li t1, 100\n  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n  sd t0, 568(x20)\n" ++
  ".Lcdac_done_" ++ tag ++ ":\n"

def precompileValueBalanceGateAsm (tag : String) (netPopBytes valueOff : Nat) : String :=
  -- Value-bearing CALL/CALLCODE to a precompile still runs the generic-call
  -- caller-balance check before entering the precompile. On insufficient
  -- balance, execution-specs charges the net value-call gas and returns 0.
  "  ld t3, " ++ toString valueOff ++ "(x12)\n" ++
  "  ld t4, " ++ toString (valueOff+8) ++ "(x12)\n  or t3, t3, t4\n" ++
  "  ld t4, " ++ toString (valueOff+16) ++ "(x12)\n  or t3, t3, t4\n" ++
  "  ld t4, " ++ toString (valueOff+24) ++ "(x12)\n  or t3, t3, t4\n" ++
  "  beqz t3, .L" ++ tag ++ "_precompile_balok\n" ++
  "  ld t3, 584(x20)\n" ++
  "  beqz t3, .L" ++ tag ++ "_precompile_balok\n" ++
  "  la t0, cd_value_be\n" ++
  "  addi t1, x12, " ++ toString (valueOff+31) ++ "\n" ++
  "  li t2, 32\n" ++
  ".L" ++ tag ++ "_precompile_val:\n" ++
  "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n" ++
  "  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .L" ++ tag ++ "_precompile_val\n" ++
  "  addi t0, x20, 63\n  la t1, cd_balance_be\n  li t2, 32\n" ++
  ".L" ++ tag ++ "_precompile_livebal:\n" ++
  "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n" ++
  "  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .L" ++ tag ++ "_precompile_livebal\n" ++
  "  la t0, cd_balance_be\n" ++
  "  la t1, cd_value_be\n" ++
  "  li t2, 32\n" ++
  ".L" ++ tag ++ "_precompile_cmp:\n" ++
  "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
  "  bltu t3, t4, .L" ++ tag ++ "_precompile_insuffbal\n" ++
  "  bltu t4, t3, .L" ++ tag ++ "_precompile_balok\n" ++
  "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
  "  bnez t2, .L" ++ tag ++ "_precompile_cmp\n" ++
  ".L" ++ tag ++ "_precompile_balok:\n" ++
  "  j .L" ++ tag ++ "_precompile_dispatch\n" ++
  ".L" ++ tag ++ "_precompile_insuffbal:\n" ++
  "  li t0, 6700\n" ++
  "  ld t1, 568(x20)\n  bltu t1, t0, .exit_outofgas\n" ++
  "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++
  "  la x15, evm_precompile_frame\n" ++
  "  sd x0, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
  "  sd x0, 0(x12)\n" ++
  "  sd x0, 8(x12)\n" ++
  "  sd x0, 16(x12)\n" ++
  "  sd x0, 24(x12)\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop\n" ++
  ".L" ++ tag ++ "_precompile_dispatch:\n"

def emitSuccessfulPrecompileValueLogAsm (tag : String) (valueOff? : Option Nat) : String :=
  match valueOff? with
  | none => ""
  | some valueOff =>
    -- Value-bearing precompile calls are successful child messages when they
    -- reach the shared success tail. Emit the EIP-7708 transfer log here, not
    -- before dispatch, so failed precompile calls keep the ordinary child
    -- rollback behavior. The appender expects raw EVM stack-word pointers:
    -- env.ADDRESS at x20, callee at x12+32, and value at x12+valueOff.
    "  ld t0, " ++ toString valueOff ++ "(x12)\n" ++
    "  ld t1, " ++ toString (valueOff+8) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff+16) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  ld t1, " ++ toString (valueOff+24) ++ "(x12)\n  or t0, t0, t1\n" ++
    "  beqz t0, .L" ++ tag ++ "_precompile_xlog_skip\n" ++
    "  mv t0, x20\n  addi t1, x12, 32\n  li t2, 20\n" ++
    ".L" ++ tag ++ "_precompile_xlog_selfcmp:\n" ++
    "  beqz t2, .L" ++ tag ++ "_precompile_xlog_skip\n" ++
    "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n" ++
    "  bne t3, t4, .L" ++ tag ++ "_precompile_xlog_emit\n" ++
    "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n" ++
    "  j .L" ++ tag ++ "_precompile_xlog_selfcmp\n" ++
    ".L" ++ tag ++ "_precompile_xlog_emit:\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  mv a0, x20\n  addi a1, x12, 32\n  addi a2, x12, " ++ toString valueOff ++ "\n" ++
    "  jal ra, eip7708_append_transfer_log\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    ".L" ++ tag ++ "_precompile_xlog_skip:\n"

def basicPrecompileCallTail
      (tag : String) (netPopBytes inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat)
      (valueOff? : Option Nat)
      (fallThroughAsm : String) : String :=
    -- Stack top at entry is the call gas word. The destination
    -- address is the next word for both CALL and STATICCALL. EVM
    -- address operands are masked to the low 160 bits: limb 1 and
    -- the low 32 bits of limb 2 participate in precompile dispatch,
    -- while bits 160..255 are ignored.
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  addi t0, x12, 32\n" ++
    "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    runtimeAccessWordToBe20Asm tag "t0" "t1" "t2" "t3" ++
    "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_charge\n" ++
    -- EIP-7702: when the callee is a delegation marker, ALSO charge the delegation
    -- target's access (cold 2600 / warm 100). callDelegationAccessChargeAsm
    -- preserves s9/s10/s11 and x10/x12/x13, so the restore below still holds.
    callDelegationAccessChargeAsm tag ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    callMemoryExpansionGasAsm
      ("precompile_" ++ tag)
      inOffsetOff inSizeOff outOffsetOff outSizeOff ++
    (if tag == "call_target" || tag == "staticcall_target" then (
    -- EIP-4788 beacon-roots system contract fast path for the current block's
    -- begin-of-block write. The ordinary bytecode descent resolves storage at a
    -- committed header root and therefore cannot see the just-modeled system
    -- storage update; `system_writes` has already staged that `(timestamp, root)`
    -- pair in swd_4788_{val,root_val}. CALLCODE/DELEGATECALL into the predeploy
    -- must keep normal bytecode semantics because their ADDRESS context is the
    -- caller, not the system contract. Historical/stale cases also keep using the
    -- normal bytecode path below.
    "  la t0, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
    "  la t1, bsr_addr_4788\n" ++
    "  li t2, 20\n" ++
    ".L" ++ tag ++ "_eip4788_addr_cmp:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_addr_match\n" ++
    "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_addr_cmp\n" ++
    ".L" ++ tag ++ "_eip4788_addr_match:\n" ++
    "  ld t0, " ++ toString inSizeOff ++ "(x12); li t1, 32; bne t0, t1, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  ld t0, 0(x12); li t1, 2100; bltu t0, t1, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  ld t0, " ++ toString inOffsetOff ++ "(x12); add t0, x13, t0\n" ++
    "  li t2, 24\n" ++
    ".L" ++ tag ++ "_eip4788_ts_hi_zero:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_ts_low_cmp_init\n" ++
    "  lbu t3, 0(t0); bnez t3, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  addi t0, t0, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_ts_hi_zero\n" ++
    ".L" ++ tag ++ "_eip4788_ts_low_cmp_init:\n" ++
    "  la t1, swd_ts_be8\n" ++
    "  li t2, 8\n" ++
    ".L" ++ tag ++ "_eip4788_ts_cmp:\n" ++
    "  beqz t2, .L" ++ tag ++ "_eip4788_current\n" ++
    "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L" ++ tag ++ "_eip4788_fallthrough\n" ++
    "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L" ++ tag ++ "_eip4788_ts_cmp\n" ++
    ".L" ++ tag ++ "_eip4788_current:\n" ++
    "  li t0, 1; la t1, bv_eip4788_current_fast_seen; sd t0, 0(t1)\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li t0, 1; sd t0, 0(x15)\n" ++
    "  li t0, 32; sd t0, 8(x15)\n" ++
    "  addi t1, x15, 16; li t2, 32\n" ++
    ".L" ++ tag ++ "_eip4788_frame_zero:\n" ++
    "  sb zero, 0(t1); addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_frame_zero\n" ++
    "  la t0, swd_4788_root_vlen; ld t2, 0(t0); beqz t2, .L" ++ tag ++ "_eip4788_frame_ready\n" ++
    "  li t3, 32; bgtu t2, t3, .L" ++ tag ++ "_eip4788_frame_ready\n" ++
    "  addi t1, x15, 48; sub t1, t1, t2; la t0, swd_4788_root_val\n" ++
    ".L" ++ tag ++ "_eip4788_frame_copy:\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L" ++ tag ++ "_eip4788_frame_copy\n" ++
    ".L" ++ tag ++ "_eip4788_frame_ready:\n" ++
    "  ld t2, " ++ toString outSizeOff ++ "(x12); li t3, 32; bgeu t2, t3, .L" ++ tag ++ "_eip4788_out_cap\n" ++
    "  mv t3, t2\n" ++
    ".L" ++ tag ++ "_eip4788_out_cap:\n" ++
    "  beqz t3, .L" ++ tag ++ "_eip4788_success\n" ++
    "  addi t0, x15, 16; ld t1, " ++ toString outOffsetOff ++ "(x12); add t1, x13, t1\n" ++
    ".L" ++ tag ++ "_eip4788_out_copy:\n" ++
    "  lbu t2, 0(t0); sb t2, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t3, t3, -1; bnez t3, .L" ++ tag ++ "_eip4788_out_copy\n" ++
    ".L" ++ tag ++ "_eip4788_success:\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  li x14, 1; sd x14, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    ".L" ++ tag ++ "_eip4788_fallthrough:\n"
    ) else "") ++
    "  ld x14, 32(x12)\n" ++
    "  ld x15, 40(x12)\n" ++
    "  bnez x15, .L" ++ tag ++ "_nonprecompile_fallthrough\n" ++
    "  ld x15, 48(x12)\n" ++
    "  slli x15, x15, 32\n" ++
    "  srli x15, x15, 32\n" ++
    "  bnez x15, .L" ++ tag ++ "_nonprecompile_fallthrough\n" ++
    "  li x15, 1\n" ++
    "  bltu x14, x15, .L" ++ tag ++ "_nonprecompile_fallthrough\n" ++
    "  li x15, 0x12\n" ++
    "  bgeu x15, x14, .L" ++ tag ++ "_supported_precompile\n" ++
    "  li x15, 0x100\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_supported_precompile\n" ++
    "  li x15, 0x101\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_supported_precompile\n" ++
    "  j .L" ++ tag ++ "_nonprecompile_fallthrough\n" ++
    ".L" ++ tag ++ "_supported_precompile:\n" ++
    (match valueOff? with
    | none => ".L" ++ tag ++ "_precompile_dispatch:\n"
    | some valueOff => precompileValueBalanceGateAsm tag netPopBytes valueOff) ++
    "  li x15, 4\n" ++
    "  bgeu x15, x14, 11f\n" ++
    "  li x15, 5\n" ++
    "  beq x14, x15, .Lmodexp_zero_header_" ++ tag ++ "\n" ++
    "  li x15, 0x06\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_add\n" ++
    "  li x15, 0x07\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_mul\n" ++
    "  li x15, 0x08\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_bn254_pairing\n" ++
    "  li x15, 0x09\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_blake2f\n" ++
    "  li x15, 0x0a\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_kzg_point_eval\n" ++
    "  li x15, 0x0b\n" ++
    "  beq x14, x15, 13f\n" ++
    "  li x15, 0x0c\n" ++
    "  beq x14, x15, 14f\n" ++
    "  li x15, 0x0d\n" ++
    "  beq x14, x15, 15f\n" ++
    "  li x15, 0x0e\n" ++
    "  beq x14, x15, 16f\n" ++
    "  li x15, 0x0f\n" ++
    "  beq x14, x15, 17f\n" ++
    "  li x15, 0x10\n" ++
    "  beq x14, x15, 18f\n" ++
    "  li x15, 0x11\n" ++
    "  beq x14, x15, 19f\n" ++
    "  li x15, 0x12\n" ++
    "  beq x14, x15, 12f\n" ++
    "  li x15, 0x100\n" ++
    "  beq x14, x15, .L" ++ tag ++ "_p256verify\n" ++
    "  li x15, 0x101\n" ++
    "  beq x14, x15, 12f\n" ++
    "  j .L" ++ tag ++ "_nonprecompile_fallthrough\n" ++
    "11:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 1\n" ++
    "  beq x14, x16, 29f\n" ++
    "  li x16, 2\n" ++
    "  beq x14, x16, 8f\n" ++
    "  li x16, 3\n" ++
    "  beq x14, x16, .L" ++ tag ++ "_ripemd160\n" ++
    "  li x16, 4\n" ++
    "  bne x14, x16, 7f\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasWithAllotmentAsm tag 15 3 "x17" "x16" "x22" ++
    -- The allotment helper clobbers x17; reload the input length before using
    -- it as identity's returndata length and copy bound.
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  sd x17, 8(x15)\n" ++       -- returndata length = full input size
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add x18, x13, x18\n" ++    -- x18 = identity input bytes
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++    -- x19 = caller output bytes
    -- Copy up to 256 bytes of returndata into the shared frame.
    "  mv x22, x18\n" ++
    "  addi x23, x15, 16\n" ++
    "  mv x24, x17\n" ++
    "  li x16, 256\n" ++
    "  bgeu x16, x24, 2f\n" ++
    "  mv x24, x16\n" ++
    "2:\n" ++
    "  beqz x24, 4f\n" ++
    "3:\n" ++
    "  lbu x16, 0(x22)\n" ++
    "  sb x16, 0(x23)\n" ++
    "  addi x22, x22, 1\n" ++
    "  addi x23, x23, 1\n" ++
    "  addi x24, x24, -1\n" ++
    "  bnez x24, 3b\n" ++
    -- Copy min(input_size, output_size) bytes to caller memory.
    "4:\n" ++
    "  mv x22, x17\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  bgeu x23, x22, 5f\n" ++
    "  mv x22, x23\n" ++
    "5:\n" ++
    "  beqz x22, 7f\n" ++
    -- If the caller output range overlaps the identity input range at a higher
    -- address, copy backward. Forward byte copy would smear the source bytes
    -- (memcpy vs memmove) before later bytes are read.
    "  bleu x19, x18, 6f\n" ++
    "  add x23, x18, x22\n" ++
    "  bgeu x19, x23, 6f\n" ++
    "  add x18, x18, x22\n" ++
    "  add x19, x19, x22\n" ++
    "8:\n" ++
    "  addi x18, x18, -1\n" ++
    "  addi x19, x19, -1\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 8b\n" ++
    "  j 7f\n" ++
    "6:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 6b\n" ++
    "7:\n" ++
    emitSuccessfulPrecompileValueLogAsm tag valueOff? ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  li x14, 1\n" ++
    "  sd x14, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "  addi x10, x10, 1\n" ++
    "  j .dispatch_loop\n" ++
    -- SHA256: digest = sha256(memory[in_offset .. in_offset+in_size)).
    -- The wrapper uses the LP64 a0/a1/a2 registers, so save the
    -- dispatcher code and stack pointers before setting up arguments.
    "8:\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a1, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasWithAllotmentAsm tag 60 12 "a1" "x16" "x22" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x18\n" ++
    "  addi a2, x15, 16\n" ++
    "  jal x1, zkvm_sha256\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x22, 32\n" ++
    "  bgeu x23, x22, 9f\n" ++
    "  mv x22, x23\n" ++
    "9:\n" ++
    "  beqz x22, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "10:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 10b\n" ++
    "  j 7b\n" ++
    -- RIPEMD160 (0x03): digest = ripemd160(memory[in_offset .. in_offset+
    -- in_size)) via the software `zkvm_ripemd160` kernel (no ZisK accelerator
    -- exists for RIPEMD-160), word-linear 600 + 120/word gas, 32-byte
    -- returndata = 12 zero bytes ++ 20-byte hash (the EVM left-padded
    -- encoding, written by the kernel itself). Mirrors the SHA256 path above.
    ".L" ++ tag ++ "_ripemd160:\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a1, " ++ toString inSizeOff ++ "(x12)\n" ++
    chargePrecompileWordGasWithAllotmentAsm tag 600 120 "a1" "x16" "x22" ++
    "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x18\n" ++
    "  addi a2, x15, 16\n" ++
    "  jal x1, zkvm_ripemd160\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  ld x23, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x22, 32\n" ++
    "  bgeu x23, x22, .L" ++ tag ++ "_ripemd_outcap\n" ++
    "  mv x22, x23\n" ++
    ".L" ++ tag ++ "_ripemd_outcap:\n" ++
    "  beqz x22, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    ".L" ++ tag ++ "_ripemd_copy:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_ripemd_copy\n" ++
    "  j 7b\n" ++
    -- ECRECOVER fixed gas, input staging, v/r/s gates, then (.62.2.5) the
    -- backend-pointer-gated recovery + 32-byte address output. Closures that
    -- leave `ecrecover_backend_ptr` 0 keep the legacy empty-returndata success.
    "29:\n" ++
    chargePrecompileGasConstWithAllotmentAsm tag 3000 "x16" "x17" ++
    stageEcrecoverInputAsm inOffsetOff inSizeOff ++
    ecrecoverVGateAsm ++
    ecrecoverNonzeroRSGateAsm ++
    ecrecoverScalarOrderGateAsm ++
    ecrecoverRecoverAndOutputAsm outOffsetOff outSizeOff ++
    -- MODEXP header/gas path. execution-specs decodes missing length/header
    -- bytes as zero, rejects component lengths above 1024 before charging gas,
    -- and otherwise charges the EIP-2565/Osaka gas formula. Small nonzero
    -- components use a bounded software path; larger inputs still wait for
    -- the full zkvm_modexp output slice.
    ".Lmodexp_zero_header_" ++ tag ++ ":\n" ++
    modexpPrecompileGasAsm
      (chargePrecompileGasWithAllotmentPreservingModexpAsm tag)
      tag
      inOffsetOff inSizeOff outOffsetOff outSizeOff ++
    -- BN254 failed-call tail (kernel invalid input / child OOG): burn the
    -- forwarded EIP-150 allotment, push 0, resume. Reached only by branches
    -- from the two entries below (the preceding modexp block ends with jumps).
    bn254FailureStubAsm tag netPopBytes ++
    -- BN254 G1 ADD (EIP-196 ecAdd): fixed 150 gas charged from the child
    -- allotment, two 64-byte zero-padded G1 inputs, real Bn254CurveAdd-backed
    -- kernel. Invalid input (coord >= p / off-curve) is a precompile failure
    -- that consumes the full child allotment (execution-specs OutOfGasError).
    ".L" ++ tag ++ "_bn254_add:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 150\n" ++
    bn254ChargeGateAsm tag ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_add_p1") inOffsetOff inSizeOff precompileFrameBls12G1Input0Off 0 64 ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_add_p2") inOffsetOff inSizeOff precompileFrameBls12G1Input1Off 64 64 ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_g1_add\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- PC into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_bn254_add_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BN254 G1 MUL (EIP-196 ecMul): fixed 6000 gas, one 64-byte point plus
    -- one 32-byte scalar, real double-and-add kernel. Same failure mode.
    ".L" ++ tag ++ "_bn254_mul:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 6000\n" ++
    bn254ChargeGateAsm tag ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_mul_point") inOffsetOff inSizeOff precompileFrameBls12G1Input0Off 0 64 ++
    stagePrecompileInputWindowAsm
      (tag ++ "_bn254_mul_scalar") inOffsetOff inSizeOff precompileFrameBls12G1Input1Off 64 32 ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G1Input0Off ++
    precompileFrameAddi "a1" precompileFrameBls12G1Input1Off ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_g1_mul\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- PC into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_bn254_mul_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BN254 pairing (EIP-197): cost = 45000 + 34000 * floor(len / 192),
    -- charged from the EIP-150 child allotment. A gas-formula overflow,
    -- a non-multiple-of-192 length, or kernel-invalid input (coord >= p,
    -- off-curve, or Q outside the order-n subgroup) is a FAILED call that
    -- burns the allotment (execution-specs OutOfGasError).
    ".L" ++ tag ++ "_bn254_pairing:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 192\n" ++
    "  divu x22, x18, x16\n" ++
    "  li x16, 34000\n" ++
    "  mulhu x23, x22, x16\n" ++
    "  bnez x23, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  mul x16, x22, x16\n" ++
    "  li x23, 45000\n" ++
    "  add x16, x16, x23\n" ++
    "  bltu x16, x23, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bn254ChargeGateAsm tag ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 192\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_kfail\n" ++
    "  divu x22, x18, x16\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  mv a1, x22\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bn254_pairing\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccessBoolFromFrameAsm
      (tag ++ "_bn254_pairing_success") outOffsetOff outSizeOff precompileFrameBls12G1OutputOff ++
    -- BLAKE2F: exact 213-byte payload, then charge gas equal to the BE
    -- rounds field, then validate the final flag. The current runtime wrapper
    -- deterministic-fails, but the path is ready to expose the updated 64-byte
    -- state from h once a success-producing backend is available.
    ".L" ++ tag ++ "_blake2f:\n" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 213\n" ++
    -- Wrong length raises InvalidParameter (an ExceptionalHalt) BEFORE any gas
    -- charge: execution-specs zeroes the child frame's gas_left, so the whole
    -- EIP-150 child allotment is consumed. Burn it like the BLS handlers rather
    -- than falling through to the regular CALL descent (which would refund the
    -- forwarded gas and under-count block gas_used by the stipend).
    "  bne x16, x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_blake2f_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 213 ++
    precompileFrameAddi "x18" precompileFrameBls12G2InputOff ++
    "  lbu x16, 0(x18)\n" ++
    "  slli x16, x16, 24\n" ++
    "  lbu x17, 1(x18)\n" ++
    "  slli x17, x17, 16\n" ++
    "  or x16, x16, x17\n" ++
    "  lbu x17, 2(x18)\n" ++
    "  slli x17, x17, 8\n" ++
    "  or x16, x16, x17\n" ++
    "  lbu x17, 3(x18)\n" ++
    "  or x16, x16, x17\n" ++
    bn254ChargeGateAsm tag ++
    "  lbu x17, 212(x18)\n" ++
    "  li x22, 1\n" ++
    "  bltu x22, x17, .L" ++ tag ++ "_bn254_kfail\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  mv a0, x16\n" ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 4) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 68) ++
    precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 196) ++
    "  mv a4, x17\n" ++
    "  jal x1, zkvm_blake2f\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- value into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, 1f\n" ++
    precompileSuccess64FromFrameAsm
      (tag ++ "_blake2f_success") outOffsetOff outSizeOff (precompileFrameBls12G2InputOff + 4) ++
    -- KZG point evaluation: execution-specs rejects non-192-byte input before
    -- gas, then charges fixed 50000 gas before hash/proof validation.
    ".L" ++ tag ++ "_kzg_point_eval:\n" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 192\n" ++
    -- Wrong length raises InvalidParameter (an ExceptionalHalt) BEFORE any gas
    -- charge: execution-specs zeroes the child frame's gas_left, so the whole
    -- EIP-150 child allotment is consumed. Burn it like the BLS handlers rather
    -- than falling through to the regular CALL descent (which would refund the
    -- forwarded gas and under-count block gas_used by the stipend).
    "  bne x16, x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  li x16, 50000\n" ++
    bn254ChargeGateAsm tag ++
    stagePrecompileInputWindowAsm
      (tag ++ "_kzg_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 192 ++
    kzgVersionedHashGateAsm (".L" ++ tag ++ "_bn254_kfail") ++
    "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" (precompileFrameBls12G2InputOff + 96) ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 64) ++
    precompileFrameAddi "a3" (precompileFrameBls12G2InputOff + 144) ++
    precompileFrameAddi "a4" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_kzg_point_eval\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- value into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  beqz x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    precompileSuccessKzgPointEvalAsm
      (tag ++ "_kzg_point_eval_success") outOffsetOff outSizeOff ++
    -- P256VERIFY: execution-specs charges fixed gas before the exact length
    -- check. Invalid length and invalid signatures are successful precompile
    -- calls with empty returndata; backend EFAIL is precompile failure.
    ".L" ++ tag ++ "_p256verify:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    chargePrecompileGasConstWithAllotmentAsm tag 6900 "x16" "x17" ++
    "  ld x16, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 160\n" ++
    "  bne x16, x17, 12f\n" ++
    stagePrecompileInputWindowAsm
      (tag ++ "_p256verify_payload") inOffsetOff inSizeOff precompileFrameBls12G2InputOff 0 160 ++
    "  sb x0, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    precompileFrameAddi "a0" precompileFrameBls12G2InputOff ++
    precompileFrameAddi "a1" (precompileFrameBls12G2InputOff + 32) ++
    precompileFrameAddi "a2" (precompileFrameBls12G2InputOff + 96) ++
    precompileFrameAddi "a3" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_secp256r1_verify\n" ++
    -- a0 IS x10: stash the kernel status before restoring the saved
    -- value into x10 (the ecrecover-path landmine, #8721 stack notes).
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  bnez x16, 1f\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G2OutputOff ++ "(x15)\n" ++
    "  beqz x16, 12f\n" ++
    precompileSuccessBoolFromFrameAsm
      (tag ++ "_p256verify_success") outOffsetOff outSizeOff precompileFrameBls12G2OutputOff ++
    "12:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G1 ADD (0x0b): exact 256-byte input, fixed 375 gas charged
    -- from the EIP-150 child allotment, real accelerator-backed kernel on the
    -- raw EIP-2537 input. Invalid input (bad pad / coord >= p / off-curve) is
    -- a FAILED call that burns the allotment (execution-specs InvalidParameter).
    "13:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 256\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 375\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_g1_add\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    "  j .L" ++ tag ++ "_blsg1_out\n" ++
    -- BLS12-381 G1 MSM (0x0c): nonempty multiple-of-160 input, per-pair
    -- discounted gas (bls12_g1_msm_discount_table) charged from the child
    -- allotment, real double-and-add kernel with the REAL order-n subgroup
    -- check on every input point (the G1 cofactor is not 1). Invalid input
    -- burns the allotment.
    "14:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 160\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bls12MsmCostAsm tag 160 12000 519 "bls12_g1_msm_discount_table" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 160\n" ++
    "  divu a1, x18, x17\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_g1_msm\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- Shared G1 success tail (ADD + MSM): expand the compact 96-byte result
    -- into EIP-2537 returndata (16 zero pad + 48-byte coordinate, twice) at
    -- frame+16, then copy min(128, out_size) to caller memory.
    ".L" ++ tag ++ "_blsg1_out:\n" ++
    "  addi x18, x15, 16\n" ++
    "  li x22, 16\n" ++
    ".L" ++ tag ++ "_blsg1_pad1:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_pad1\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G1OutputOff ++
    "  li x22, 48\n" ++
    ".L" ++ tag ++ "_blsg1_cx:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_cx\n" ++
    "  li x22, 16\n" ++
    ".L" ++ tag ++ "_blsg1_pad2:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_pad2\n" ++
    "  li x22, 48\n" ++
    ".L" ++ tag ++ "_blsg1_cy:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, .L" ++ tag ++ "_blsg1_cy\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 128\n" ++
    "  bgeu x22, x23, .L" ++ tag ++ "_blsg1_outcap\n" ++
    "  mv x23, x22\n" ++
    ".L" ++ tag ++ "_blsg1_outcap:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    ".L" ++ tag ++ "_blsg1_copyout:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, .L" ++ tag ++ "_blsg1_copyout\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G2 ADD (0x0d): exact 512-byte input, fixed 600 gas charged
    -- from the EIP-150 child allotment, real software-Fp2 kernel (complex
    -- accelerators + Arith384Mod Fermat inverse) on the raw EIP-2537 input.
    -- Invalid input burns the allotment (execution-specs InvalidParameter).
    "15:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 512\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 600\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G2AddOutputOff ++
    "  jal x1, zkvm_bls12_g2_add\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2AddOutputOff ++
    "  li x23, 4\n" ++
    "20:\n" ++
    "  li x22, 16\n" ++
    "21:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  li x22, 48\n" ++
    "22:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 20b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 23f\n" ++
    "  mv x23, x22\n" ++
    "23:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "24:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 24b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 G2 MSM (0x0e): nonempty multiple-of-288 input, per-pair
    -- discounted gas (bls12_g2_msm_discount_table) charged from the child
    -- allotment, real software-Fp2 double-and-add kernel with the REAL
    -- order-n subgroup check on every input point. Invalid input burns the
    -- allotment.
    "16:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 288\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bls12MsmCostAsm tag 288 22500 524 "bls12_g2_msm_discount_table" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 288\n" ++
    "  divu a1, x18, x17\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_bls12_g2_msm\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2OutputOff ++
    "  li x23, 4\n" ++
    "20:\n" ++
    "  li x22, 16\n" ++
    "21:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 21b\n" ++
    "  li x22, 48\n" ++
    "22:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 22b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 20b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 23f\n" ++
    "  mv x23, x22\n" ++
    "23:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "24:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 24b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 pairing (0x0f): nonempty multiple-of-384 input, gas
    -- 32600*k + 37700 charged from the EIP-150 child allotment, real
    -- py_ecc-mirroring FQ12 Miller-loop kernel on the raw EIP-2537 input
    -- (decode + on-curve + REAL subgroup checks on both sides in-kernel).
    -- Invalid input burns the allotment.
    "17:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  beqz x18, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 384\n" ++
    "  remu x17, x18, x16\n" ++
    "  bnez x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 384\n" ++
    "  divu x17, x18, x16\n" ++
    "  li x16, 32600\n" ++
    "  mul x16, x17, x16\n" ++
    "  li x22, 32600\n" ++
    "  divu x22, x16, x22\n" ++
    "  bne x22, x17, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x22, 37700\n" ++
    "  add x16, x16, x22\n" ++
    "  bltu x16, x22, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    "  ld x18, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x17, 384\n" ++
    "  divu a1, x18, x17\n" ++
    precompileFrameAddi "a2" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_pairing\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 pairing returns a 32-byte boolean word: 31 zero bytes followed
    -- by the backend `verified` byte.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    "  sd x0, 32(x15)\n" ++
    "  sd x0, 40(x15)\n" ++
    "  lbu x16, " ++ toString precompileFrameBls12G1OutputOff ++ "(x15)\n" ++
    "  sb x16, 47(x15)\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 32\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 32\n" ++
    "  bgeu x22, x23, 22f\n" ++
    "  mv x23, x22\n" ++
    "22:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "23:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 23b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 map-Fp-to-G1: execution-specs requires exactly one
    -- 64-byte Fp field element; the compact 48-byte field payload starts
    -- after the 16-byte EIP-2537 zero pad.
    "18:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 64\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 5500\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G1OutputOff ++
    "  jal x1, zkvm_bls12_map_fp_to_g1\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g1_to_bytes`: each compact 48-byte coordinate is left-padded
    -- to a 64-byte big-endian field element.
    "  sd x0, 16(x15)\n" ++
    "  sd x0, 24(x15)\n" ++
    precompileFrameAddi "x17" precompileFrameBls12G1OutputOff ++
    "  addi x18, x15, 32\n" ++
    "  li x19, 48\n" ++
    "34:\n" ++
    "  lbu x16, 0(x17)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 34b\n" ++
    "  sd x0, 80(x15)\n" ++
    "  sd x0, 88(x15)\n" ++
    precompileFrameAddi "x17" (precompileFrameBls12G1OutputOff + 48) ++
    "  addi x18, x15, 96\n" ++
    "  li x19, 48\n" ++
    "35:\n" ++
    "  lbu x16, 0(x17)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x17, x17, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, -1\n" ++
    "  bnez x19, 35b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 128\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 128\n" ++
    "  bgeu x22, x23, 36f\n" ++
    "  mv x23, x22\n" ++
    "36:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "37:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 37b\n" ++
    "  j 7b\n" ++
    -- BLS12-381 map-Fp2-to-G2: execution-specs requires exactly one
    -- 128-byte Fp2 element. Project the two compact 48-byte Fp chunks into
    -- the G2-class compact input lane before calling the backend.
    "19:\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
    "  li x16, 128\n" ++
    "  bne x17, x16, .L" ++ tag ++ "_bn254_fail_allot\n" ++
    "  li x16, 23800\n" ++
    bn254ChargeGateAsm tag ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld x17, " ++ toString inOffsetOff ++ "(x12)\n" ++
    "  add a0, x13, x17\n" ++
    precompileFrameAddi "a1" precompileFrameBls12G2OutputOff ++
    "  jal x1, zkvm_bls12_map_fp2_to_g2\n" ++
    -- a0 IS x10: stash the kernel status before the saved-PC restore.
    "  mv x16, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  la x15, evm_precompile_frame\n" ++
    "  bnez x16, .L" ++ tag ++ "_bn254_kfail\n" ++
    -- EIP-2537 `g2_to_bytes`: each compact 48-byte FQ component is left-padded
    -- to a 64-byte big-endian field element.
    "  addi x18, x15, 16\n" ++
    precompileFrameAddi "x19" precompileFrameBls12G2OutputOff ++
    "  li x23, 4\n" ++
    "34:\n" ++
    "  li x22, 16\n" ++
    "35:\n" ++
    "  sb x0, 0(x18)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 35b\n" ++
    "  li x22, 48\n" ++
    "36:\n" ++
    "  lbu x16, 0(x19)\n" ++
    "  sb x16, 0(x18)\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x22, x22, -1\n" ++
    "  bnez x22, 36b\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 34b\n" ++
    "  li x16, 1\n" ++
    "  sd x16, 0(x15)\n" ++
    "  li x16, 256\n" ++
    "  sd x16, 8(x15)\n" ++
    "  ld x22, " ++ toString outSizeOff ++ "(x12)\n" ++
    "  li x23, 256\n" ++
    "  bgeu x22, x23, 37f\n" ++
    "  mv x23, x22\n" ++
    "37:\n" ++
    "  beqz x23, 7b\n" ++
    "  addi x18, x15, 16\n" ++
    "  ld x19, " ++ toString outOffsetOff ++ "(x12)\n" ++
    "  add x19, x13, x19\n" ++
    "38:\n" ++
    "  lbu x16, 0(x18)\n" ++
    "  sb x16, 0(x19)\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 38b\n" ++
    "  j 7b\n" ++
    ".L" ++ tag ++ "_nonprecompile_fallthrough:\n" ++
    "1:\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    fallThroughAsm

end EvmAsm.Codegen
