/-
  EvmAsm.Codegen.Programs.NoopHalt

  Terminating runtime opcode handlers split out of `Programs.Noop` to keep the
  mixed no-op/child-frame surface below the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- RETURN/REVERT output tail. Both read `offset_low` / `size_low` from the
    stack, keep the legacy `OUTPUT_ADDR[0..32]` return-data prefix and
    `halt_kind` at `OUTPUT_ADDR+32`, and expose a wider diagnostic return-data
    surface at `OUTPUT_ADDR+64/+72/+248`. -/
private def returnRevertTail (kind : Nat) (rollbackAsm : String := "")
    (depthAware : Bool := false) : String :=
  "  ld x14, 0(x12)\n" ++
  "  ld x15, 32(x12)\n" ++
  -- Depth-aware (guest only): a child frame's RETURN/REVERT returns to the parent
  -- via frame_return (success 1/0, returndata = child mem[offset..offset+size])
  -- instead of halting the guest. At depth 0 this is byte-identical (falls through
  -- to the original halt). REVERT rolls back the child's state before returning.
  (if depthAware then
    "  la t0, evm_call_depth\n" ++
    "  ld t0, 0(t0)\n" ++
    "  beqz t0, .Lrr_halt_" ++ toString kind ++ "\n" ++
    rollbackAsm ++
    -- .61.8.3.5.2 (.5b): a CREATE child frame (create_frame_flag[depth]=1, set by
    -- create_frame_descend) does NOT return a CALL result — on RETURN it deposits the
    -- returned bytes as the deployed code and pushes the DERIVED ADDRESS to the parent;
    -- on REVERT it pushes 0 (CREATE failed). A CALL frame uses frame_return (success +
    -- returndata). Clear the flag (frame-slot reuse). Inert until .5c wires the descent.
    "  la t1, create_frame_flag\n" ++
    "  slli t2, t0, 3\n" ++
    "  add t1, t1, t2\n" ++
    "  ld t3, 0(t1)\n" ++
    "  beqz t3, .Lrr_call_" ++ toString kind ++ "\n" ++
    "  sd x0, 0(t1)\n" ++
    (if kind == 2 then
      -- REVERT: CREATE failed -> push 0 (rollback already ran above).
      "  li a0, 0\n  li a1, 0\n  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      "  j .dispatch_loop\n"
     else
      -- RETURN: validity-gate child mem[x14..x14+x15] (the deployed code), record the
      -- code-effect (copies it into the log BEFORE the frame pop), pop via frame_return
      -- (push 0 placeholder), then overwrite the parent result slot (x12) with the
      -- derived address. create_deployed_code_valid/create_record_code_effect preserve
      -- x13 (a3 mem base) and x14/x15 (per #8629); the validity result (a0) is consumed
      -- by bnez before create_record_code_effect clobbers a0.
      "  add a0, x13, x14\n  mv a1, x15\n" ++
      "  jal ra, create_deployed_code_valid\n" ++
      "  bnez a0, .Lrr_crinv_" ++ toString kind ++ "\n" ++
      -- nxio8.7: charge code_hash_gas (keccak-per-word, REGULAR/GAS dim) = OPCODE_KECCACK256_PER_WORD(6)
      -- * ceil32(deployed_code_len)/32 = 6 * ((x15+31)>>5) words, spec amsterdam vm/interpreter.py:236-240
      -- charge_gas, BEFORE the state-gas charge ('regular before state' ordering). Simple charge_gas
      -- (no reservoir/spill): drain the child frame gas_left (568(x20)); OOG-fail the CREATE
      -- (-> .Lrr_crinv) if short. A valid block never OOGs at deposit -> no false-reject. x15 preserved.
      "  addi t0, x15, 31\n  srli t0, t0, 5\n" ++                  -- words = ceil32(len)/32
      "  li t1, 6\n  mul t0, t0, t1\n" ++                          -- code_hash_gas = 6 * words
      "  ld t1, 568(x20)\n  bltu t1, t0, .Lrr_crinv_" ++ toString kind ++ "\n" ++   -- gas_left < code_hash_gas -> OOG, CREATE fails
      "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++                   -- gas_left -= code_hash_gas
      -- nxio8.6: charge code-deposit STATE gas = deployed_code_len(x15) * COST_PER_STATE_BYTE(1530)
      -- (spec amsterdam vm/interpreter.py:241-242 charge_state_gas(evm, ulen(code)*1530), AFTER the
      -- 0xEF/MAX_CODE_SIZE validity gate just above, BEFORE the deposit). Mirrors the SSTORE
      -- charge_state_gas pattern (Storage.lean): drain the global evm_state_gas_left reservoir; spill
      -- the remainder into the child frame gas_left (568(x20) = child env, before frame_return); if
      -- both are short, OOG-FAIL the CREATE (consume all child gas, push 0 via .Lrr_crinv) -- a valid
      -- block never OOGs at deposit, so no false-reject. evm_state_gas_used += charge on the non-OOG
      -- paths (spec raises BEFORE state_gas_used += amount; gas.py:302-311). Previously DROPPED ->
      -- state gas under-counted -> EIP-7778/8037 state budget too lenient (false-accept on state-heavy
      -- creation blocks); this makes the exec state gas (bvgr_tx_exec_state_gas) spec-accurate.
      -- x13/x14/x15 preserved by create_deployed_code_valid (#8629) and untouched here (only t0-t3 +
      -- the child gas_left). x15 <= MAX_CODE_SIZE (0x8000) so x15*1530 cannot overflow u64.
      "  li t0, 1530\n  mul t0, x15, t0\n" ++
      "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
      "  bgeu t2, t0, .Lrr_csg_res_" ++ toString kind ++ "\n" ++
      "  sub t3, t0, t2\n  sd x0, 0(t1)\n" ++                                  -- reservoir short: spill = charge - reservoir; reservoir = 0
      "  ld t2, 568(x20)\n  bgeu t2, t3, .Lrr_csg_spill_" ++ toString kind ++ "\n" ++  -- child gas_left >= spill -> ok
      "  sd x0, 568(x20)\n  j .Lrr_crinv_" ++ toString kind ++ "\n" ++         -- OOG: consume all child gas, CREATE fails
      ".Lrr_csg_spill_" ++ toString kind ++ ":\n" ++
      "  sub t2, t2, t3\n  sd t2, 568(x20)\n  j .Lrr_csg_used_" ++ toString kind ++ "\n" ++
      ".Lrr_csg_res_" ++ toString kind ++ ":\n" ++
      "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++                                  -- reservoir covers it
      ".Lrr_csg_used_" ++ toString kind ++ ":\n" ++
      "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
      "  la a0, create_address_be\n  add a1, x13, x14\n  mv a2, x15\n" ++
      "  jal ra, create_record_code_effect\n" ++
      -- i3djw.2: record the created account's NON-STORAGE effect (pre absent 0/0; post
      -- nonce=1, balance=endowment). endowment = child env.CALLVALUE (x20+96), which
      -- call_frame_set_call_env stored as the LE stack value word, so reverse it to BE
      -- (read x20+127 down to x20+96) for the BE effect-log convention (matching i3djw.1).
      -- x20 = child env here (before frame_return restores the parent). a0/a2/a3 alias
      -- x10/x12/x13 -> saved/restored around record_nonstorage_effect. INERT until i3djw.3
      -- wires the comparator (and CREATE is self-contained-rejected until .8c-3).
      "  la t0, nse_create_post_bal\n  addi t1, x20, 127\n  li t2, 32\n" ++
      ".Lrr_crendow_" ++ toString kind ++ ":\n" ++
      "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .Lrr_crendow_" ++ toString kind ++ "\n" ++
      "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
      "  la a0, create_address_be\n  la a1, nse_zero_bal\n  la a2, nse_create_post_bal\n  li a3, 0\n  li a4, 1\n" ++
      "  jal ra, record_nonstorage_effect\n" ++
      "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
      "  li a0, 0\n  li a1, 0\n  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      "  la t1, create_address_be\n  addi t1, t1, 19\n  mv t2, x12\n  li t3, 20\n" ++
      ".Lrr_craddr_" ++ toString kind ++ ":\n" ++
      "  beqz t3, .Lrr_craddr_d_" ++ toString kind ++ "\n" ++
      "  lbu t4, 0(t1)\n  sb t4, 0(t2)\n  addi t1, t1, -1\n  addi t2, t2, 1\n  addi t3, t3, -1\n  j .Lrr_craddr_" ++ toString kind ++ "\n" ++
      ".Lrr_craddr_d_" ++ toString kind ++ ":\n" ++
      "  j .dispatch_loop\n" ++
      ".Lrr_crinv_" ++ toString kind ++ ":\n" ++
      "  li a0, 0\n  li a1, 0\n  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      "  j .dispatch_loop\n") ++
    ".Lrr_call_" ++ toString kind ++ ":\n" ++
    "  li a0, " ++ (if kind == 2 then "0" else "1") ++ "\n" ++
    "  add a1, x13, x14\n" ++
    "  mv a2, x15\n" ++
    "  jal ra, frame_return\n" ++
    "  j .dispatch_loop\n" ++
    ".Lrr_halt_" ++ toString kind ++ ":\n"
   else "") ++
  -- 8uld3.2.1a: when system_call_mode!=0, capture the top-level (depth-0) RETURN data
  -- (evm_memory[x14..x14+x15]) into system_call_returndata so an EIP-7002/7251 predeploy
  -- system call's return_data is recoverable. RETURN (kind 1) only; flag is 0 for normal
  -- txs so the halt path stays byte-identical. x13=mem base, x14=offset, x15=size (read-only).
  (if kind == 1 then
    "  la t0, system_call_mode\n  ld t0, 0(t0)\n  beqz t0, .Lrr_nocap_" ++ toString kind ++ "\n" ++
    "  li t1, 4096\n  bltu t1, x15, .Lrr_nocap_" ++ toString kind ++ "\n" ++   -- oversized -> skip (conservative)
    "  la t1, system_call_returndata_len\n  sd x15, 0(t1)\n" ++
    "  add t2, x13, x14\n  la t3, system_call_returndata\n  mv t4, x15\n" ++
    ".Lrr_capz_" ++ toString kind ++ ":\n" ++
    "  beqz t4, .Lrr_nocap_" ++ toString kind ++ "\n" ++
    "  lbu t5, 0(t2)\n  sb t5, 0(t3)\n  addi t2, t2, 1\n  addi t3, t3, 1\n  addi t4, t4, -1\n  j .Lrr_capz_" ++ toString kind ++ "\n" ++
    ".Lrr_nocap_" ++ toString kind ++ ":\n"
   else "") ++
  "  li x16, 0xa0010000\n" ++
  "  sd x0, 0(x16)\n" ++
  "  sd x0, 8(x16)\n" ++
  "  sd x0, 16(x16)\n" ++
  "  sd x0, 24(x16)\n" ++
  "  addi x19, x16, 72\n" ++
  "  li x21, 22\n" ++
  "1:\n" ++
  "  beqz x21, 2f\n" ++
  "  sd x0, 0(x19)\n" ++
  "  addi x19, x19, 8\n" ++
  "  addi x21, x21, -1\n" ++
  "  j 1b\n" ++
  "2:\n" ++
  "  mv x21, x15\n" ++
  "  li x22, 176\n" ++
  "  bgeu x22, x21, 3f\n" ++
  "  mv x21, x22\n" ++
  "3:\n" ++
  "  sd x15, 64(x16)\n" ++
  "  sd x21, 248(x16)\n" ++
  "  la x17, evm_memory\n" ++
  "  add x17, x17, x14\n" ++
  "  addi x19, x16, 72\n" ++
  "  mv x22, x21\n" ++
  "4:\n" ++
  "  beqz x22, 5f\n" ++
  "  lbu x23, 0(x17)\n" ++
  "  sb x23, 0(x19)\n" ++
  "  addi x17, x17, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j 4b\n" ++
  "5:\n" ++
  "  la x17, evm_memory\n" ++
  "  add x17, x17, x14\n" ++
  "  mv x22, x15\n" ++
  "  li x21, 32\n" ++
  "  bgeu x21, x22, 6f\n" ++
  "  mv x22, x21\n" ++
  "6:\n" ++
  "  mv x19, x16\n" ++
  "7:\n" ++
  "  beqz x22, 8f\n" ++
  "  lbu x23, 0(x17)\n" ++
  "  sb x23, 0(x19)\n" ++
  "  addi x17, x17, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j 7b\n" ++
  "8:\n" ++
  s!"  li x17, {kind}\n" ++
  "  sd x17, 32(x16)\n" ++
  rollbackAsm ++
  "  j .exit_no_epilogue"

/-- Stage the popped SELFDESTRUCT beneficiary for later EIP-6780 state work. -/
private def selfdestructTailAsm : String :=
  "  la x14, evm_selfdestruct_beneficiary\n" ++
  "  mv x15, x14\n" ++
  "  li x16, 4\n" ++
  ".L_selfdestruct_zero_scratch:\n" ++
  "  sd x0, 0(x15)\n" ++
  "  addi x15, x15, 8\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, .L_selfdestruct_zero_scratch\n" ++
  "  addi x15, x12, 19\n" ++
  "  li x16, 20\n" ++
  ".L_selfdestruct_copy_beneficiary:\n" ++
  "  lbu x17, 0(x15)\n" ++
  "  sb x17, 0(x14)\n" ++
  "  addi x15, x15, -1\n" ++
  "  addi x14, x14, 1\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, .L_selfdestruct_copy_beneficiary\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  -- SELFDESTRUCT charges COLD_ACCOUNT_ACCESS (2600) for a COLD beneficiary and 0
  -- when warm (spec amsterdam vm/instructions/system.py:646-650; unlike CALL, it
  -- adds NO warm-access cost). runtime_access_account_charge only debited the
  -- 2500 cold delta (its 100 floor presumes a dispatcher account-opcode floor that
  -- SELFDESTRUCT's 5000 base lacks), so add the missing 100 ONLY on the cold path
  -- (helper a0==1) to reach the full 2600; a warm beneficiary stays at 0. Without
  -- this the cold-beneficiary SELFDESTRUCT under-charged regular gas by 100,
  -- corrupting the type-4 receipt cumulative (bv_fail=53). Check a0 before the
  -- x10 restore clobbers it.
  "  beqz a0, .L_selfdestruct_access_floor_done\n" ++
  "  ld t0, 568(x20)\n" ++
  "  li t1, 100\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
  ".L_selfdestruct_access_floor_done:\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  selfdestructNewAccountSurchargeAsm ++
  selfdestructLoadAccountInputsAsm ++
  selfdestructBalanceTransferRuntimeAsm ++
  selfdestructEip7708LogRuntimeAsm ++
  "  la x14, evm_selfdestruct_staged\n" ++
  "  li x15, 1\n" ++
  "  sd x15, 0(x14)\n" ++
  selfdestructBeneficiaryNonstorageAsm ++
  "  addi x12, x12, 32\n" ++
  "  j .exit_selfdestruct"

/-- M18 / M23 / M31 EVM-terminating opcodes. `depthAware` makes RETURN/REVERT
    return to the parent frame (via `frame_return`) when `evm_call_depth > 0`
    instead of halting — used by the call-frame guest registry; the standalone
    dispatch probes pass `false` (byte-identical halt, no `frame_return` link). -/
def haltHandlers (depthAware : Bool) : List OpcodeHandlerSpec :=
  [ { label   := "h_RETURN"
    , opcodes := [0xf3]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 returnRevertMemoryGasAsm "return"
    , body    := []
    , tail    := .custom (returnRevertTail 1 "" depthAware) }
  , { label   := "h_REVERT"
    , opcodes := [0xfd]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 returnRevertMemoryGasAsm "revert"
    , body    := []
    , tail    := .custom <|
        returnRevertTail 2
          ("  ld x17, 456(x20)\n" ++
           "  sd x17, 448(x20)\n" ++
           "  sd x0, 464(x20)\n" ++
           "  ld x17, 480(x20)\n" ++
           "  sd x17, 472(x20)\n") depthAware }
  , { label := "h_INVALID", opcodes := [0xfe]
    , body := []
    , tail := .custom "  j .exit_invalid_op" }
  , { label := "h_SELFDESTRUCT", opcodes := [0xff]
    , preBody := stackUnderflowGuardAsm 1 ++ "\n" ++ staticContextWriteGuardAsm
    , body := []
    , tail := .custom selfdestructTailAsm } ]

end EvmAsm.Codegen
