/-
  EvmAsm.Codegen.Programs.NoopHalt

  Terminating runtime opcode handlers split out of `Programs.Noop` to keep the
  mixed no-op/child-frame surface below the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Selfdestruct
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
      "  la a0, create_address_be\n  add a1, x13, x14\n  mv a2, x15\n" ++
      "  jal ra, create_record_code_effect\n" ++
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
    , preBody := stackUnderflowGuardAsm 1
    , body := []
    , tail := .custom selfdestructTailAsm } ]

end EvmAsm.Codegen
