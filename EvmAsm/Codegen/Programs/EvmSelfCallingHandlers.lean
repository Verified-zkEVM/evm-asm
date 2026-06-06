/-
  EvmAsm.Codegen.Programs.EvmSelfCallingHandlers

  Dispatcher handlers for self-calling ADDMOD and EXP.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Multiply.Callable
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## M10 self-calling opcode handlers: ADDMOD (0x08) and EXP (0x0a) -/

/-- Runtime ADDMOD handler body for the dispatcher.

    The proof-facing `evm_addmod` skeleton still only reduces the truncated
    low 256-bit sum. The dispatcher needs total EVM behavior now, so this
    raw handler uses assembler labels for the internal calls and handles the
    carry-out path empirically:

      * if `N = 0`, write zero and advance by one stack word;
      * if the ADD carry is zero, reduce the truncated sum with MOD;
      * if the ADD carry is one, compute `m = 2^256 mod N`, reduce the
        truncated sum first, add `m`, then perform the single conditional
        subtract required because both addends are already `< N`.

    The carry helper uses `addmod_runtime_scratch` for the extra callable MOD
    frames so temporary reduction state cannot alias deeper live EVM stack
    words. This wrapper exists only to avoid brittle
    hand-counted JAL offsets in the runtime dispatcher while the verified
    top-level ADDMOD assembly catches up. -/
private def evmAddmodRuntimeTail : HandlerTail :=
  .custom <| String.intercalate "\n" [
    emitProgram EvmAsm.Evm64.evm_addmod_prologue,
    emitProgram EvmAsm.Evm64.evm_addmod_phase1_carry,
    "  ld x6, 32(x12)\n  ld x5, 40(x12)\n  or x6, x6, x5\n  ld x5, 48(x12)\n  or x6, x6, x5\n  ld x5, 56(x12)\n  or x6, x6, x5\n  beq x6, x0, .Laddmod_zero\n  beq x7, x0, .Laddmod_no_carry\n  la x16, addmod_saved_stack_ptr\n  sd x12, 0(x16)\n  la x15, addmod_runtime_scratch\n  addi x5, x0, -1\n  sd x5, 0(x15)\n  sd x5, 8(x15)\n  sd x5, 16(x15)\n  sd x5, 24(x15)\n  ld x5, 32(x12)\n  sd x5, 32(x15)\n  ld x5, 40(x12)\n  sd x5, 40(x15)\n  ld x5, 48(x12)\n  sd x5, 48(x15)\n  ld x5, 56(x12)\n  sd x5, 56(x15)\n  mv x12, x15\n  jal x1, .Laddmod_mod_callable\n  la x16, addmod_saved_stack_ptr\n  ld x12, 0(x16)\n  la x15, addmod_runtime_scratch\n  ld x5, 32(x15)\n  addi x6, x5, 1\n  sltiu x7, x6, 1\n  sd x6, 64(x15)\n  ld x5, 40(x15)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 72(x15)\n  ld x5, 48(x15)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 80(x15)\n  ld x5, 56(x15)\n  add x6, x5, x7\n  sltu x7, x6, x7\n  sd x6, 88(x15)\n  ld x5, 32(x12)\n  sd x5, 96(x15)\n  ld x5, 40(x12)\n  sd x5, 104(x15)\n  ld x5, 48(x12)\n  sd x5, 112(x15)\n  ld x5, 56(x12)\n  sd x5, 120(x15)\n  addi x12, x15, 64\n  jal x1, .Laddmod_mod_callable\n  la x16, addmod_saved_stack_ptr\n  ld x12, 0(x16)\n  la x15, addmod_runtime_scratch\n  ld x5, 32(x12)\n  sd x5, 64(x12)\n  ld x5, 40(x12)\n  sd x5, 72(x12)\n  ld x5, 48(x12)\n  sd x5, 80(x12)\n  ld x5, 56(x12)\n  sd x5, 88(x12)\n  jal x1, .Laddmod_mod_callable\n  addi x12, x12, -32\n  ld x5, 32(x12)\n  sd x5, 0(x12)\n  ld x5, 40(x12)\n  sd x5, 8(x12)\n  ld x5, 48(x12)\n  sd x5, 16(x12)\n  ld x5, 56(x12)\n  sd x5, 24(x12)\n  la x15, addmod_runtime_scratch\n  ld x5, 96(x15)\n  sd x5, 32(x12)\n  ld x5, 104(x15)\n  sd x5, 40(x12)\n  ld x5, 112(x15)\n  sd x5, 48(x12)\n  ld x5, 120(x15)\n  sd x5, 56(x12)",
    emitProgram EvmAsm.Evm64.evm_add,
    "  bne x5, x0, .Laddmod_sub_n\n  ld x6, 24(x12)\n  ld x7, 56(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 16(x12)\n  ld x7, 48(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 8(x12)\n  ld x7, 40(x12)\n  bltu x7, x6, .Laddmod_sub_n\n  bltu x6, x7, .Laddmod_done\n  ld x6, 0(x12)\n  ld x7, 32(x12)\n  bltu x6, x7, .Laddmod_done\n.Laddmod_sub_n:\n  ld x6, 0(x12)\n  ld x7, 32(x12)\n  sub x5, x6, x7\n  sltu x11, x6, x7\n  sd x5, 0(x12)\n  ld x6, 8(x12)\n  ld x7, 40(x12)\n  sub x5, x6, x7\n  sltu x10, x6, x7\n  sub x5, x5, x11\n  sltu x11, x5, x11\n  or x11, x10, x11\n  sd x5, 8(x12)\n  ld x6, 16(x12)\n  ld x7, 48(x12)\n  sub x5, x6, x7\n  sltu x10, x6, x7\n  sub x5, x5, x11\n  sltu x11, x5, x11\n  or x11, x10, x11\n  sd x5, 16(x12)\n  ld x6, 24(x12)\n  ld x7, 56(x12)\n  sub x5, x6, x7\n  sub x5, x5, x11\n  sd x5, 24(x12)\n  j .Laddmod_done\n.Laddmod_no_carry:\n  jal x1, .Laddmod_mod_callable\n  j .Laddmod_done\n.Laddmod_zero:",
    emitProgram EvmAsm.Evm64.evm_addmod_phase2_zero_path,
    emitProgram EvmAsm.Evm64.evm_addmod_epilogue,
    ".Laddmod_done:\n  mv x10, x14\n  addi x10, x10, 1\n  j .dispatch_loop\n.Laddmod_mod_callable:",
    emitProgram EvmAsm.Evm64.evm_mod_callable_v4]

/-- Runtime ADDMOD handler assembly. Supports the no-carry lane by reusing
    `evmAddmodComposed`'s snippets, but rejects carry-out sums explicitly.
    The full ADDMOD semantics need 257-bit reduction `(c * 2^256 + r) mod N`;
    until that lands, `x7 != 0` is an unsupported development halt
    (`halt_kind = 3`) rather than a false successful low-256-bit result. -/
private def addmodRuntimeAsm : String :=
  "  mv x14, x10\n" ++
  emitProgram EvmAsm.Evm64.evm_addmod_prologue ++ "\n" ++
  emitProgram EvmAsm.Evm64.evm_addmod_phase1_carry ++ "\n" ++
  "  bnez x7, .exit_invalid_op\n" ++
  emitProgram (EvmAsm.Evm64.evm_addmod_phase2_reduce 8) ++ "\n" ++
  emitProgram (single (Instr.JAL .x0 (1376 : BitVec 21))) ++ "\n" ++
  emitProgram EvmAsm.Evm64.evm_mod_callable_v4 ++ "\n" ++
  "  mv x10, x14\n" ++
  "  addi x10, x10, 1\n" ++
  "  j .dispatch_loop"

/-- EXP (0x0a) handler body: the double-fixed verified EXP body inlined
    with `mul_callable`, mirroring `evmAddmodComposed`.

    Composition:
      - `evm_exp_..._fixed_fixed_canonical 200 92`: 84 instr (336 B). The
        two interior `JAL .x1` MUL-call sites target `mul_callable`.
      - skip-JAL `JAL .x0 +260`: 1 instr (4 B) at byte 336; jumps past
        the inlined callable to the handler tail (260 = 4 + 256).
      - `mul_callable`: 64 instr (256 B) at byte 340.

    Net `x12` advance: `exp_epilogue` does one `ADDI x12, x12, 32` (pops 2,
    pushes 1); the per-iteration call marshal/un-marshal nets zero. -/
def evmExpComposed : Program :=
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_fixed_canonical
    (200 : BitVec 21) (92 : BitVec 21) ;;
  single (Instr.JAL .x0 (260 : BitVec 21)) ;;
  EvmAsm.Evm64.mul_callable

/-- Tail for EXP (0x0a): the inner `JAL .x1` into `mul_callable` clobbers
    `x1`, so `ret` would jump to garbage. Restore the LP64 stack pointer
    that h_EXP's `preBody` repointed at `exp_scratch`, then dispatch again. -/
private def expTail : HandlerTail :=
  .custom ("  mv x10, x14\n" ++
           "  la sp, lp64_sp_top\n" ++
           "  addi x10, x10, 1\n" ++
           "  j .dispatch_loop")

def selfCallingHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_ADDMOD"
      opcodes       := [0x08]
      preBody       := stackUnderflowGuardAsm 3 ++ "\n  mv x14, x10"
      body          := []
      tail          := evmAddmodRuntimeTail }
  , { label         := "h_EXP"
      opcodes       := [0x0a]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n" ++ expDynamicGasAsm ++ "  mv x14, x10\n  la x2, exp_scratch"
      body          := evmExpComposed
      tail          := expTail } ]

end EvmAsm.Codegen
