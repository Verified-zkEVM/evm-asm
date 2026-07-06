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

/-- ADDMOD (0x08) handler body: the verified total three-way ADDMOD program
    inlined with `evm_mod_callable_v5`.

    Composition (mirrors `AddMod/ProgramTest.lean`'s canonical layout, whose
    `#guard` vectors execute exactly this program):
      - `evm_addmod_total 624 520 416 32`: 216 instr (864 B). The four
        interior `JAL .x1` MOD-call sites (bytes 244 / 348 / 452 / 836) all
        target the callable entry at byte 868.
      - skip-JAL `JAL .x0 +1416`: 1 instr (4 B) at byte 864; jumps past the
        inlined callable to the handler tail (1416 = 4 + 1412).
      - `evm_mod_callable_v5`: 353 instr (1412 B) at byte 868.

    This replaces the earlier hand-written `.Laddmod_*` label-based runtime
    tail, which (a) still called the buggy v4 MOD callable, and (b) carried a
    borrow-chain bug in its conditional-subtract path (`sub x5, x5, x11;
    sltu x11, x5, x11` tests the borrow *after* subtracting it, inverting the
    borrow whenever a limb difference is 0 or 1 with an incoming borrow).
    `evm_addmod_total` uses the verified `evm_sub` idiom and parks its carry
    scratch below the callable's own `F−160..F−8` scratch band, so no
    absolute-addressed scratch symbols are needed.

    Net `x12` advance: +64 on every branch (pops 3, pushes 1). -/
def evmAddmodComposedTotal : Program :=
  EvmAsm.Evm64.evm_addmod_total 624 520 416 32 ;;
  single (Instr.JAL .x0 (1416 : BitVec 21)) ;;
  EvmAsm.Evm64.evm_mod_callable_v5

/-- EXP (0x0a) handler body: the double-fixed verified EXP body inlined
    with `mul_callable`, mirroring `evmAddmodComposedTotal`.

    Uses the architecture-B **headroom** body
    (`evm_exp_..._fixed_fixed_headroom_canonical`), which fixes the
    stack-corruption bug `evm-asm-fjivz`: the prior `_fixed_fixed_canonical`
    body ran its squaring loop in place and marshalled the MUL factors into
    the *live* EVM stack words below the two operands (slots [2]/[3] at
    `x12+64..120`), clobbering caller data. The headroom body copies the
    operands into the slack below the live stack (`evm_stack_guard`, 512 B)
    and runs the loop there, leaving the live stack framed through untouched.
    The counter stays in callee-saved `x22` (not the `x20` of the proof-only
    `_headroom`), so the dispatcher's reserved `x20`/`x21` are preserved.

    Composition:
      - `evm_exp_..._fixed_fixed_headroom_canonical 200 92`: 102 instr (408 B).
        The two interior `JAL .x1` MUL-call sites target `mul_callable`. The
        operand-copy prologue shifts the loop body +72 bytes, but `mul_callable`
        shifts by the same +72, so the 200/92 offsets are unchanged.
      - skip-JAL `JAL .x0 +260`: 1 instr (4 B) at byte 408; jumps past the
        inlined callable to the handler tail (260 = 4 + 256).
      - `mul_callable`: 64 instr (256 B) at byte 412.

    Net `x12` advance: `exp_epilogue` does one `ADDI x12, x12, 32` (pops 2,
    pushes 1); the headroom operand-copy / pointer-frame moves net zero. -/
def evmExpComposed : Program :=
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_canonical
    (200 : BitVec 21) (92 : BitVec 21) ;;
  single (Instr.JAL .x0 (260 : BitVec 21)) ;;
  EvmAsm.Evm64.mul_callable

/-- Shared tail for the self-calling handlers (ADDMOD / EXP): their inner
    `JAL .x1` calls (into `evm_mod_callable_v5` / `mul_callable`) clobber
    `x1`, so restore the dispatch continuation into `x1` and `ret` (4ch8f.10.3
    callRegS contract) instead of `j .dispatch_loop`. The callables also use
    `x2` (= `sp`) as a general-purpose register, so restore the LP64
    helper-call stack pointer first (same `sp`-restore as `divModTail`). -/
private def selfCallingTail : HandlerTail :=
  .custom ("  mv x10, x14\n" ++
           "  la sp, lp64_sp_top\n" ++
           "  addi x10, x10, 1\n" ++
           dispatchContinueRet)

def selfCallingHandlers : List OpcodeHandlerSpec :=
  [ { label         := "h_ADDMOD"
      opcodes       := [0x08]
      preBody       := stackUnderflowGuardAsm 3 ++ "\n  mv x14, x10"
      body          := evmAddmodComposedTotal
      tail          := selfCallingTail }
  , { label         := "h_EXP"
      opcodes       := [0x0a]
      preBody       := stackUnderflowGuardAsm 2 ++ "\n" ++ expDynamicGasAsm ++ "  mv x14, x10\n  la x2, exp_scratch"
      body          := evmExpComposed
      tail          := selfCallingTail } ]

end EvmAsm.Codegen
