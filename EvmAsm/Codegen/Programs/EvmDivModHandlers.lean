/-
  EvmAsm.Codegen.Programs.EvmDivModHandlers

  Dispatcher handlers for unsigned DIV and MOD.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmDivModWrappers

namespace EvmAsm.Codegen

-- The verified DIV/MOD body (`evm_div` / `evm_mod`) uses `x2` (= `sp`) as a
-- general-purpose working register for its multi-precision arithmetic (e.g.
-- `ld sp, -128(a2); jr sp` for the internal dispatch, and the bignum
-- multiply-subtract chain that overwrites `sp` with intermediate limbs). In the
-- dispatcher, `sp` is the LP64 helper-call stack pointer (= `lp64_sp_top`), so a
-- handler whose body clobbers it MUST restore it before returning to
-- `.dispatch_loop`, or the next helper-call prologue (`addi sp, sp, -N;
-- sd ra, 0(sp)` in `frame_return` / `h_SSTORE` / …) stores through a garbage
-- (often tiny / negative) `sp` and ziskemu faults (`mem.rs:593` invalid addr).
-- This is the same `sp`-restore that `expTail` (EvmSelfCallingHandlers.lean)
-- performs for the EXP body, which clobbers `x2` for the identical reason.
-- (No `la x2, exp_scratch` preBody is needed here: the DIV/MOD body only ever
-- treats `x2` as a value register — it never does `sp`-relative *stores* — so
-- it cannot scribble into the `lp64_stack` region the way EXP does.)
private def divModTail : HandlerTail :=
  .custom "  mv x10, x14\n  la sp, lp64_sp_top\n  addi x10, x10, 1\n  ret"

def divModHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_DIV"
      opcodes := [0x04]
      preBody := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10"
      body    := evmDivV6Patched
      tail    := divModTail }
  , { label   := "h_MOD"
      opcodes := [0x06]
      preBody := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10"
      body    := evmModPatched
      tail    := divModTail } ]

end EvmAsm.Codegen
