/-
  EvmAsm.Codegen.Programs.ExpProperty

  Property-test harness for the EXP opcode (`evm_exp_from_input`).

  Lifted out of `Programs/Evm.lean` to stay within the file-size cap
  (see `Programs.lean` §File-size guard). Uses the EXP body defined in
  `EvmAsm.Evm64.Exp.Program` and the callable MUL shim from
  `EvmAsm.Evm64.Multiply.Callable`.

  Uses the corrected `_fixed_fixed` EXP body: the per-limb bit counter
  moved from `x6` (which `mul_callable` clobbers) to callee-saved `x22`.
  The earlier `_fixed` body had two bugs — (1) the `x6` counter clobber
  above, and (2) `exp_epilogue` falling straight through into the
  appended `mul_callable` (it has no trailing jump). Both are fixed here:
  `_fixed_fixed` repairs (1) and the skip-JAL after the body repairs (2).
  `scripts/codegen-evm_exp-property-check.sh` now validates random
  `(base, exponent)` pairs against Python's `pow(base, exp, 2**256)`.
-/

import EvmAsm.Codegen.Programs.EvmBasic
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Multiply.Callable

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## evm_exp_from_input — property-test harness

    Standalone EXP computation using prover-supplied operands. Same
    input/output conventions as `evm_div_from_input`:
    - ziskemu `-i <file>` payload: 8-byte LE length (= 64) followed by
      32 bytes of base (LE limbs) and 32 bytes of exponent (LE limbs).
    - First 32 bytes of `OUTPUT_ADDR`: the LE result base^exp mod 2^256.

    Memory layout:
      x2  → exp_sp_scratch     : 32 B  (result accumulator at sp+0..31)
      x12 → operands_ram       : 128 B
                                  +0..31   base
                                  +32..63  exponent (overwritten by result)
      below x12: exp_headroom_slack : 128 B (operands_ram-128 .. operands_ram-1)
                  — the architecture-B loop frame. The headroom body copies
                  both operands here (`x12-128..-72`) and runs the squaring
                  loop at `x12_loop = x12-64`, so its MUL scratch lands in the
                  slack instead of clobbering caller data. Mirrors the
                  dispatcher's `evm_stack_guard` (512 B) below the live stack.

    A 4-byte skip-JAL sits between the 408-byte headroom EXP body and the
    inlined `mul_callable`, so the two interior MUL-call offsets are **200/92**
    (`mul_callable` starts at body byte 412; the operand-copy prologue shifts
    both the JAL sites and `mul_callable` by +72, so the offsets match the
    non-headroom `_fixed_fixed` body's 200/92). The skip-JAL (`JAL x0 +260`)
    carries the loop-exit fall-through past `mul_callable` to `evmAddEpilogue`,
    instead of running straight into the callable. Mirrors `evmExpComposed` in
    `Programs/EvmSelfCallingHandlers.lean` — same headroom body, so this
    property test gates the dispatched EXP code's arithmetic. -/

def evm_exp_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_fixed_headroom_canonical
    (200 : BitVec 21) (92 : BitVec 21) ++
  (single (Instr.JAL .x0 (260 : BitVec 21))) ++
  EvmAsm.Evm64.mul_callable ++
  evmAddEpilogue

def evmExpFromInputPrologue : String :=
  "  la x2, exp_sp_scratch\n" ++
  "  la x12, operands_ram"

def evmExpFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "exp_sp_scratch:\n" ++
  "  .zero 32\n" ++
  -- Architecture-B headroom slack: the 128 bytes immediately *below*
  -- `operands_ram`, where the EXP loop frame and its MUL scratch live
  -- (`x12-128 .. x12-1`). Placed adjacent-below so `operands_ram-128`
  -- resolves to `exp_headroom_slack`. Mirrors `evm_stack_guard` in the
  -- runtime dispatcher.
  ".balign 8\n" ++
  "exp_headroom_slack:\n" ++
  "  .zero 128\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 128"

def evmExpFromInputUnit : BuildUnit := {
  body        := evm_exp_from_input
  prologueAsm := evmExpFromInputPrologue
  dataAsm     := evmExpFromInputDataSection
}

end EvmAsm.Codegen
