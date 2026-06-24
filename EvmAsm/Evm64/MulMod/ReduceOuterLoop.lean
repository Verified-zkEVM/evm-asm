/-
  EvmAsm.Evm64.MulMod.ReduceOuterLoop

  Outer eight-limb loop of the MULMOD 512-bit reducer. This file lifts the
  inner 64-bit bit-loop spec into the enclosing `evm_mulmod_reduce512_loop`
  code (the inner step sits at byte offset 8), and (later) composes the outer
  loop body and its eight-limb induction.
-/

import EvmAsm.Evm64.MulMod.ReduceBitLoop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- The inner reducer-step block sits at byte offset 8 within
    `evm_mulmod_reduce512_loop` (after `LD x17` and `ADDI x15`). -/
theorem evm_mulmod_reduce512_loop_inner_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_code (base + 8) a = some i →
      (CodeReq.ofProg base evm_mulmod_reduce512_loop) a = some i := by
  intro a i h
  unfold evm_mulmod_reduce512_inner_step_code at h
  refine CodeReq.ofProg_mono_subrange base
    [Instr.LD .x17 .x16 0, Instr.ADDI .x15 .x0 64]
    evm_mulmod_reduce512_inner_step
    [Instr.ADDI .x16 .x16 4088, Instr.ADDI .x18 .x18 4095,
      Instr.BNE .x18 .x0 (-272 : BitVec 13)]
    ?_ a i ?_
  · decide
  · exact h

/-- The inner 64-bit bit loop, lifted to the enclosing `reduce512_loop` code:
    it runs from byte offset 8 to byte offset 264 (where the pointer-advance
    instructions begin), folding the current product limb `w` into the
    remainder. -/
theorem evm_mulmod_reduce512_loop_bit_loop_spec_within
    (sp base w x19v x20v : Word) (r n : EvmWord) :
    cpsTripleWithin (64 * 64) (base + 8) (base + 8 + 256)
      (CodeReq.ofProg base evm_mulmod_reduce512_loop)
      (mulModReduceBitLoopPre sp w (BitVec.ofNat 64 64) x19v x20v r n)
      (mulModReduceBitLoopPost sp (mulModReduceStepN r n w 64) n) :=
  cpsTripleWithin_extend_code
    (hmono := evm_mulmod_reduce512_loop_inner_code_sub base)
    (h := evm_mulmod_reduce512_bit_loop_spec_within sp (base + 8) w x19v x20v r n)

end EvmAsm.Evm64
