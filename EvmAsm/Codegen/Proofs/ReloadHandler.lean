/-
  EvmAsm.Codegen.Proofs.ReloadHandler

  Handler-level lift infrastructure for EVM opcode bodies that CLOBBER the
  dispatcher's EVM code pointer `x10` (Multiply, SignExtend, Byte, AddMod,
  SDiv, SMod, Push). Unlike the `cleanRetHandler` (which advances the
  surviving `x10`), these bodies need `x10` saved before the body and reloaded
  from the saved register after, before the advance-and-return tail.

  This file provides the foundational, kernel-checked pieces; the full
  `reloadRetHandlerSpec` lift (composing the five pieces below, mirroring
  `cleanRetHandlerSpec` in HandlerSpecs.lean) is the remaining step — see the
  module note at the bottom.
-/

import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Evm64 (cc_ret)

/-- The save/reload handler ABI: save the EVM code pointer `x10` into `save`,
    run the (x10-clobbering) `body`, reload `x10` from `save`, advance by `n`
    bytes, and return via `cc_ret`. The dual of `cleanRetHandlerProgram` for
    x10-clobbering bodies. -/
def saveReloadHandlerProgram (body : Program) (n : BitVec 12) (save : Reg) : Program :=
  MV save .x10 ;; body ;; MV .x10 save ;; (Rv64.ADDI .x10 .x10 n) ;; cc_ret

theorem saveReloadHandlerProgram_length (body : Program) (n : BitVec 12) (save : Reg) :
    (saveReloadHandlerProgram body n save).length = body.length + 4 := by
  simp only [saveReloadHandlerProgram, seq, MV, Rv64.ADDI, cc_ret, JALR, single,
    Program.length_append, List.length_cons, List.length_nil]
  omega

/-- `MV rd rs` consuming a *don't-care* (owned) destination value — the novel
    step in the reload tail: the reloaded `x10` discards the body's garbage
    value. Built directly from `mv_spec_within` via the regOwn-elimination
    rule `cpsTripleWithin_of_forall_regIs_to_regOwn`. This is the piece that
    resolves the `regOwn .x10` in an x10-clobbering body's postcondition
    (e.g. `evmMulStackPost`). -/
theorem mv_dst_regOwn_spec_within (rd rs : Reg) (v : Word) (addr : Word)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MV rd rs))
      ((rs ↦ᵣ v) ** regOwn rd)
      ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn
    (fun vOld => mv_spec_within rd rs v vOld addr hrd_ne_x0)

/-
  ## Remaining step: `reloadRetHandlerSpec`

  With the pieces above, the full lift composes (mirroring `cleanRetHandlerSpec`,
  HandlerSpecs.lean:95-260, extended from 3 to 5 sub-blocks):

    given  h_body : cpsTripleWithin nSteps (base+4) ((base+4) + fourTimes nSteps)
                      (ofProg (base+4) body)
                      (R ** (.x10 ↦ᵣ x10_init)) (S ** regOwn .x10)
    derive cpsTripleWithin (nSteps+4) base (x1_init &&& ~~~1)
             (ofProg base (saveReloadHandlerProgram body n save))
             (R ** (.x10 ↦ᵣ x10_init) ** (.save ↦ᵣ s_init) ** (.x1 ↦ᵣ x1_init))
             (S ** (.x10 ↦ᵣ (x10_init + signExtend12 n)) ** (.save ↦ᵣ x10_init)
                ** (.x1 ↦ᵣ x1_init))

  Five sub-blocks: (1) `MV save x10` @ base, (2) body @ base+4, (3)
  `mv_dst_regOwn_spec_within .x10 save` @ base+4+4·len (consumes regOwn .x10),
  (4) `ADDI x10 x10 n` @ base+8+4·len, (5) `cc_ret` @ base+12+4·len. Compose
  with `cpsTripleWithin_seq` + per-pair `CodeReq.Disjoint`; an inter-piece
  `cpsTripleWithin_weaken`/`xperm` is needed between (1) and (2) (x10 moves
  from being adjacent to `save` to adjacent to `R`). Apply to Multiply by
  permuting `evm_mul_stack_spec_within`'s P into `R ** (.x10 ↦ᵣ v10)` form
  (v10 := x10_init) and Q (= `evmMulStackPost` which carries `regOwn .x10`)
  into `S ** regOwn .x10`.
-/

end EvmAsm.Codegen.Proofs
