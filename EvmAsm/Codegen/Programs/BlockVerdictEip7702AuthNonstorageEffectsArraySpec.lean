/-
  Whole-program caller contract for the 66-instruction
  `block_verdict_eip7702_auth_nonstorage_effects_array` accessor.

  `blockVerdictEip7702AuthNonstorageEffectsArray_prog` (defined in
  `TxIntrinsicStateGas.lean`) iterates over an SSZ transaction array and, for
  each transaction slice, calls the per-tx worker
  `eip7702_auth_nonstorage_effects`, which appends the EIP-7702 nonce-only
  non-storage effect for every successfully authorized authority. The array
  driver always returns `a0 = 0` (the per-tx worker is fail-open in the
  effect-recording sense; real failures are surfaced through the effect log /
  overflow cells, not the return code).

  Structure (mirrors the ChainValidate `*Array` triad):
    * prologue (instrs 0..17): save 10 callee-saved regs, move args into
      s-regs, `li x5, 4`;
    * descriptor validation: `bgv_u32le` reads the u32 element count, alignment
      / bounds guards, `x21 := count`;
    * loop over `x22 ∈ [0, count)`: two `bgv_u32le` reads compute the tx slice
      `[start, end)`, then `jal eip7702_auth_nonstorage_effects(slice_ptr,
      slice_len, x19, x20, x24)`; `x22 += 1`;
    * epilogue: restore, `a0 := 0`, return.

  Callees:
    * `bgv_u32le` — proven leaf `BalGasValidSAsm.bgvU32leFn` (spec
      `bgvU32leFn_spec`): `a0 := leU32 (bytes@a0) 0`.
    * `eip7702_auth_nonstorage_effects` — string leaf, not yet Program-form;
      its contract enters this proof as an ASSUMED leaf spec (discharged once
      that worker is converted + proven; interface aligned with the proof lead).

  NOTE: this file currently establishes the convention-independent foundation
  (base, program, code region, length). The prologue block, loop invariant,
  three-way post, iteration lemma, fuel induction and top-level
  `block_verdict_eip7702_auth_nonstorage_effects_array_spec_within` follow the
  ChainValidateBlobGasMultiple{Spec,Loop,LoopClose} template.
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.BalGasValidSAsm
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen.BlockVerdictEip7702AuthNonstorageEffectsArraySpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## Base address and linked code -/

/-- Accessor base address. -/
abbrev D : Word := (GuestAddrs.block_verdict_eip7702_auth_nonstorage_effects_array : Word)

/-- The accessor's own program. -/
abbrev bvteanseProg : Program :=
  EvmAsm.Codegen.blockVerdictEip7702AuthNonstorageEffectsArray_prog

theorem bvteanse_length : bvteanseProg.length = 66 := by decide

/-- The accessor's re-emitted instructions at its base. -/
def bvteanseCode : CodeReq := CodeReq.ofProg D bvteanseProg

/-! ## Prologue (instructions 0..17): save 10 callee-saved regs, move args, `li x5,4`

    Straight-line, convention-independent: `addi sp,sp,-88`; ten `sd`s spilling
    `x1,x8,x9,x18,x19,x20,x21,x22,x23,x24`; six `mv`s loading the ABI args into
    `x8,x9,x18,x19,x20,x24`; `li x5,4`. Exit at `D+72` (before the descriptor
    `bltu`). -/
set_option maxRecDepth 8000 in
theorem bvteansePrologue
    (sp0 spC raIn a0 a1 a2 a3 a4 a5
      cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 old5 : Word)
    (hspC : spC = sp0 + signExtend12 (-88 : BitVec 12)) :
    cpsTripleWithin 18 D (D + 72) bvteanseCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ cs0) ** (.x9 ↦ᵣ cs1) **
        (.x18 ↦ᵣ cs2) ** (.x19 ↦ᵣ cs3) ** (.x20 ↦ᵣ cs4) ** (.x21 ↦ᵣ cs5) **
        (.x22 ↦ᵣ cs6) ** (.x23 ↦ᵣ cs7) ** (.x24 ↦ᵣ cs8) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) ** (.x15 ↦ᵣ a5) ** (.x5 ↦ᵣ old5) ** (.x0 ↦ᵣ (0 : Word)) **
        memOwn spC ** memOwn (spC + 8) ** memOwn (spC + 16) ** memOwn (spC + 24) **
        memOwn (spC + 32) ** memOwn (spC + 40) ** memOwn (spC + 48) **
        memOwn (spC + 56) ** memOwn (spC + 64) ** memOwn (spC + 72))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ raIn) ** (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) **
        (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) ** (.x20 ↦ᵣ a4) ** (.x21 ↦ᵣ cs5) **
        (.x22 ↦ᵣ cs6) ** (.x23 ↦ᵣ cs7) ** (.x24 ↦ᵣ a5) **
        (.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) ** (.x15 ↦ᵣ a5) ** (.x5 ↦ᵣ (4 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (spC ↦ₘ raIn) ** ((spC + 8) ↦ₘ cs0) ** ((spC + 16) ↦ₘ cs1) **
        ((spC + 24) ↦ₘ cs2) ** ((spC + 32) ↦ₘ cs3) ** ((spC + 40) ↦ₘ cs4) **
        ((spC + 48) ↦ₘ cs5) ** ((spC + 56) ↦ₘ cs6) ** ((spC + 64) ↦ₘ cs7) **
        ((spC + 72) ↦ₘ cs8)) := by
  subst hspC
  have h0 := addi_spec_gen_same_within .x2 sp0 (-88 : BitVec 12) D (by decide)
  have h1 := sd_spec_gen_own_within .x2 .x1
    (sp0 + signExtend12 (-88 : BitVec 12)) raIn (0 : BitVec 12) (D + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show (sp0 + signExtend12 (-88 : BitVec 12)) + (0 : Word)
      = sp0 + signExtend12 (-88 : BitVec 12) from by bv_omega] at h1
  have h2 := sd_spec_gen_own_within .x2 .x8
    (sp0 + signExtend12 (-88 : BitVec 12)) cs0 (8 : BitVec 12) (D + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at h2
  have h3 := sd_spec_gen_own_within .x2 .x9
    (sp0 + signExtend12 (-88 : BitVec 12)) cs1 (16 : BitVec 12) (D + 12)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at h3
  have h4 := sd_spec_gen_own_within .x2 .x18
    (sp0 + signExtend12 (-88 : BitVec 12)) cs2 (24 : BitVec 12) (D + 16)
  rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide] at h4
  have h5 := sd_spec_gen_own_within .x2 .x19
    (sp0 + signExtend12 (-88 : BitVec 12)) cs3 (32 : BitVec 12) (D + 20)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide] at h5
  have h6 := sd_spec_gen_own_within .x2 .x20
    (sp0 + signExtend12 (-88 : BitVec 12)) cs4 (40 : BitVec 12) (D + 24)
  rw [show signExtend12 (40 : BitVec 12) = (40 : Word) from by decide] at h6
  have h7 := sd_spec_gen_own_within .x2 .x21
    (sp0 + signExtend12 (-88 : BitVec 12)) cs5 (48 : BitVec 12) (D + 28)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide] at h7
  have h8 := sd_spec_gen_own_within .x2 .x22
    (sp0 + signExtend12 (-88 : BitVec 12)) cs6 (56 : BitVec 12) (D + 32)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide] at h8
  have h9 := sd_spec_gen_own_within .x2 .x23
    (sp0 + signExtend12 (-88 : BitVec 12)) cs7 (64 : BitVec 12) (D + 36)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide] at h9
  have h10 := sd_spec_gen_own_within .x2 .x24
    (sp0 + signExtend12 (-88 : BitVec 12)) cs8 (72 : BitVec 12) (D + 40)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide] at h10
  have h11 := mv_spec_gen_within .x8 .x10 a0 cs0 (D + 44) (by decide)
  have h12 := mv_spec_gen_within .x9 .x11 a1 cs1 (D + 48) (by decide)
  have h13 := mv_spec_gen_within .x18 .x12 a2 cs2 (D + 52) (by decide)
  have h14 := mv_spec_gen_within .x19 .x13 a3 cs3 (D + 56) (by decide)
  have h15 := mv_spec_gen_within .x20 .x14 a4 cs4 (D + 60) (by decide)
  have h16 := mv_spec_gen_within .x24 .x15 a5 cs8 (D + 64) (by decide)
  have h17 := li_spec_gen_within .x5 old5 (4 : Word) (D + 68) (by decide)
  runBlock h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

end EvmAsm.Codegen.BlockVerdictEip7702AuthNonstorageEffectsArraySpec
