/-
  EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix

  CPS spec for the shift-and-insert prefix of the MULMOD reducer inner step.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.MulMod.ReduceCompare
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The straight-line shift/update prefix of `evm_mulmod_reduce512_inner_step`. -/
def evm_mulmod_reduce512_inner_step_shift_prefix : Program :=
  SRLI .x19 .x17 63 ;;
  SLLI .x17 .x17 1 ;;
  LD .x5 .x12 4064 ;;
  SRLI .x20 .x5 63 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x19 ;;
  SD .x12 .x6 4064 ;;
  LD .x5 .x12 4072 ;;
  SRLI .x19 .x5 63 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x20 ;;
  SD .x12 .x6 4072 ;;
  LD .x5 .x12 4080 ;;
  SRLI .x20 .x5 63 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x19 ;;
  SD .x12 .x6 4080 ;;
  LD .x5 .x12 4088 ;;
  SLLI .x6 .x5 1 ;;
  OR' .x6 .x6 .x20 ;;
  SD .x12 .x6 4088

abbrev evm_mulmod_reduce512_inner_step_shift_prefix_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_mulmod_reduce512_inner_step_shift_prefix

/-- Folded postcondition for the reducer shift/update prefix. -/
@[irreducible]
def mulModReduceShiftPrefixPost (sp x17Old r0 r1 r2 r3 : Word) : Assertion :=
  let shifted :=
    mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) (mulModReduceInputBit x17Old)
  (.x12 ↦ᵣ sp) **
  (.x17 ↦ᵣ (x17Old <<< 1)) **
  (.x5 ↦ᵣ r3) **
  (.x6 ↦ᵣ EvmWord.getLimbN shifted 3) **
  (.x19 ↦ᵣ (r1 >>> 63)) **
  (.x20 ↦ᵣ (r2 >>> 63)) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ EvmWord.getLimbN shifted 3)

/-- Raw postcondition matching the generated instruction specs before normalizing shift amounts. -/
@[irreducible]
def mulModReduceShiftPrefixRawPost (sp x17Old r0 r1 r2 r3 : Word) : Assertion :=
  let x17New := x17Old <<< (1 : BitVec 6).toNat
  let inBit := x17Old >>> (63 : BitVec 6).toNat
  let carry0 := r0 >>> (63 : BitVec 6).toNat
  let carry1 := r1 >>> (63 : BitVec 6).toNat
  let carry2 := r2 >>> (63 : BitVec 6).toNat
  let limb0 := (r0 <<< (1 : BitVec 6).toNat) ||| inBit
  let limb1 := (r1 <<< (1 : BitVec 6).toNat) ||| carry0
  let limb2 := (r2 <<< (1 : BitVec 6).toNat) ||| carry1
  let limb3 := (r3 <<< (1 : BitVec 6).toNat) ||| carry2
  (.x12 ↦ᵣ sp) **
  (.x17 ↦ᵣ x17New) **
  (.x5 ↦ᵣ r3) **
  (.x6 ↦ᵣ limb3) **
  (.x19 ↦ᵣ carry1) **
  (.x20 ↦ᵣ carry2) **
  ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ limb0) **
  ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ limb1) **
  ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ limb2) **
  ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ limb3)

theorem mulModReduceShiftPrefixRawPost_eq_folded
    (sp x17Old r0 r1 r2 r3 : Word) :
    mulModReduceShiftPrefixRawPost sp x17Old r0 r1 r2 r3 =
      mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3 := by
  unfold mulModReduceShiftPrefixRawPost mulModReduceShiftPrefixPost
  rw [show (1 : BitVec 6).toNat = 1 by decide]
  rw [show (63 : BitVec 6).toNat = 63 by decide]
  simp only [mulModReduceShiftInBit_getLimbN_zero_input,
    mulModReduceShiftInBit_getLimbN_one, mulModReduceShiftInBit_getLimbN_two,
    mulModReduceShiftInBit_getLimbN_three]

theorem evm_mulmod_reduce512_inner_step_shift_prefix_raw_spec_within
    (sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20 : Word) :
    cpsTripleWithin 21 base (base + 84)
      (evm_mulmod_reduce512_inner_step_shift_prefix_code base)
      ((.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      (mulModReduceShiftPrefixRawPost sp x17Old r0 r1 r2 r3) := by
  unfold mulModReduceShiftPrefixRawPost
  have S0 := srli_spec_gen_within .x19 .x17 v19 x17Old 63 base (by decide)
  have S1 := slli_spec_gen_same_within .x17 x17Old 1 (base + 4) (by decide)
  have L0 := ld_spec_gen_within .x5 .x12 sp v5 r0 4064 (base + 8) (by decide)
  have S2 := srli_spec_gen_within .x20 .x5 v20 r0 63 (base + 12) (by decide)
  have S3 := slli_spec_gen_within .x6 .x5 v6 r0 1 (base + 16) (by decide)
  have O0 := or_spec_gen_rd_eq_rs1_within .x6 .x19
    (r0 <<< (1 : BitVec 6).toNat) (x17Old >>> (63 : BitVec 6).toNat)
    (base + 20) (by decide)
  have St0 := sd_spec_gen_within .x12 .x6 sp
    ((r0 <<< (1 : BitVec 6).toNat) ||| (x17Old >>> (63 : BitVec 6).toNat)) r0 4064
    (base + 24)
  have L1 := ld_spec_gen_within .x5 .x12 sp r0 r1 4072 (base + 28) (by decide)
  have S4 := srli_spec_gen_within .x19 .x5 (x17Old >>> (63 : BitVec 6).toNat) r1 63
    (base + 32) (by decide)
  have S5 := slli_spec_gen_within .x6 .x5
    ((r0 <<< (1 : BitVec 6).toNat) ||| (x17Old >>> (63 : BitVec 6).toNat)) r1 1
    (base + 36) (by decide)
  have O1 := or_spec_gen_rd_eq_rs1_within .x6 .x20
    (r1 <<< (1 : BitVec 6).toNat) (r0 >>> (63 : BitVec 6).toNat)
    (base + 40) (by decide)
  have St1 := sd_spec_gen_within .x12 .x6 sp
    ((r1 <<< (1 : BitVec 6).toNat) ||| (r0 >>> (63 : BitVec 6).toNat)) r1 4072
    (base + 44)
  have L2 := ld_spec_gen_within .x5 .x12 sp r1 r2 4080 (base + 48) (by decide)
  have S6 := srli_spec_gen_within .x20 .x5 (r0 >>> (63 : BitVec 6).toNat) r2 63
    (base + 52) (by decide)
  have S7 := slli_spec_gen_within .x6 .x5
    ((r1 <<< (1 : BitVec 6).toNat) ||| (r0 >>> (63 : BitVec 6).toNat)) r2 1
    (base + 56) (by decide)
  have O2 := or_spec_gen_rd_eq_rs1_within .x6 .x19
    (r2 <<< (1 : BitVec 6).toNat) (r1 >>> (63 : BitVec 6).toNat)
    (base + 60) (by decide)
  have St2 := sd_spec_gen_within .x12 .x6 sp
    ((r2 <<< (1 : BitVec 6).toNat) ||| (r1 >>> (63 : BitVec 6).toNat)) r2 4080
    (base + 64)
  have L3 := ld_spec_gen_within .x5 .x12 sp r2 r3 4088 (base + 68) (by decide)
  have S8 := slli_spec_gen_within .x6 .x5
    ((r2 <<< (1 : BitVec 6).toNat) ||| (r1 >>> (63 : BitVec 6).toNat)) r3 1
    (base + 72) (by decide)
  have O3 := or_spec_gen_rd_eq_rs1_within .x6 .x20
    (r3 <<< (1 : BitVec 6).toNat) (r2 >>> (63 : BitVec 6).toNat)
    (base + 76) (by decide)
  have St3 := sd_spec_gen_within .x12 .x6 sp
    ((r3 <<< (1 : BitVec 6).toNat) ||| (r2 >>> (63 : BitVec 6).toNat)) r3 4088
    (base + 80)
  dsimp only
  runBlock S0 S1 L0 S2 S3 O0 St0 L1 S4 S5 O1 St1 L2 S6 S7 O2 St2 L3 S8 O3 St3

theorem evm_mulmod_reduce512_inner_step_shift_prefix_spec_within
    (sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20 : Word) :
    cpsTripleWithin 21 base (base + 84)
      (evm_mulmod_reduce512_inner_step_shift_prefix_code base)
      ((.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      (mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3) := by
  have hraw :=
    evm_mulmod_reduce512_inner_step_shift_prefix_raw_spec_within
      sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20
  rw [mulModReduceShiftPrefixRawPost_eq_folded] at hraw
  exact hraw

/-- The shift prefix (instructions 0–20) is subsumed by the full inner-step
    CodeReq. (Mirrors `evm_mulmod_reduce512_inner_step_shift_prefix_code_sub`
    in `ReduceInnerStepSpecs`, which is downstream of this file.) -/
private theorem inner_step_shift_prefix_code_sub (base : Word) :
    ∀ a i, evm_mulmod_reduce512_inner_step_shift_prefix_code base a = some i →
      CodeReq.ofProg base evm_mulmod_reduce512_inner_step a = some i := by
  unfold evm_mulmod_reduce512_inner_step_shift_prefix_code
  refine CodeReq.ofProg_mono_sub base base
    evm_mulmod_reduce512_inner_step evm_mulmod_reduce512_inner_step_shift_prefix
    0 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 0) = (0 : Word) by decide]
    bv_omega
  · rfl
  · decide
  · decide

/-- The new `SRLI .x8 .x5 63` at byte offset 84 (program index 21) of
    `evm_mulmod_reduce512_inner_step` is subsumed by the full-step CodeReq. -/
private theorem inner_step_srli_carry_code_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 84) (.SRLI .x8 .x5 (63 : BitVec 6)) a = some i →
      CodeReq.ofProg base evm_mulmod_reduce512_inner_step a = some i := by
  rw [← CodeReq.ofProg_singleton]
  refine CodeReq.ofProg_mono_sub base (base + 84)
    evm_mulmod_reduce512_inner_step [.SRLI .x8 .x5 (63 : BitVec 6)]
    21 ?_ ?_ ?_ ?_
  · rw [show BitVec.ofNat 64 (4 * 21) = (84 : Word) by decide]
  · rfl
  · decide
  · decide

/-- Shift prefix spec extended by the new carry-capturing `SRLI .x8 .x5 63`
    (program index 21, byte offset 84 → 88), over the full inner-step CodeReq.

    After the 21-instruction shift cascade, `.x5 ↦ᵣ r3` holds the pre-shift high
    limb (the 4th remainder limb), so `SRLI .x8 .x5 63` writes `x8 = r3 >>> 63`,
    i.e. the remainder's bit 255 — the carry-out the old code discarded. -/
theorem evm_mulmod_reduce512_inner_step_shift_prefix_carry_spec_within
    (sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20 x8Old : Word) :
    cpsTripleWithin 22 base (base + 88)
      (CodeReq.ofProg base evm_mulmod_reduce512_inner_step)
      ((.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ x17Old) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
       (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x8 ↦ᵣ x8Old) **
       ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ r3))
      (mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3 ** (.x8 ↦ᵣ (r3 >>> 63))) := by
  -- Prefix: 21 instructions, base → base+84, framed with `.x8 ↦ᵣ x8Old`.
  have hprefix :=
    cpsTripleWithin_frameR (.x8 ↦ᵣ x8Old) pcFree_regIs
      (cpsTripleWithin_extend_code
        (hmono := inner_step_shift_prefix_code_sub base)
        (h := evm_mulmod_reduce512_inner_step_shift_prefix_spec_within
          sp base x17Old r0 r1 r2 r3 v5 v6 v19 v20))
  -- SRLI step: 1 instruction, base+84 → base+88, reads x5 = r3, writes x8.
  have hsrli :=
    cpsTripleWithin_extend_code
      (hmono := inner_step_srli_carry_code_sub base)
      (h := srli_spec_gen_within .x8 .x5 x8Old r3 (63 : BitVec 6) (base + 84) (by decide))
  rw [show (63 : BitVec 6).toNat = 63 by decide] at hsrli
  rw [show base + 84 + 4 = base + 88 by bv_omega] at hsrli
  -- The frame for the SRLI: every atom of the folded prefix post except `.x5`.
  set shifted :=
    mulModReduceShiftInBit (mulModReduceRemWord r0 r1 r2 r3) (mulModReduceInputBit x17Old)
    with hshifted
  have hstep :
      cpsTripleWithin 1 (base + 84) (base + 88)
        (CodeReq.ofProg base evm_mulmod_reduce512_inner_step)
        (mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3 ** (.x8 ↦ᵣ x8Old))
        (mulModReduceShiftPrefixPost sp x17Old r0 r1 r2 r3 ** (.x8 ↦ᵣ (r3 >>> 63))) := by
    have hframed :=
      cpsTripleWithin_frameR
        ((.x12 ↦ᵣ sp) ** (.x17 ↦ᵣ (x17Old <<< 1)) ** (.x6 ↦ᵣ shifted.getLimbN 3) **
         (.x19 ↦ᵣ (r1 >>> 63)) ** (.x20 ↦ᵣ (r2 >>> 63)) **
         ((sp + signExtend12 (4064 : BitVec 12)) ↦ₘ shifted.getLimbN 0) **
         ((sp + signExtend12 (4072 : BitVec 12)) ↦ₘ shifted.getLimbN 1) **
         ((sp + signExtend12 (4080 : BitVec 12)) ↦ₘ shifted.getLimbN 2) **
         ((sp + signExtend12 (4088 : BitVec 12)) ↦ₘ shifted.getLimbN 3))
        (by
          repeat first
            | exact pcFree_regIs
            | exact pcFree_memIs
            | apply pcFree_sepConj)
        hsrli
    refine cpsTripleWithin_weaken ?_ ?_ hframed
    · intro h hp
      unfold mulModReduceShiftPrefixPost at hp
      simp only [← hshifted] at hp
      xperm_hyp hp
    · intro h hp
      unfold mulModReduceShiftPrefixPost
      simp only [← hshifted]
      xperm_hyp hp
  -- Sequence prefix then SRLI step (same CodeReq), then fix entry/exit shape.
  have hcomp := cpsTripleWithin_seq_same_cr hprefix hstep
  refine cpsTripleWithin_weaken ?_ (fun _ hp => hp) hcomp
  intro h hp
  xperm_hyp hp

end EvmAsm.Evm64
