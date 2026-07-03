/-
  EvmAsm.Evm64.AddMod.Compose.CarryLd

  Phase-3 M3d for total ADDMOD (issue #9704): the fourth (final) carry-branch
  sub-chain prefix — the pre-reduced modular add's data staging + 4-limb add.

  Ld runs from `addmodCarryAfterCall3` (byte 460) to byte 832:

    mod_add_stage (460,8) ;; evm_add (492,30) ;;
    pass1take_clean (612,25) ;; pass2_owned (712,30)

  This file currently lands the machine prefix `mod_add_stage ;; evm_add`
  (460 → 612): it copies the carry contribution `m = pow256ModN N` (parked at
  S3) into the F+0..24 work window over `rMod = mod r N` at F+32..56, then runs
  the verified 4-limb `evm_add` to form the 257-bit sum `m + rMod` at the new
  top (x12 = F+32), exposing the add carry-out in x5.
-/

import EvmAsm.Evm64.AddMod.Compose.CondSubWrapper
import EvmAsm.Evm64.AddMod.Compose.CarryCompose
import EvmAsm.Evm64.EvmWordArith.AddModCondSub
import EvmAsm.Evm64.Add.Spec

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.Evm64

/-- Frame carried through `mod_add_stage`: `x0`, the return address, the six
    registers untouched (`x2/x6/x7/x9/x10/x11`, generic), the owned div-scratch
    band + `F−160` cell, the reduced low sum at F+32..56 (`rMod`), and the
    S1/S2 park cells (N and r). -/
def addmodLdModAddFrame (F raVal x2v x6v x7v x9v x10v x11v : Word)
    (v : EvmWord) (n0 n1 n2 n3 r0 r1 r2 r3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x6 ↦ᵣ x6v) ** (.x7 ↦ᵣ x7v) **
  (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) ** (.x11 ↦ᵣ x11v) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  evmWordIs (F + 32) v **
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3)

theorem addmodLdModAddFrame_pcFree (F raVal x2v x6v x7v x9v x10v x11v : Word)
    (v : EvmWord) (n0 n1 n2 n3 r0 r1 r2 r3 : Word) :
    (addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3).pcFree := by
  unfold addmodLdModAddFrame divScratchOwnCallNoX1 divScratchOwn evmWordIs
  pcFree

/-- Link 1 of Ld: `mod_add_stage` framed, over `C`. Copies the carry
    contribution `m` (limbs `p0..p3`, from S3) into F+0..24 (over the stale
    dividend `dd0..dd3`), leaving `rMod` at F+32..56. -/
theorem ld_mod_add_stage_in_C
    (bt F raVal x2v x6v x7v x9v x10v x11v : Word) (v : EvmWord)
    (p0 p1 p2 p3 n0 n1 n2 n3 r0 r1 r2 r3 dd0 dd1 dd2 dd3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    cpsTripleWithin 8 (bt + 460) ((bt + 460) + 32)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** regOwn .x5 **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ dd0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ dd1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ dd2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ dd3)) **
       addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3)
      (((.x12 ↦ᵣ F) ** (.x5 ↦ᵣ p3) **
        ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
        ((F + signExtend12 (0 : BitVec 12)) ↦ₘ p0) **
        ((F + signExtend12 (8 : BitVec 12)) ↦ₘ p1) **
        ((F + signExtend12 (16 : BitVec 12)) ↦ₘ p2) **
        ((F + signExtend12 (24 : BitVec 12)) ↦ₘ p3)) **
       addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3) := by
  simp only [sepConj_assoc']
  refine cpsTripleWithin_pre_regOwn_under (fun x5o => ?_)
  have hblk := carry_block_in_C
    (blockCode := evm_addmod_carry_mod_add_stage_code (bt + 460))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_mod_add_stage_sub a i
      (by rw [← evm_addmod_carry_mod_add_stage_code_eq_ofProg]; exact h))
    (cpsTripleWithin_frameR
      (addmodLdModAddFrame F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3)
      (addmodLdModAddFrame_pcFree F raVal x2v x6v x7v x9v x10v x11v v n0 n1 n2 n3 r0 r1 r2 r3)
      (evm_addmod_carry_mod_add_stage_spec_within F (bt + 460) x5o
        p0 p1 p2 p3 dd0 dd1 dd2 dd3))
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hp => ?_) hblk
  · simp only [addmodLdModAddFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLdModAddFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp

-- ============================================================================
-- Ld link 2: evm_add (byte 492 → 612)
-- ============================================================================

/-- The `evm_add` carry-out (`x5` of `evm_add_stack_spec_within`, the `carry3`
    let-chain over `getLimbN`) equals the 257th-bit overflow indicator. Bridges
    `evm_add_carry3_eq_overflow` (stated over `getLimb`) into the `getLimbN`
    form `evm_add_stack_spec_within` produces. -/
theorem evm_add_stack_carry3_eq_overflow (a b : EvmWord) :
    let b3 := b.getLimbN 3
    let a3 := a.getLimbN 3
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let psum2 := a.getLimbN 2 + b.getLimbN 2
    let carry2a := if BitVec.ult psum2 (b.getLimbN 2) then (1 : Word) else 0
    let psum1 := a.getLimbN 1 + b.getLimbN 1
    let carry1a := if BitVec.ult psum1 (b.getLimbN 1) then (1 : Word) else 0
    let sum0 := a.getLimbN 0 + b.getLimbN 0
    let carry0 := if BitVec.ult sum0 (b.getLimbN 0) then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    carry3 = if a.toNat + b.toNat ≥ 2 ^ 256 then (1 : Word) else 0 := by
  have h := EvmWord.evm_add_carry3_eq_overflow a b
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h
  exact h

/-- Frame carried through `evm_add`: everything the 4-limb add does not touch —
    `x0`, the return address, the three registers `x2/x9/x10` (generic), the
    owned div-scratch band + `F−160` cell, and the S1 (`N`) / S2 (`r`) / S3 (`m`)
    park cells. `evm_add` owns `x5/x6/x7/x11/x12` and the `F+0..56` work window. -/
def addmodLdAddFrame (F raVal x2v x9v x10v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ raVal) **
  (.x2 ↦ᵣ x2v) ** (.x9 ↦ᵣ x9v) ** (.x10 ↦ᵣ x10v) **
  divScratchOwnCallNoX1 F ** memOwn (F + signExtend12 (3936 : BitVec 12)) **
  ((F + signExtend12 (3840 : BitVec 12)) ↦ₘ p0) **
  ((F + signExtend12 (3848 : BitVec 12)) ↦ₘ p1) **
  ((F + signExtend12 (3856 : BitVec 12)) ↦ₘ p2) **
  ((F + signExtend12 (3864 : BitVec 12)) ↦ₘ p3) **
  ((F + signExtend12 (3872 : BitVec 12)) ↦ₘ r0) **
  ((F + signExtend12 (3880 : BitVec 12)) ↦ₘ r1) **
  ((F + signExtend12 (3888 : BitVec 12)) ↦ₘ r2) **
  ((F + signExtend12 (3896 : BitVec 12)) ↦ₘ r3) **
  ((F + signExtend12 (3904 : BitVec 12)) ↦ₘ n0) **
  ((F + signExtend12 (3912 : BitVec 12)) ↦ₘ n1) **
  ((F + signExtend12 (3920 : BitVec 12)) ↦ₘ n2) **
  ((F + signExtend12 (3928 : BitVec 12)) ↦ₘ n3)

theorem addmodLdAddFrame_pcFree (F raVal x2v x9v x10v : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word) :
    (addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3).pcFree := by
  unfold addmodLdAddFrame divScratchOwnCallNoX1 divScratchOwn
  pcFree

/-- Link 2 of Ld: the verified 4-limb `evm_add`, framed, over `C`. From the
    two pre-reduced operands `m` (at F+0..24) and `rMod` (at F+32..56), forms
    the 257-bit sum `m + rMod` at the new top (`x12 = F+32`), leaving the add
    carry-out in `x5` (folded to the overflow bit) and the dead limb-3 outputs
    in `x7/x6/x11`. The carry3-chain→overflow fold is done here so downstream
    reads a clean `x5`; `x6/x7/x11` stay concrete (pass1take treats them as
    dead inputs). -/
theorem ld_evm_add_in_C
    (bt F raVal x2v x9v x10v v5 v6 v7 v11 : Word) (m rMod : EvmWord)
    (n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3 : Word)
    (mo1 mo2 mo3 moNC : BitVec 21) (calleeEntry : Word) :
    let b0 := rMod.getLimbN 0; let a0 := m.getLimbN 0
    let b1 := rMod.getLimbN 1; let a1 := m.getLimbN 1
    let b2 := rMod.getLimbN 2; let a2 := m.getLimbN 2
    let b3 := rMod.getLimbN 3; let a3 := m.getLimbN 3
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    cpsTripleWithin 30 (bt + 492) ((bt + 492) + 120)
      (addmodCarryCode bt mo1 mo2 mo3 moNC calleeEntry)
      (((.x12 ↦ᵣ F) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
        evmWordIs F m ** evmWordIs (F + 32) rMod) **
       addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
      (((.x12 ↦ᵣ (F + 32)) ** (.x7 ↦ᵣ result3) ** (.x6 ↦ᵣ carry3b) **
        (.x5 ↦ᵣ (if m.toNat + rMod.toNat ≥ 2 ^ 256 then (1 : Word) else 0)) **
        (.x11 ↦ᵣ carry3a) **
        evmWordIs F m ** evmWordIs (F + 32) (m + rMod)) **
       addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3) := by
  intro b0 a0 b1 a1 b2 a2 b3 a3 sum0 carry0 psum1 carry1a result1 carry1b carry1
    psum2 carry2a result2 carry2b carry2 psum3 carry3a result3 carry3b
  have hadd := evm_add_stack_spec_within F (bt + 492) m rMod v7 v6 v5 v11
  simp only at hadd
  have hframed := cpsTripleWithin_frameR
    (addmodLdAddFrame F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
    (addmodLdAddFrame_pcFree F raVal x2v x9v x10v n0 n1 n2 n3 r0 r1 r2 r3 p0 p1 p2 p3)
    hadd
  have hC := carry_block_in_C
    (blockCode := evm_add_code (bt + 492))
    (totalCode := evm_addmod_total_program_code bt mo1 mo2 mo3 moNC)
    (calleeCode := evm_mod_callable_code_v5 calleeEntry)
    (fun a i h => evm_addmod_total_program_code_carry_evm_add_sub a i h)
    hframed
  have hcarry := evm_add_stack_carry3_eq_overflow m rMod
  simp only at hcarry
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hC
  · simp only [addmodLdAddFrame, sepConj_assoc'] at hp ⊢; xperm_hyp hp
  · simp only [addmodLdAddFrame, sepConj_assoc'] at hq ⊢
    rw [hcarry] at hq
    xperm_hyp hq

end EvmAsm.Evm64.AddMod.Compose
