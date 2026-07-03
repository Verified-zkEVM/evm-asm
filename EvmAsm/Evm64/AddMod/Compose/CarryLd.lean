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

end EvmAsm.Evm64.AddMod.Compose
