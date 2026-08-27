/-
  Decrease-route composition toward the Route-B K73 contract (#12346 item 2b).

  The increasing arm ships a fully-composed entry-to-return theorem
  (`k73_increase_entry_status_div_zero_to_return_general_spec_within`).  The
  decreasing arm only ships seams.  This file assembles them bottom-up:

    entry            (19, premise-free)              K73 .. K73 + 84
    mul call/status  (needs deployed mul callee)     K73 + 84 .. K73 + 92
    div pair         (premise-free, htargetPos)      K73 + 92 .. K73 + 124
    branch x20=0     (premise-free)                  K73 + 124 .. K73 + 172
    div-to-sub       (premise-free modulo ABI facts) K73 + 172 .. K73 + 220
    borrow branch                                    K73 + 220 .. K73 + 224
    tails            (symbolic raIn, saved-generic)  K73 + 224/+272 .. raIn

  Everything here composes already-proven seams; no new instruction is
  interpreted.  The borrow branch below is the only machine-level piece that
  was missing entirely: the decrease subtract's overflow test at K73 + 220
  branches on the callee borrow register against x0.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeEntry
import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec

/-- Overflow test of the in-place subtraction on the nonzero decrease arm:
    `bne a0, x0, +52` at K73 + 220 sends a nonzero borrow to the shared
    failure exit (li x10, 1 at K73 + 272) and falls through to the successful
    `li x10, 0` at K73 + 224 otherwise.  Value-generalized over the borrowed
    register exactly like the multiply status branch helper. -/
theorem k73_decrease_sub_borrow_branch_spec_within
    (Rest : Assertion) (hRest : Rest.pcFree) :
    cpsBranchWithin 1 (K73 + 220) wholeCode
      (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 272)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 224)
        (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
  have hraw : ∀ old10 : Word, cpsBranchWithin 1 (K73 + 220) wholeCode
      ((((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) **
        ((.x10 : Reg) ↦ᵣ old10))
      (K73 + 272) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10)
      (K73 + 224) (((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest ** regOwn .x10) := by
    intro old10
    have hbne := bne_spec_gen_within .x10 .x0 (52 : BitVec 13)
      old10 (0 : Word) (K73 + 220)
    have hbneC := cpsBranchWithin_extend_code
      (k73_whole_mem 55 (.BNE .x10 .x0 (52 : BitVec 13)) (K73 + 220)
        (by decide) (by rw [k73_length]; decide) (by rfl)) hbne
    rw [show signExtend13 (52 : BitVec 13) = (52 : Word) by decide,
      show (K73 + 220) + (52 : Word) = K73 + 272 by bv_omega,
      show (K73 + 220) + 4 = K73 + 224 by bv_omega] at hbneC
    have hbneF := cpsBranchWithin_frameR Rest hRest hbneC
    refine cpsBranchWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun h hq => ?_) (fun h hq => ?_) hbneF
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      sep_perm hq1
    · have hq1 := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn .x10 old10)) h hq
      drop_pure hq1
      sep_perm hq1
  have hbr := cpsBranchWithin_of_forall_regIs_to_regOwn
    (r := .x10) (P := ((.x0 : Reg) ↦ᵣ (0 : Word)) ** Rest) hraw
  exact cpsBranchWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) (fun _ hq => by sep_perm hq) hbr

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionDecreaseRoute
