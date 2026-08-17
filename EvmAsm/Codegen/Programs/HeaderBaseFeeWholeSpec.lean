/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeSpec

  K73's callee composition layer.  `HeaderBaseFeeSpec` contains the linked
  arithmetic seams and the equal-target route; this module keeps the larger
  call/branch composition out of that file's Codegen/Programs line cap.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeSpec
import EvmAsm.Codegen.Proofs.HandlerHandlesUnary
import EvmAsm.Codegen.Proofs.U256BeFlatTriples
import EvmAsm.Codegen.Proofs.U256IsZeroSpec

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.U256DivU64BeSAsm

/-! The zero test consumes four dword cells, while K73's caller contract owns
    the same 32 bytes as one `bytesRegion`.  Keep this bridge local to the
    caller composition; it does not change the public memory vocabulary. -/
theorem k73_bytes4cells (ptr : Word) (bs : List (BitVec 8))
    (hlen : bs.length = 32) :
    bytesRegion ptr bs =
      ((ptr ↦ₘ packBytes ((bs.drop 0).take 8)) **
       ((ptr + 8) ↦ₘ packBytes ((bs.drop 8).take 8)) **
       ((ptr + 16) ↦ₘ packBytes ((bs.drop 16).take 8)) **
       ((ptr + 24) ↦ₘ packBytes ((bs.drop 24).take 8))) := by
  simpa [EvmAsm.Codegen.Proofs.wsDword] using (bytesRegion_eq_4cells ptr bs hlen)

/-! Both overflow arms converge on the same `li x10,1` plus epilogue tail.
    Keeping this adapter separate lets arithmetic-call posts retain their own
    status/overflow relation while the caller frame is restored uniformly. -/
theorem k73_failure_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn) (hP : P.pcFree) :
    cpsTripleWithin 9 (K73 + 272) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P) := by
  let Rest : Assertion :=
    (.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved ** P
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    exact pcFree_sepConj (pcFree_regIs (r := .x2) (v := spH))
      (pcFree_sepConj (pcFree_regsOwnAt k73Frame)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hP))
  have hliAny : ∀ old10, cpsTripleWithin 1 (K73 + 272) (K73 + 276)
      wholeCode (Rest ** (.x10 ↦ᵣ old10))
      (Rest ** (.x10 ↦ᵣ (1 : Word))) := by
    intro old10
    have hli := li_spec_gen_within .x10 old10 (1 : Word) (K73 + 272)
      (by decide)
    have hliC := cpsTripleWithin_extend_code
      (k73_whole_mem 68 _ (K73 + 272) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hli
    have hliF := cpsTripleWithin_frameR Rest hRest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hli' := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P := Rest) (Q := Rest ** (.x10 ↦ᵣ (1 : Word))) hliAny
  let P1 : Assertion := (.x10 ↦ᵣ (1 : Word)) ** P
  have hP1 : P1.pcFree := by
    dsimp [P1]
    exact pcFree_sepConj (pcFree_regIs (r := .x10) (v := 1)) hP
  have hepi := k73_epilogue_spec_within sp0 spH raIn saved P1
    hsp hret hsaved hP1
  have hepi' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P))
      (((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P)) := by
    dsimp [P1] at hepi ⊢
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) hepi
  have hepi'' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (Rest ** (.x10 ↦ᵣ (1 : Word)))
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 1) ** P) := by
    simpa [Rest, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hepi'
  have hseq := cpsTripleWithin_seq_same_cr hli' hepi''
  dsimp [Rest] at hseq ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hseq

/-! The successful increase arm has the analogous `li x10,0` plus a jump over
    the failure arm before entering the shared epilogue. -/
theorem k73_success_tail_spec_within
    (sp0 spH raIn : Word) (saved : Reg → Word) (P : Assertion)
    (hsp : spH + signExtend12 (56 : BitVec 12) = sp0)
    (hret : (raIn &&& ~~~(1 : Word)) = raIn)
    (hsaved : saved .x1 = raIn) (hP : P.pcFree) :
    cpsTripleWithin 10 (K73 + 196) raIn wholeCode
      ((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
        frameSlotsSaved k73Frame spH saved ** regOwn .x10 ** P)
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 0) ** P) := by
  let Rest : Assertion :=
    (.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved ** P
  have hRest : Rest.pcFree := by
    dsimp [Rest]
    exact pcFree_sepConj (pcFree_regIs (r := .x2) (v := spH))
      (pcFree_sepConj (pcFree_regsOwnAt k73Frame)
        (pcFree_sepConj (pcFree_frameSlotsSaved _ _ _) hP))
  have hliAny : ∀ old10, cpsTripleWithin 1 (K73 + 196) (K73 + 200)
      wholeCode (Rest ** (.x10 ↦ᵣ old10))
      (Rest ** (.x10 ↦ᵣ (0 : Word))) := by
    intro old10
    have hli := li_spec_gen_within .x10 old10 (0 : Word) (K73 + 196)
      (by decide)
    have hliC := cpsTripleWithin_extend_code
      (k73_whole_mem 49 _ (K73 + 196) (by decide)
        (by rw [k73_length]; decide) (by rfl)) hli
    have hliF := cpsTripleWithin_frameR Rest hRest hliC
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have hli' := cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x10)
    (P := Rest) (Q := Rest ** (.x10 ↦ᵣ (0 : Word))) hliAny
  have hj := jal_x0_spec_gen_within (76 : BitVec 21) (K73 + 200)
  rw [show (K73 + 200) + signExtend21 (76 : BitVec 21) = K73 + 276 by
    rw [show signExtend21 (76 : BitVec 21) = (76 : Word) from by decide]
    bv_omega] at hj
  have hjC := cpsTripleWithin_extend_code
    (k73_whole_mem 50 _ (K73 + 200) (by decide)
      (by rw [k73_length]; decide) (by rfl)) hj
  let P0 : Assertion := (.x10 ↦ᵣ (0 : Word)) ** P
  have hP0 : P0.pcFree := by
    dsimp [P0]
    exact pcFree_sepConj (pcFree_regIs (r := .x10) (v := 0)) hP
  have hjF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ spH) ** regsOwnAt k73Frame **
      frameSlotsSaved k73Frame spH saved) ** P0)
    (by dsimp [P0]; pcf; exact hP) hjC
  have hjump : cpsTripleWithin 1 (K73 + 200) (K73 + 276) wholeCode
      (Rest ** (.x10 ↦ᵣ (0 : Word)))
      (Rest ** (.x10 ↦ᵣ (0 : Word))) := by
    simpa [Rest, P0, sepConj_assoc', sepConj_comm', sepConj_left_comm',
      sepConj_emp_left', sepConj_emp_right'] using hjF
  have hepi := k73_epilogue_spec_within sp0 spH raIn saved P0
    hsp hret hsaved hP0
  have hepi' : cpsTripleWithin 8 (K73 + 276) raIn wholeCode
      (Rest ** (.x10 ↦ᵣ (0 : Word)))
      ((.x2 ↦ᵣ sp0) ** regsAt k73Frame saved **
        frameSlotsSaved k73Frame spH saved ** (.x10 ↦ᵣ 0) ** P) := by
    simpa [Rest, P0, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hepi
  have hseq := cpsTripleWithin_seq_same_cr hli' hjump
  have hseq' := cpsTripleWithin_seq_same_cr hseq hepi'
  dsimp [Rest] at hseq' ⊢
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hseq'

end EvmAsm.Codegen.HeaderBaseFeeSpec
