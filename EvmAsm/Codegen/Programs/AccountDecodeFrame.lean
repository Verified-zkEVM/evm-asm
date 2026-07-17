/-
  The ABI frame blocks of `accountDecode_prog` (`Programs/State.lean`, PR-K27):

    * `adPrologue`  — instructions [0]-[13] (`AB → AB+56`): `addi sp,-64`, the
      seven callee-saved stores (`x1/x8/x9/x18/x19/x20/x21`), and the six `mv`
      shuffles copying the caller arguments `a0..a5` into the saved registers
      `s0..s5` (`x8/x9/x18/x19/x20/x21`).
    * `adEpilogue` — instructions [127]-[135] (`AB+508 → ra`): the seven
      register reloads, `addi sp,+64`, and the `ret`.

  Both reuse K20's 7-slot `listNthFrame` (identical layout).  The prologue is
  the `storeSeq`/`setupMoves` pattern of `RlpListNthItemSAsm.wrapperPrologue`;
  the epilogue mirrors `RlpListNthItemSAsm.epilogueOwned`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeSpec
import EvmAsm.Codegen.Programs.RlpListNthItemCallSAsm
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame
  regsAt_listNthFrame frameSlotsSaved_listNthFrame)

set_option maxRecDepth 8000 in
/-- The ABI epilogue [127]-[135] (`AB+508 → saved.ra`): reload the seven
    callee-saved registers from their (untouched) frame slots, restore
    `sp := sp0`, and `ret`.  Generic over an arbitrary framed result `F`
    (which carries the already-set `a0` status).  Mirrors `epilogueOwned`. -/
theorem adEpilogue (sp0 newSp : Word) (saved : Saved)
    (F : Assertion) (hF : F.pcFree)
    (hnewSp : newSp = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : saved.ra &&& ~~~(1 : Word) = saved.ra) :
    cpsTripleWithin 9 (AB + 508) saved.ra fullCode
      (((.x2 ↦ᵣ newSp) ** regsOwnAt listNthFrame **
        savedFrame newSp saved) ** F)
      (((.x2 ↦ᵣ sp0) ** regsAt listNthFrame (savedVals saved) **
        savedFrame newSp saved) ** F) := by
  have hl0 := loadSeq_spec_own listNthFrame newSp (savedVals saved)
    (AB + 508) (by decide) (by decide)
  have hlMono : ∀ a i,
      CodeReq.ofProg (AB + 508) (loadProg listNthFrame) a = some i → fullCode a = some i := by
    intro a i hmem
    exact ad_mono a i (CodeReq.ofProg_mono_sub AB (AB + 508) accountDecode_prog
      (loadProg listNthFrame) 127 (by bv_omega) (by rfl)
      (by rw [ad_length]; simp [listNthFrame])
      (by rw [ad_length]; norm_num) a i hmem)
  have hl := cpsTripleWithin_extend_code hlMono hl0
  rw [show AB + 508 + BitVec.ofNat 64 (4 * listNthFrame.length) = AB + 536 from by
    simp [listNthFrame]; bv_omega] at hl
  rw [frameSlotsSaved_listNthFrame] at hl
  have hlF := cpsTripleWithin_frameR F hF hl
  have hd0 := addi_spec_gen_same_within .x2 newSp (64 : BitVec 12) (AB + 536)
    (by decide)
  rw [show newSp + signExtend12 (64 : BitVec 12) = sp0 from by
    rw [hnewSp]
    exact sext_frameRestore sp0 (-64 : BitVec 12) (64 : BitVec 12) (by decide)] at hd0
  have hd := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 536) accountDecode_prog 134
        (.ADDI .x2 .x2 (64 : BitVec 12)) (by bv_omega)
        (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) hd0)
  have hdF := cpsTripleWithin_frameR
    (regsAt listNthFrame (savedVals saved) ** savedFrame newSp saved ** F)
    (by unfold savedFrame; pcf; assumption) hd
  have hr0 := EvmAsm.Evm64.ret_spec_within' (AB + 540) saved.ra
  rw [hret] at hr0
  have hr := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 540) accountDecode_prog 135
        (.JALR .x0 .x1 (0 : BitVec 12)) (by bv_omega)
        (by rw [ad_length]; norm_num) rfl (by rw [ad_length]; norm_num)) hr0)
  have hrF := cpsTripleWithin_frameR
    (((.x2 ↦ᵣ sp0) **
      (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
      (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) **
      (.x20 ↦ᵣ saved.s4) ** (.x21 ↦ᵣ saved.s5) **
      savedFrame newSp saved) ** F) (by
        unfold savedFrame
        pcf
        assumption) hr
  have h12 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlF hdF
  have h123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    rw [regsAt_listNthFrame] at hp
    xperm_hyp hp) h12 hrF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hp => by
    rw [regsAt_listNthFrame]
    xperm_hyp hp) h123

#print axioms adEpilogue

end EvmAsm.Codegen.AccountDecodeSpec
