/- Code-station outer composition for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainJ

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Reframe a successful code tuple `walk_init` for the continuation at
    `B + 652`. -/
theorem codeTupleInitOk_to_cont652Pre
    (aB newSp oB n5 v19 v20 s64 s72 : Word)
    (aLen tOff tSpanN : Nat) (acctBytes : List (BitVec 8))
    (G F : Assertion) :
    ∀ h,
      ((fieldInitPost aB tOff tSpanN acctBytes (B + 644 + 4) F **
        (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
         ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ s64) **
         ((newSp + 72) ↦ₘ s72) ** G **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB))) h →
      (∃ cOff : Nat,
        (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
            ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
            ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
            memOwn (newSp + 72)) **
           (((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
            ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
            ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
            ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
            ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
            ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
            bytesRegion aB acctBytes ** G ** F)) **
          ⌜FieldInitOk acctBytes tOff tSpanN cOff⌝) h)) := by
  intro h hp
  unfold fieldInitPost at hp
  obtain ⟨g1, g2, gd, gu, hInit, hfr⟩ := hp
  obtain ⟨cOff, hInit2⟩ := hInit
  obtain ⟨hregs, hok⟩ := (sepConj_pure_right g1).1 hInit2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
      ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (tOff + tSpanN))) **
      ((.x12 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
      regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) ** bytesRegion aB acctBytes ** F) **
     (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
      ((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 64) ↦ₘ s64) **
      ((newSp + 72) ↦ₘ s72) ** G **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB))) h))
  have hconv := sepConj_mono (fun _ x => x)
    (sepConj_mono (regIs_implies_regOwn .x19)
      (sepConj_mono (regIs_implies_regOwn .x20)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn (fun _ x => x)))))) h hR
  have hconv2 := sepConj_mono
    (sepConj_mono (fun _ x => x)
      (sepConj_mono (fun _ x => x)
        (sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono (fun _ x => x)
                    (sepConj_mono (fun _ x => x)
                      (sepConj_mono (fun _ x => x)
                        (sepConj_mono (fun _ x => x)
                          (sepConj_mono (regIs_implies_regOwn .x1)
                            (fun _ x => x)))))))))))))
    (fun _ x => x) h hconv
  refine ⟨cOff, (sepConj_pure_right h).2 ⟨?_, hok⟩⟩
  xperm_hyp hconv2

#print axioms codeTupleInitOk_to_cont652Pre

/-- Slots 159–160 (`B + 636 → B + 644`): move the last code tuple span into
    the tuple `rlp_walk_init` arguments, accepting owned destination regs. -/
theorem bansf_codeLoopExitMove159_own_spec (v19 v20 : Word) :
    cpsTripleWithin 2 (B + 636) (B + 644) bansfCR
      (((((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)) **
        regOwn .x10 ** regOwn .x11))
      ((((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x10) (r2 := .x11) (fun v10 v11 => ?_)
  have s1 := mv_spec_gen_within .x10 .x19 v19 v10 (B + 636) (by decide)
  rw [show (B + 636) + 4 = B + 640 from by bv_omega] at s1
  have s1L := liftCode (cr' := bansfCR) s1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 636) bansfProg 159 (.MV .x10 .x19)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have s2 := mv_spec_gen_within .x11 .x20 v20 v11 (B + 640) (by decide)
  rw [show (B + 640) + 4 = B + 644 from by bv_omega] at s2
  have s2L := liftCode (cr' := bansfCR) s2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 640) bansfProg 160 (.MV .x11 .x20)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have s1F := cpsTripleWithin_frameR
    (((.x20 : Reg) ↦ᵣ v20) ** ((.x11 : Reg) ↦ᵣ v11)) (by pcf) s1L
  have s2F := cpsTripleWithin_frameR
    (((.x19 : Reg) ↦ᵣ v19) ** ((.x10 : Reg) ↦ᵣ v19)) (by pcf) s2L
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) s1F s2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hc

#print axioms bansf_codeLoopExitMove159_own_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
