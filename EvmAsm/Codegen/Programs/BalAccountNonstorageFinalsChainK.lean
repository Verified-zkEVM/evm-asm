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

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
