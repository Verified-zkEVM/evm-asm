/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainI

  Code-station assembly for bal_account_nonstorage_finals.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainH

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Slot 144, status-zero arm (`B + 576 → B + 580`): preserve a successful
    code-window `rlp_walk_init` result as the unified field-init post. -/
theorem bansf_codeFieldInitSuccess144_spec (aB : Word)
    (fOff fSpanN cOff : Nat) (acctBytes : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hok : FieldInitOk acctBytes fOff fSpanN cOff) :
    cpsTripleWithin 1 (B + 576) (B + 580) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
       bytesRegion aB acctBytes ** F)
      (fieldInitPost aB fOff fSpanN acctBytes (B + 572 + 4) F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (156 : BitVec 13)
    (0 : Word) (0 : Word) (B + 576)
  rw [show (B + 576) + 4 = B + 580 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeFieldStatus144_code hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
     ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanN))) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hfall
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hfallF
  unfold fieldInitPost
  refine ⟨cOff, (sepConj_pure_right h).2 ⟨?_, hok⟩⟩
  have hq' := sepConj_mono_left (sepConj_mono_right
    (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
  xperm_hyp hq'

#print axioms bansf_codeFieldInitSuccess144_spec

/-- Slot 144, nonzero-status arm (`B + 576 → B + 736`): branch through the
    shared reject stub and release the code field-init registers. -/
theorem bansf_codeFieldInitFailure144_spec (aB cur endW k : Word)
    (acctBytes : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 576) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       ((.x12 : Reg) ↦ᵣ k) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
       bytesRegion aB acctBytes ** F)
      (fieldRej aB acctBytes F) := by
  have hbne := bne_spec_gen_within .x12 .x0 (156 : BitVec 13)
    k (0 : Word) (B + 576)
  rw [show (B + 576) + signExtend13 (156 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (156 : BitVec 13) = (156 : Word) from by decide]
        bv_omega,
      show (B + 576) + 4 = B + 580 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeFieldStatus144_code hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hk (((sepConj_pure_right _).1 h_pure).2))
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B cur bansf_item4_code.2.2.2.2)
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ endW) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp') htaken hrejF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hchain
  unfold fieldRej
  have hq' :
      (((.x11 : Reg) ↦ᵣ endW) ** ((.x12 : Reg) ↦ᵣ k) **
       ((.x1 : Reg) ↦ᵣ (B + 572 + 4)) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq'
  xperm_hyp hqOwn

#print axioms bansf_codeFieldInitFailure144_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
