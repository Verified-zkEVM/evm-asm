/- Final code-item composition for bal_account_nonstorage_finals. -/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainK

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP
namespace BalAccountNonstorageFinalsSpec

/-- Slots 135–136 (`B + 540 → B + 548`): load the final outer-item cursor
    and account end for the code-item `rlp_walk_next` call. -/
theorem bansf_codeItemArgs135_spec (newSp cursor endW v10 v11 : Word) :
    cpsTripleWithin 2 (B + 540) (B + 548) bansfCR
      (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 48) ↦ₘ cursor) **
       ((newSp + 56) ↦ₘ endW) ** ((.x10 : Reg) ↦ᵣ v10) **
       ((.x11 : Reg) ↦ᵣ v11))
      (((.x2 : Reg) ↦ᵣ newSp) ** ((newSp + 48) ↦ₘ cursor) **
       ((newSp + 56) ↦ₘ endW) ** ((.x10 : Reg) ↦ᵣ cursor) **
       ((.x11 : Reg) ↦ᵣ endW)) := by
  have s1 := ld_spec_gen_within .x10 .x2 newSp v10 cursor
    (48 : BitVec 12) (B + 540) (by decide)
  rw [show signExtend12 (48 : BitVec 12) = (48 : Word) from by decide,
      show (B + 540) + 4 = B + 544 from by bv_omega] at s1
  have s1L := liftCode (cr' := bansfCR) s1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 540) bansfProg 135
        (.LD .x10 .x2 (48 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have s2 := ld_spec_gen_within .x11 .x2 newSp v11 endW
    (56 : BitVec 12) (B + 544) (by decide)
  rw [show signExtend12 (56 : BitVec 12) = (56 : Word) from by decide,
      show (B + 544) + 4 = B + 548 from by bv_omega] at s2
  have s2L := liftCode (cr' := bansfCR) s2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 544) bansfProg 136
        (.LD .x11 .x2 (56 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have s1F := cpsTripleWithin_frameR
    (((newSp + 56) ↦ₘ endW) ** ((.x11 : Reg) ↦ᵣ v11)) (by pcf) s1L
  have s2F := cpsTripleWithin_frameR
    (((newSp + 48) ↦ₘ cursor) ** ((.x10 : Reg) ↦ᵣ cursor)) (by pcf) s2L
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) s1F s2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hc

#print axioms bansf_codeItemArgs135_spec

/-- Concrete code witness for the final outer-item status gate at slot 138. -/
theorem bansf_codeItemStatus138_code :
    ∀ a i,
      CodeReq.singleton (B + 552) (.BNE .x11 .x0 (180 : BitVec 13)) a = some i →
      bansfCR a = some i := by
  intro a i h
  exact CodeReq.union_mono_left a i
    (CodeReq.ofProg_mem_at B (B + 552) bansfProg 138
      (.BNE .x11 .x0 (180 : BitVec 13))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) a i h)

#print axioms bansf_codeItemStatus138_code

/-- Status-zero arm of the final outer code item (`B + 552 → B + 556`). -/
theorem bansf_codeItemSuccess138_spec
    (next len : Word) :
    cpsTripleWithin 1 (B + 552) (B + 556) bansfCR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) := by
  have hbne := bne_spec_gen_within .x11 .x0 (180 : BitVec 13)
    (0 : Word) (0 : Word) (B + 552)
  rw [show (B + 552) + 4 = B + 556 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeItemStatus138_code hbne
  have hfall := cpsBranchWithin_ntakenPath hbneL
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
      exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
  have hfallF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ next) ** ((.x12 : Reg) ↦ᵣ len)) (by pcf) hfall
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      have hq' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      xperm_hyp hq') hfallF

#print axioms bansf_codeItemSuccess138_spec

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
