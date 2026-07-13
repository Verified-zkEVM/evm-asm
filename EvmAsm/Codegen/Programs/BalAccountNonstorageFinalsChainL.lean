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


/-- Nonzero-status continuation for the final outer code item
    (`B + 552 → B + 736`). -/
theorem bansf_codeItemFailure138_spec (aB newSp cur k : Word)
    (aLen off : Nat) (acctBytes : List (BitVec 8)) (F : Assertion)
    (hF : F.pcFree) (hk : k ≠ (0 : Word)) :
    cpsTripleWithin 2 (B + 552) (B + 736) bansfCR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
       bytesRegion aB acctBytes ** F)
      (itemRej aB newSp acctBytes F) := by
  have hbne := bne_spec_gen_within .x11 .x0 (180 : BitVec 13)
    k (0 : Word) (B + 552)
  rw [show (B + 552) + signExtend13 (180 : BitVec 13) = B + 732 from by
        rw [show signExtend13 (180 : BitVec 13) = (180 : Word) from by decide]
        bv_omega,
      show (B + 552) + 4 = B + 556 from by bv_omega] at hbne
  have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
    bansf_codeItemStatus138_code hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x10 : Reg) ↦ᵣ cur) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
     ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hbneL
  have htaken := cpsBranchWithin_takenPath hbneF
    (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
      exact hk (((sepConj_pure_right _).1 h_pure).2))
  have hrej := liftCode (cr' := bansfCR)
    (bansf_rejectTail_spec B cur bansf_item4_code.2.2.2.2)
    (fun a i h => CodeReq.union_mono_left a i h)
  have hrejF := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hrej
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      have hp' := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp') htaken hrejF
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_)
    hchain
  unfold itemRej
  have hq' :
      (((.x11 : Reg) ↦ᵣ k) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12)
      (sepConj_mono (regIs_implies_regOwn .x1)
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn (fun _ x => x))))) h hq'
  xperm_hyp hqOwn

#print axioms bansf_codeItemFailure138_spec

/-- Reframe final-item success for `B + 556`, keeping cursor and spill distinct. -/
theorem codeItemSuccess_to_cont556Pre
    (aB newSp oB spill5 next len v19 v20 : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ spill5) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
       bytesRegion aB acctBytes ** F ** G ** memOwn (newSp + 64) **
       memOwn (newSp + 72) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word))) h →
      (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x19 : Reg) ↦ᵣ v19) **
       ((.x20 : Reg) ↦ᵣ v20) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ spill5) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       memOwn (newSp + 64) ** memOwn (newSp + 72) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ aB) **
       ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
       G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) h := by
  intro h hp
  xperm_hyp hp

#print axioms codeItemSuccess_to_cont556Pre

/-- Successful final outer-item decode, with spill 48 unchanged. -/
def codeItemFinalOk (aB newSp spill5 : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  fun h => ∃ next len : Word,
    ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 48) ↦ₘ spill5) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
       (aB + BitVec.ofNat 64 aLen) next len⌝) h

/-- Expose a final-item success as the corrected continuation precondition. -/
theorem codeItemFinalOk_to_cont556Pre
    (aB newSp oB spill5 v19 v20 : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (codeItemFinalOk aB newSp spill5 aLen off acctBytes F **
       (G ** memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20) ** ((oB + 56) ↦ₘ (0 : Word)) **
        ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word)))) h →
      (∃ next len : Word,
        (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) ** ((.x19 : Reg) ↦ᵣ v19) **
          ((.x20 : Reg) ↦ᵣ v20) ** ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 48) ↦ₘ spill5) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          memOwn (newSp + 64) ** memOwn (newSp + 72) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x8 : Reg) ↦ᵣ aB) **
          ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
          ((.x18 : Reg) ↦ᵣ oB) ** G ** ((oB + 56) ↦ₘ (0 : Word)) **
          ((oB + 64) ↦ₘ (0 : Word)) ** ((oB + 72) ↦ₘ (0 : Word)) **
          bytesRegion aB acctBytes ** F) ** regOwn .x5 ** regOwn .x6 **
         regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
         regOwn .x31 ** regOwn .x1) **
        ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
          (aB + BitVec.ofNat 64 aLen) next len⌝) h) := by
  intro h hp
  unfold codeItemFinalOk at hp
  obtain ⟨next, hpN⟩ := (sepConj_exists_left h).1 hp
  obtain ⟨len, hpL⟩ := (sepConj_exists_left h).1 hpN
  refine ⟨next, len, ?_⟩
  xperm_hyp hpL

#print axioms codeItemFinalOk_to_cont556Pre


theorem bansf_codeItem5_spec (aB newSp : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v10 v11 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoffle : off ≤ aLen) :
    cpsBranchWithin 93 (B + 540) bansfCR
      (((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 556) (codeItemFinalOk aB newSp (aB + BitVec.ofNat 64 off) aLen off acctBytes F) := by
  have hoffb : off < acctBytes.length := by omega
  have hargs := bansf_codeItemArgs135_spec newSp
    (aB + BitVec.ofNat 64 off) (aB + BitVec.ofNat 64 aLen) v10 v11
  have hargsF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ v12) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
     ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x1 : Reg) ↦ᵣ vRa) ** bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hargs
  -- the callee triple with ra = B + 548 + 4
  have hwn := rlp_walk_next_spec_within WN aB (aB + BitVec.ofNat 64 aLen)
    (B + 548 + 4) v12 v5 v6 v7 v28 v29 v30 v31
    acctBytes off hsalign hoffb (by omega)
    (hvalid off hoffb)
    (fun h80 hb8 => ⟨by omega, by omega, hvalid _ (by omega)⟩)
    (fun hb8 hc0 => by
      have hlo : ((acctBytes[off]'hoffb).zeroExtend 64 - (0xb7 : Word)).toNat ≤ 8 := by
        have h1 := ult_lt hc0
        have h2 := not_ult_le hb8
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
    (fun hf8 => by
      have hlo : ((acctBytes[off]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[off]'hoffb).isLt
        bv_omega
      exact ⟨by omega, by omega, fun k hk => hvalid _ (by omega)⟩)
  have hwn' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwn
    (P' := ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite137_walk_next (n := 87) vRa (by pcf) hwn'
  rw [show (B + 548) + 4 = B + 552 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** F)
    (by pcf; exact hF) hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hargsF hcallF
  -- ===== ok continuation: BNE falls through only =====
  have hokc : cpsBranchWithin 1 (B + 552) bansfCR
      (fun h => ∃ next len : Word,
        ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
           (aB + BitVec.ofNat 64 aLen) next len⌝) h)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 556) (codeItemFinalOk aB newSp (aB + BitVec.ofNat 64 off) aLen off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun next => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (180 : BitVec 13) (0 : Word) (0 : Word) (B + 552)
    rw [show (B + 552) + 4 = B + 556 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      bansf_codeItemStatus138_code hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x12 : Reg) ↦ᵣ len) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hout : cpsTripleWithin 1 (B + 552) (B + 556) bansfCR
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ len) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
         bytesRegion aB acctBytes ** F)
        (codeItemFinalOk aB newSp (aB + BitVec.ofNat 64 off) aLen off acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      unfold codeItemFinalOk
      refine ⟨next, len, ?_⟩
      have hq1 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
      have hq2 : ((((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
          (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ len) **
           ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq1
      have hq3 := sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x) h hq2
      have hq4 : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          (((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen))) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hq3
      exact (sepConj_pure_right h).2 ⟨by xperm_hyp hq4, hdec⟩
    exact cpsTripleWithin_as_cpsBranchWithin_right _ _ hout
  -- ===== fail continuation =====
  have hfailc : cpsBranchWithin 2 (B + 552) bansfCR
      (fun h => ∃ cur k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (itemRej aB newSp acctBytes F)
      (B + 556) (codeItemFinalOk aB newSp (aB + BitVec.ofNat 64 off) aLen off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (180 : BitVec 13) k (0 : Word) (B + 552)
    rw [show (B + 552) + signExtend13 (180 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (180 : BitVec 13) = (180 : Word) from by decide]
          bv_omega,
        show (B + 552) + 4 = B + 556 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      bansf_codeItemStatus138_code hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hbneL
    have htaken := cpsBranchWithin_takenPath hbneF
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact hk (((sepConj_pure_right _).1 h_pure).2))
    have hrej := liftCode (cr' := bansfCR)
      (bansf_rejectTail_spec B cur bansf_item4_code.2.2.2.2)
      (fun a i h => CodeReq.union_mono_left a i h)
    have hrejF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ k) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 552) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
         bytesRegion aB acctBytes ** F)
        (itemRej aB newSp acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold itemRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ k) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
          ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq
      have hq5 := sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1)
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn (fun _ x => x))))) h hq4
      xperm_hyp hq5
    exact cpsTripleWithin_as_cpsBranchWithin_left _ _ hout
  -- ===== chain: loads ; call ; (ok ∨ fail) =====
  refine cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_seq_branch_same_cr hpre
        (cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
          (cpsBranchWithin_pre_or
            (cpsBranchWithin_mono_nSteps (by omega) hokc) hfailc))))
  obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
  have rebuild : ∀ (arm : Assertion), arm h4 →
      ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) ** bytesRegion aB acctBytes) ** arm) **
        (((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** F))) h :=
    fun arm ha => ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ha⟩, hEx⟩
  rcases hor with a1 | a2 | a3 | a4 | a5 | a6
  · obtain ⟨next, len, hpins⟩ := a1
    refine Or.inl ⟨next, len, ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := hpins
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, hdec⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ len))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ len) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, hdec⟩
  · -- fail arm: status 2
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (2 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a2
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (2 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (2 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 3
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (3 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a3
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (3 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (3 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 4
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (4 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a4
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (4 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (4 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 5
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (5 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a5
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (5 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (5 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 6
    refine Or.inr ⟨aB + BitVec.ofNat 64 off, (6 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a6
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (6 : Word)) ** ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
        ((.x11 : Reg) ↦ᵣ (6 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        ((.x2 : Reg) ↦ᵣ newSp) **
        ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 548 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩

#print axioms bansf_codeItem5_spec

/-- Reframe final outer-item failure as the code-station reject post. -/
theorem item5Reject_to_codeStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (itemRej aB newSp acctBytes F **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** memOwn (newSp + 64) **
        memOwn (newSp + 72) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x19 ** regOwn .x20)) h →
      codeStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold itemRej at hq
  have hq' :
      ((((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word))) **
       (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 48) ** memOwn (newSp + 56) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F ** G ** memOwn (newSp + 64) **
        memOwn (newSp + 72) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x19 ** regOwn .x20)) h := by
    xperm_hyp hq
  have hqOwn := sepConj_mono
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn))
    (fun _ x => x) h hq'
  unfold codeStationRej
  xperm_hyp hqOwn

#print axioms item5Reject_to_codeStationRej


def codeStationOuterPost (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h => ∃ n5 l5 : Word,
    (codeStationPost aB newSp oB aLen ((n5 - l5 - aB).toNat)
        l5.toNat (aB + BitVec.ofNat 64 off) acctBytes G F **
      ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
        (aB + BitVec.ofNat 64 aLen) n5 l5⌝) h

/-- Stable state entering the outer code item, excluding caller-saved
    register ownership peeled by the station theorem. -/
def codeStationOuterBase (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
  ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
  ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) ** G **

  ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
  ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion aB acctBytes ** F

/-- **The code station** (`B + 540 → B + 736 | B + 724`): decode outer
    account item 5, parse its last code tuple, and materialize the code
    result while retaining the full outer/inner derivation. -/
theorem bansf_codeStation_spec (aB newSp oB : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoff : off ≤ aLen) :
    cpsBranchWithin (98 * (aLen + 1) + (7 * acctBytes.length + 800))
      (B + 540) bansfCR
      (((codeStationOuterBase aB newSp oB aLen off acctBytes G F **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
        regOwn .x19 ** regOwn .x20) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1))
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724) (codeStationOuterPost aB newSp oB aLen off acctBytes G F) := by
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  let V8 : Assertion :=
    ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
    ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
    ((.x31 : Reg) ↦ᵣ v31) ** ((.x1 : Reg) ↦ᵣ vRa)
  refine cpsBranchWithin_weaken
    (P' := (codeStationOuterBase aB newSp oB aLen off acctBytes G F **
      regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 ** regOwn .x20) ** V8)
    (fun h hp => by
      change (((codeStationOuterBase aB newSp oB aLen off acctBytes G F **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 **
        regOwn .x20) ** V8) h) at hp
      change (((codeStationOuterBase aB newSp oB aLen off acctBytes G F ** V8) **
        regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x19 **
        regOwn .x20) h)
      dsimp only [V8] at hp ⊢
      xperm_hyp hp)
    (fun _ x => x) (fun _ x => x) ?_
  refine cpsBranchWithin_of_forall_regIs_to_regOwn5
    (P := codeStationOuterBase aB newSp oB aLen off acctBytes G F ** V8)
    (fun v10 v11 v12 v19 v20 => ?_)
  let H : Assertion :=
    G **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** memOwn (newSp + 64) **
    memOwn (newSp + 72) ** ((.x8 : Reg) ↦ᵣ aB) **
    ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
    ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20)
  have hi := bansf_codeItem5_spec aB newSp aLen off acctBytes
    v5 v6 v7 v10 v11 v12 v28 v29 v30 v31 vRa F hF hsalign
    hslack hover hvalid hoff
  have hiF := cpsBranchWithin_frameR H
    (by dsimp only [H]; pcf; exact hG; pcf) hi
  have hiW := cpsBranchWithin_weaken
    (Q_t' := codeStationRej aB newSp oB aLen acctBytes G F)
    (fun _ x => x)
    (fun h hq => by
      have hq' :
          (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
           (itemRej aB newSp acctBytes F **
            (G **
             ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
             ((oB + 72) ↦ₘ (0 : Word)) ** memOwn (newSp + 64) **
             memOwn (newSp + 72) ** ((.x8 : Reg) ↦ᵣ aB) **
             ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB)))) h := by
        dsimp only [H] at hq
        xperm_hyp hq
      have hqOwn := sepConj_mono (regIs_implies_regOwn .x19)
        (sepConj_mono (regIs_implies_regOwn .x20) (fun _ x => x)) h hq'
      exact item5Reject_to_codeStationRej aB newSp oB aLen
        acctBytes G F h (by xperm_hyp hqOwn))
    (fun _ x => x) hiF
  let SpanPre : Word → Word → Assertion := fun n5 l5 =>
    (((.x10 : Reg) ↦ᵣ n5) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
     ((.x12 : Reg) ↦ᵣ l5) ** ((.x19 : Reg) ↦ᵣ v19) **
     ((.x20 : Reg) ↦ᵣ v20) ** ((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 48) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
     memOwn (newSp + 64) ** memOwn (newSp + 72) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
     ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
     ((.x18 : Reg) ↦ᵣ oB) ** G **

     ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
     ((oB + 72) ↦ₘ (0 : Word)) ** bytesRegion aB acctBytes ** F)
  let ItemSuccess : Assertion := fun h => ∃ n5 l5 : Word,
    (SpanPre n5 l5 **
     ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
       (aB + BitVec.ofNat 64 aLen) n5 l5⌝) h
  have hcont : cpsBranchWithin
      (98 * (aLen + 1) + (7 * acctBytes.length + 700))
      (B + 556) bansfCR ItemSuccess
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724) (codeStationOuterPost aB newSp oB aLen off acctBytes G F) := by
    refine cpsBranchWithin_exists_pre (fun n5 => ?_)
    refine cpsBranchWithin_exists_pre (fun l5 => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hc := bansf_codeStationCont556_spec aB newSp oB aLen off
      n5 l5 (aB + BitVec.ofNat 64 off) v19 v20 acctBytes G F hG hF hsalign hslack hover hvalid hoff hdec
    refine cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun _ x => x) (fun h hq => ?_) hc
    unfold codeStationOuterPost
    exact ⟨n5, l5, (sepConj_pure_right h).2 ⟨hq, hdec⟩⟩
  have hcont' := cpsBranchWithin_weaken
    (fun h hp => by
      have hp' := codeItemFinalOk_to_cont556Pre aB newSp oB (aB + BitVec.ofNat 64 off) v19 v20 aLen off
        acctBytes G F h hp
      change ItemSuccess h
      obtain ⟨n5, l5, hp4⟩ := hp'
      refine ⟨n5, l5, ?_⟩
      dsimp only [SpanPre]
      xperm_hyp hp4)
    (fun _ x => x) (fun _ x => x) hcont
  have hcont'' := cpsBranchWithin_weaken
    (P' := codeItemFinalOk aB newSp (aB + BitVec.ofNat 64 off)
      aLen off acctBytes F ** H)
    (fun h hp => by dsimp only [H] at hp ⊢; xperm_hyp hp)
    (fun _ x => x) (fun _ x => x) hcont'
  have hfull := cpsBranchWithin_chain_snd hiW hcont''
  exact cpsBranchWithin_weaken
    (fun h hp => by
      unfold codeStationOuterBase at hp
      dsimp only [H, V8]
      xperm_hyp hp)
    (fun _ x => x) (fun _ x => x)
    (cpsBranchWithin_mono_nSteps (by omega) hfull)

#print axioms bansf_codeStation_spec


end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
