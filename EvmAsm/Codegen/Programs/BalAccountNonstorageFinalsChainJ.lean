/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainJ

  Code-station continuation assembly for bal_account_nonstorage_finals.
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainI

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- At `B + 700`, materialize a successfully decoded tuple value as the
    selected code window. -/
theorem bansf_codeStationCont700_spec
    (aB newSp oB n5 : Word) (aLen tEnd off fOff fSpanN : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hFF : ∀ vNext vLen : Word,
      rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsTripleWithin 6 (B + 700) (B + 724) bansfCR
      (tupleValOk aB newSp tEnd off acctBytes F **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20))
      (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
  apply cpsTripleWithin_weaken
    (codeTupleValOk_to_materializePre aB newSp oB n5 aLen tEnd off acctBytes G F)
    (fun _ hq => hq)
  refine cpsTripleWithin_exists_pre_gen (fun vNext => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun vLen => ?_)
  let R : Assertion :=
    ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
    memOwn (newSp + 72) ** regOwn .x6 ** regOwn .x7 **
    regOwn .x28 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
    bytesRegion aB acctBytes ** ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** regOwn .x19 ** regOwn .x20 **
    ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
      (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝ ** F ** G
  let P : Assertion :=
    ((.x10 : Reg) ↦ᵣ vNext) ** ((.x12 : Reg) ↦ᵣ vLen) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x18 : Reg) ↦ᵣ oB) **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** R
  apply cpsTripleWithin_weaken (P := P ** regOwn .x29 ** regOwn .x5)
    (fun h hp => by dsimp only [P, R]; xperm_hyp hp) (fun _ hq => hq)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2
    (r1 := .x29) (r2 := .x5) (fun v29 v5 => ?_)
  have hm := bansf_codeMaterialize175_spec aB oB vNext vLen v29 v5
  have hmF := cpsTripleWithin_frameR R (by
    dsimp only [R]
    pcf
    exact hF
    exact hG) hm
  exact cpsTripleWithin_weaken (fun h hp => by dsimp only [R]; xperm_hyp hp)
    (fun h hq => by
      have hq' :
          ((((.x10 : Reg) ↦ᵣ vNext) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ vLen) ** ((.x8 : Reg) ↦ᵣ aB) **
           ((.x18 : Reg) ↦ᵣ oB) ** ((.x29 : Reg) ↦ᵣ (vNext - vLen - aB)) **
           ((.x5 : Reg) ↦ᵣ (1 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           ((oB + 56) ↦ₘ (1 : Word)) **
           ((oB + 64) ↦ₘ (vNext - vLen - aB)) ** ((oB + 72) ↦ₘ vLen) **
           ((.x2 : Reg) ↦ᵣ newSp) ** memOwn (newSp + 64) **
           memOwn (newSp + 72) ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
           regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
           bytesRegion aB acctBytes ** F ** G ** ((newSp + 48) ↦ₘ n5) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** regOwn .x19 ** regOwn .x20) **
          ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
            (aB + BitVec.ofNat 64 tEnd) vNext vLen⌝) h := by
        dsimp only [R] at hq
        xperm_hyp hq
      obtain ⟨hsp, hdec⟩ := (sepConj_pure_right h).1 hq'
      exact codeMaterialized_to_stationPost aB newSp oB n5 vNext vLen aLen
        fOff fSpanN acctBytes G F (hFF vNext vLen hdec) h hsp) hmF

#print axioms bansf_codeStationCont700_spec

/-- A rejected code value item carries the untouched station frame needed for
    the shared code-station reject boundary. -/
theorem codeTupleReject_to_stationRej (aB newSp oB n5 : Word)
    (aLen : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (tupleRej aB newSp acctBytes F **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h →
      codeStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold tupleRej at hq
  have hq2 :
      ((((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((.x10 : Reg) ↦ᵣ (1 : Word))) **
       (G ** ((.x2 : Reg) ↦ᵣ newSp) **
        memOwn (newSp + 64) ** memOwn (newSp + 72) **
        ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
        ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hq3 := sepConj_mono
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn (fun _ x => x))))))
    (fun _ x => x) h hq2
  unfold codeStationRej
  xperm_hyp hq3

#print axioms codeTupleReject_to_stationRej

/-- Slots 163–164 (`B + 652 → B + 660`): spill the code tuple cursor and
    end before decoding its index item. -/
theorem bansf_codeTupleSpill163_spec (newSp v10 v11 : Word) :
    cpsTripleWithin 2 (B + 652) (B + 660) bansfCR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ v10) ** ((newSp + 72) ↦ₘ v11)) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp v10
    (64 : BitVec 12) (B + 652)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 652) + 4 = B + 656 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 652) bansfProg 163
        (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp v11
    (72 : BitVec 12) (B + 656)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 656) + 4 = B + 660 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 656) bansfProg 164
        (.SD .x2 .x11 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have hsd1F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** memOwn (newSp + 72)) (by pcf) hsd1L
  have hsd2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ v10) ** ((newSp + 64) ↦ₘ v10)) (by pcf) hsd2L
  have hchain := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsd1F hsd2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_codeTupleSpill163_spec


theorem bansf_codeTupleItem0_spec (aB newSp : Word) (aLen off : Nat)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v10 v11 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hoffle : off ≤ aLen) :
    cpsBranchWithin 93 (B + 660) bansfCR
      (((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 680) (tupleOk aB newSp aLen off acctBytes F) := by
  have hoffb : off < acctBytes.length := by omega
  -- LD a0, 48(sp) ; LD a1, 56(sp)  (B+104, B+108)
  have hld1 := ld_spec_gen_within .x10 .x2 newSp v10 (aB + BitVec.ofNat 64 off)
    (64 : BitVec 12) (B + 660) (by decide)
  rw [(show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide), show (B + 660) + 4 = B + 664 from by bv_omega] at hld1
  have hld1L := liftCode (cr' := bansfCR) hld1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 660) bansfProg 165 (.LD .x10 .x2 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have hld2 := ld_spec_gen_within .x11 .x2 newSp v11 (aB + BitVec.ofNat 64 aLen)
    (72 : BitVec 12) (B + 664) (by decide)
  rw [(show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide), show (B + 664) + 4 = B + 668 from by bv_omega] at hld2
  have hld2L := liftCode (cr' := bansfCR) hld2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 664) bansfProg 166 (.LD .x11 .x2 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  have hld1F := cpsTripleWithin_frameR
    (((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** ((.x11 : Reg) ↦ᵣ v11))
    (by pcf) hld1L
  have hld2F := cpsTripleWithin_frameR
    (((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)))
    (by pcf) hld2L
  have hlds := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hld1F hld2F
  have hldsF := cpsTripleWithin_frameR
    (((.x12 : Reg) ↦ᵣ v12) **
     ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
     ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
     bytesRegion aB acctBytes ** F)
    (by pcf; exact hF) hlds
  -- the callee triple with ra = B + 668 + 4
  have hwn := rlp_walk_next_spec_within WN aB (aB + BitVec.ofNat 64 aLen)
    (B + 668 + 4) v12 v5 v6 v7 v28 v29 v30 v31 acctBytes off hsalign hoffb (by omega)
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
    (P' := ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 off)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 aLen)) ** ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite167_walk_next (n := 87) vRa (by pcf) hwn'
  rw [show (B + 668) + 4 = B + 672 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ newSp) **
     ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
     ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** F)
    (by pcf; exact hF) hcall
  have hpre := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hldsF hcallF
  -- ===== ok continuation: BNE falls through, SD spills the cursor =====
  have hokc : cpsBranchWithin 2 (B + 672) bansfCR
      (fun h => ∃ next len : Word,
        ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
           (aB + BitVec.ofNat 64 aLen) next len⌝) h)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 680) (tupleOk aB newSp aLen off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun next => ?_)
    refine cpsBranchWithin_exists_pre (fun len => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hdec => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (60 : BitVec 13) (0 : Word) (0 : Word) (B + 672)
    rw [show (B + 672) + 4 = B + 676 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 672) bansfProg 168 (.BNE .x11 .x0 (60 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) a i h))
      hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    -- SD a0, 48(sp) at B+120
    have hsd := sd_spec_gen_within .x2 .x10 newSp next (aB + BitVec.ofNat 64 off)
      (64 : BitVec 12) (B + 676)
    rw [(show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide), show (B + 676) + 4 = B + 680 from by bv_omega] at hsd
    have hsdL := liftCode (cr' := bansfCR) hsd
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 676) bansfProg 169 (.SD .x2 .x10 (64 : BitVec 12))
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) a i h))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ next) ** ((.x12 : Reg) ↦ᵣ len) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hsdF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ len) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hsdL
    have hout : cpsTripleWithin 2 (B + 672) (B + 680) bansfCR
        (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
         ((.x12 : Reg) ↦ᵣ len) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
         bytesRegion aB acctBytes ** F)
        (tupleOk aB newSp aLen off acctBytes F) := by
      have hchain := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          have hp2 := sepConj_mono_left (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp2)
        hfallF hsdF
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold tupleOk
      refine ⟨next, len, ?_⟩
      have hq2 : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ next) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
          bytesRegion aB acctBytes ** F)) h := by
        xperm_hyp hq
      have hq3 : ((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
          ((.x12 : Reg) ↦ᵣ len) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ next) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
          bytesRegion aB acctBytes ** F)) h := by
        have hq4 : ((((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
            (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
             ((.x12 : Reg) ↦ᵣ len) **
             ((.x2 : Reg) ↦ᵣ newSp) **
             ((newSp + 64) ↦ₘ next) **
             ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
             regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
             regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
             ((.x0 : Reg) ↦ᵣ (0 : Word)) **
             bytesRegion aB acctBytes ** F))) h := by
          xperm_hyp hq2
        have hq5 := sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x) h hq4
        xperm_hyp hq5
      exact (sepConj_pure_right h).2 ⟨hq3, hdec⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right _ _ hout)
  -- ===== fail continuation =====
  have hfailc : cpsBranchWithin 2 (B + 672) bansfCR
      (fun h => ∃ cur k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x2 : Reg) ↦ᵣ newSp) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (tupleRej aB newSp acctBytes F)
      (B + 680) (tupleOk aB newSp aLen off acctBytes F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    have hbne := bne_spec_gen_within .x11 .x0 (60 : BitVec 13) k (0 : Word) (B + 672)
    rw [show (B + 672) + signExtend13 (60 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (60 : BitVec 13) = (60 : Word) from by decide]
          bv_omega,
        show (B + 672) + 4 = B + 676 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 672) bansfProg 168 (.BNE .x11 .x0 (60 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
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
       ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 672) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ k) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
         bytesRegion aB acctBytes ** F)
        (tupleRej aB newSp acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold tupleRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ k) ** ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
          ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
          ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
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
          (cpsBranchWithin_pre_or hokc hfailc))))
  -- pointwise: collapse the six callee arms into ok ∨ fail
  obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
  have rebuild : ∀ (arm : Assertion), arm h4 →
      ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) ** bytesRegion aB acctBytes) ** arm) **
        (((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) ** F))) h :=
    fun arm ha => ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ha⟩, hEx⟩
  rcases hor with a1 | a2 | a3 | a4 | a5 | a6
  · -- ok arm: rlpWalkNextOk
    obtain ⟨next, len, hpins⟩ := a1
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
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
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
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
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
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
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
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
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
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
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
        ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 off)) **
        ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 668 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
#print axioms bansf_codeTupleItem0_spec



@[irreducible]
def codeCont680Pre (aB newSp oB n5 : Word) (aLen tEnd off : Nat)
    (acctBytes : List (BitVec 8)) (G F : Assertion) : Assertion :=
  fun h => ∃ next len : Word,
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
       ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ next) **
       ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
       ((newSp + 48) ↦ₘ n5) **
       ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
       ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
       ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
       ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
       ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion aB acctBytes ** G ** F) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
     ⌜rlpItemDecode acctBytes off (aB + BitVec.ofNat 64 off)
       (aB + BitVec.ofNat 64 tEnd) next len⌝) h

/-- Folded adapter from the code index-item success post to `Cont680`. -/
theorem codeTupleOk_to_cont680Pre (aB newSp oB n5 : Word)
    (aLen tEnd off : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (tupleOk aB newSp tEnd off acctBytes F **
        (G **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h →
      codeCont680Pre aB newSp oB n5 aLen tEnd off acctBytes G F h := by
  intro h hp
  unfold tupleOk at hp
  obtain ⟨g1, g2, gd, gu, hVal, hfr⟩ := hp
  obtain ⟨next, len, hVal2⟩ := hVal
  obtain ⟨hregs, hdec⟩ := (sepConj_pure_right g1).1 hVal2
  have hR := (⟨g1, g2, gd, gu, hregs, hfr⟩ :
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)) h))
  delta codeCont680Pre
  refine ⟨next, len, (sepConj_pure_right h).2 ⟨?_, hdec⟩⟩
  let L : Assertion :=
    (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
      bytesRegion aB acctBytes ** F) **
     (G **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20)))
  let R : Assertion :=
    (((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
      ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
      ((newSp + 64) ↦ₘ next) **
      ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
      ((newSp + 48) ↦ₘ n5) **
      ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
      ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
      ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
      ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
      ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion aB acctBytes ** G ** F) **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1
  have hL : L h := by dsimp only [L]; exact hR
  have heq : L = R := by dsimp only [L, R]; xperm
  change R h
  exact (congrFun heq h).mp hL

#print axioms codeTupleOk_to_cont680Pre

/-- Continuation at `B + 680`: decode the code tuple's value item and
    materialize its selected byte window. -/
theorem bansf_codeStationCont680_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n5 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF2 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 110) (B + 680) bansfCR
      (fun h => ∃ next len : Word,
        (((((.x10 : Reg) ↦ᵣ next) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
           ((.x12 : Reg) ↦ᵣ len) ** ((.x2 : Reg) ↦ᵣ newSp) **
           ((newSp + 64) ↦ₘ next) **
           ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
           ((newSp + 48) ↦ₘ n5) **
           ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
           ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
           ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
           ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
           ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** G ** F) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1) **
         ⌜rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
           (aB + BitVec.ofNat 64 tEnd) next len⌝) h)
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724)
        (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
  refine cpsBranchWithin_exists_pre (fun next => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_pure_pre_right (fun hdecI => ?_)
  obtain ⟨hrepI, _, hleI⟩ := rlpItemDecode_advance hdecI hoffleI (by omega)
  set offN := (next - aB).toNat with hoffN
  rw [hrepI]
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  have hti := bansf_codeTupleItem1_spec aB newSp aLen tEnd offN acctBytes
    v5 v6 v7 (aB + BitVec.ofNat 64 offN) 0 len v28 v29 v30 v31 vRa F hF
    hsalign hslack hover hvalid htEnd hleI
  let H : Assertion :=
    G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20
  have hHF : H.pcFree := by dsimp only [H]; pcf; exact hG; pcf
  have htiF := cpsBranchWithin_frameR H hHF hti
  have hc700 := bansf_codeStationCont700_spec aB newSp oB n5 aLen tEnd offN
    fOff fSpanN acctBytes G F hG hF
    (fun vNext vLen hdecV =>
      hFF2 next len vNext vLen hdecI (by rw [← hoffN, hrepI]; exact hdecV))
  have hc700' := cpsTripleWithin_weaken
    (P' := tupleValOk aB newSp tEnd offN acctBytes F ** H)
    (fun h hp => by dsimp only [H] at hp ⊢; xperm_hyp hp)
    (fun _ hq => hq) hc700
  have hc700B := cpsTripleWithin_as_cpsBranchWithin_right (B + 736)
    (codeStationRej aB newSp oB aLen acctBytes G F) hc700'
  have htiW := cpsBranchWithin_weaken
    (Q_t' := codeStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => codeTupleReject_to_stationRej
      aB newSp oB n5 aLen acctBytes G F h (by dsimp only [H] at hq; exact hq))
    (fun _ hq => hq) htiF
  have hchain := cpsBranchWithin_chain_snd htiW hc700B
  exact cpsBranchWithin_weaken (fun h hp => by dsimp only [H]; xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_mono_nSteps (by omega) hchain)

#print axioms bansf_codeStationCont680_spec

/-- Continuation at `B + 660`: decode the code tuple's index item, then its
    value item, and materialize the selected window. -/
theorem bansf_codeStationCont660_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n5 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF3 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 203) (B + 660) bansfCR
      ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 offI)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 tEnd)) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
         ((newSp + 64) ↦ₘ (aB + BitVec.ofNat 64 offI)) **
         ((newSp + 72) ↦ₘ (aB + BitVec.ofNat 64 tEnd)) **
         ((newSp + 48) ↦ₘ n5) **
         ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
         ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
         ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
         ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
         ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion aB acctBytes ** G ** F) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1)
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724)
        (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
  refine cpsBranchWithin_of_forall_regIs_to_regOwn8
    (fun v5 v6 v7 v28 v29 v30 v31 vRa => ?_)
  have hti := bansf_codeTupleItem0_spec aB newSp tEnd offI acctBytes
    v5 v6 v7 (aB + BitVec.ofNat 64 offI) (aB + BitVec.ofNat 64 tEnd) 0
    v28 v29 v30 v31 vRa F hF hsalign (by omega) hover hvalid hoffleI
  let H : Assertion :=
    G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20
  have hHF : H.pcFree := by dsimp only [H]; pcf; exact hG; pcf
  have htiF := cpsBranchWithin_frameR H hHF hti
  have hc680 := bansf_codeStationCont680_spec aB newSp oB aLen tEnd offI
    fOff fSpanN n5 acctBytes G F hG hF hsalign hslack hover hvalid htEnd
    hoffleI hFF3
  have hc680F := cpsBranchWithin_weaken
    (P' := codeCont680Pre aB newSp oB n5 aLen tEnd offI acctBytes G F)
    (fun _ hp => by delta codeCont680Pre at hp; exact hp)
    (fun _ hq => hq) (fun _ hq => hq) hc680
  have hc680' := cpsBranchWithin_weaken
    (codeTupleOk_to_cont680Pre aB newSp oB n5 aLen tEnd offI acctBytes G F)
    (fun _ hq => hq) (fun _ hq => hq) hc680F
  have htiW := cpsBranchWithin_weaken
    (Q_t' := codeStationRej aB newSp oB aLen acctBytes G F)
    (fun _ hp => hp)
    (fun h hq => codeTupleReject_to_stationRej
      aB newSp oB n5 aLen acctBytes G F h (by dsimp only [H] at hq; exact hq))
    (fun _ hq => hq) htiF
  have hchain := cpsBranchWithin_chain_snd htiW hc680'
  exact cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_mono_nSteps (by omega) hchain)

#print axioms bansf_codeStationCont660_spec

/-- Continuation at `B + 652`: spill the code tuple cursor/end, then decode
    its index and value items. -/
theorem bansf_codeStationCont652_spec (aB newSp oB : Word)
    (aLen tEnd offI fOff fSpanN : Nat) (n5 : Word)
    (acctBytes : List (BitVec 8)) (G F : Assertion)
    (hG : G.pcFree) (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (htEnd : tEnd ≤ aLen) (hoffleI : offI ≤ tEnd)
    (hFF3 : ∀ iNext iLen vNext vLen : Word,
      rlpItemDecode acctBytes offI (aB + BitVec.ofNat 64 offI)
        (aB + BitVec.ofNat 64 tEnd) iNext iLen →
      rlpItemDecode acctBytes ((iNext - aB).toNat) iNext
        (aB + BitVec.ofNat 64 tEnd) vNext vLen →
      FieldFinal acctBytes aB fOff fSpanN (some (vNext, vLen))) :
    cpsBranchWithin (7 * acctBytes.length + 205) (B + 652) bansfCR
      ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 offI)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 tEnd)) **
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
         bytesRegion aB acctBytes ** G ** F))
      (B + 736) (codeStationRej aB newSp oB aLen acctBytes G F)
      (B + 724)
        (codeStationPost aB newSp oB aLen fOff fSpanN n5 acctBytes G F) := by
  have hsp := bansf_codeTupleSpill163_spec newSp
    (aB + BitVec.ofNat 64 offI) (aB + BitVec.ofNat 64 tEnd)
  let H : Assertion :=
    ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
    ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
    ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
    ((.x18 : Reg) ↦ᵣ oB) ** regOwn .x19 ** regOwn .x20 **
    ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
    ((oB + 72) ↦ₘ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
    regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** regOwn .x1 **
    bytesRegion aB acctBytes ** G ** F
  have hH : H.pcFree := by dsimp only [H]; pcf; exact hG; exact hF
  have hspF := cpsTripleWithin_frameR H hH hsp
  have hc := bansf_codeStationCont660_spec aB newSp oB aLen tEnd offI
    fOff fSpanN n5 acctBytes G F hG hF hsalign hslack hover hvalid htEnd
    hoffleI hFF3
  have hfull := cpsTripleWithin_seq_branch_same_cr hspF
    (cpsBranchWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun _ hq => hq) (fun _ hq => hq) hc)
  exact cpsBranchWithin_mono_nSteps (by omega) hfull

#print axioms bansf_codeStationCont652_spec


theorem bansf_codeTupleInit161_spec (aB : Word) (aLen fOff : Nat) (fSpanW : Word)
    (acctBytes : List (BitVec 8))
    (v5 v6 v7 v12 v28 v29 v30 v31 vRa : Word) (F : Assertion)
    (hF : F.pcFree)
    (hsalign : aB.toNat % 8 = 0)
    (hslack : aLen + 9 ≤ acctBytes.length)
    (hover : aB.toNat + acctBytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < acctBytes.length →
      isValidByteAccess (aB + BitVec.ofNat 64 k) = true)
    (hfB : fOff + fSpanW.toNat ≤ aLen) :
    cpsBranchWithin 84 (B + 644) bansfCR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
       ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ vRa) **
       bytesRegion aB acctBytes ** F)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 652) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 644 + 4) F) := by
  have hoffb : fOff < acctBytes.length := by omega
  have hovOff : aB.toNat + fOff < 2 ^ 64 := by omega
  -- the callee triple at its entry with ra = B + 644 + 4
  have hwi := rlp_walk_init_spec_within WI aB (B + 644 + 4) fSpanW
    v12 v5 v6 v7 v28 v29 v30 v31 acctBytes fOff hsalign hoffb hovOff
    (hvalid fOff hoffb)
    (fun hf8 => by
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      omega)
    (fun hf8 => by
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      omega)
    (fun hf8 => by
      intro k hk
      have hlo : ((acctBytes[fOff]'hoffb).zeroExtend 64 - (0xf7 : Word)).toNat ≤ 8 := by
        have h2 := not_ult_le hf8
        have h3 := (acctBytes[fOff]'hoffb).isLt
        bv_omega
      exact hvalid _ (by omega))
  have hwi' := cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) hwi
    (P' := ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) ** ((.x11 : Reg) ↦ᵣ fSpanW) **
       ((.x12 : Reg) ↦ᵣ v12) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
       ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
       ((.x30 : Reg) ↦ᵣ v30) ** ((.x31 : Reg) ↦ᵣ v31) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion aB acctBytes))
  have hcall := bansf_callSite161_walk_init (n := 81) vRa (by pcf) hwi'
  rw [show (B + 644) + 4 = B + 648 from by bv_omega] at hcall
  have hcallF := cpsTripleWithin_frameR F hF hcall
  set bb : BitVec 8 := acctBytes[fOff]'hoffb with hbb
  -- the window-end bridge: ptr + span = aB + ofNat (fOff + span.toNat)
  have hendB : (aB + BitVec.ofNat 64 fOff) + fSpanW
      = aB + BitVec.ofNat 64 (fOff + fSpanW.toNat) := by
    bv_omega
  -- ===== the success continuation (status pinned 0) =====
  have hsucc : cpsBranchWithin 2 (B + 648) bansfCR
      (fun h => ∃ cOff : Nat,
        ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜FieldInitOk acctBytes fOff fSpanW.toNat cOff⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 652) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 644 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cOff => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hok => ?_)
    have hbne := bne_spec_gen_within .x12 .x0 (84 : BitVec 13) (0 : Word) (0 : Word) (B + 648)
    rw [show (B + 648) + 4 = B + 652 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 648) bansfProg 162 (.BNE .x12 .x0 (84 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
      hbne
    have hfall := cpsBranchWithin_ntakenPath hbneL
      (fun hp hQt => by
        obtain ⟨_, _, _, _, _, h_pure⟩ := hQt
        exact absurd rfl (((sepConj_pure_right _).1 h_pure).2))
    have hfallF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
       ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
       bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hfall
    have hout : cpsTripleWithin 1 (B + 648) (B + 652) bansfCR
        (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
         ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
         ((.x12 : Reg) ↦ᵣ (0 : Word)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 644 + 4) F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hfallF
      unfold fieldInitPost
      refine ⟨cOff, ?_⟩
      have hq2 : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 cOff)) **
          ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
          ((.x12 : Reg) ↦ᵣ (0 : Word)) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
          bytesRegion aB acctBytes ** F)) h := by
        have hq3 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
        xperm_hyp hq3
      exact (sepConj_pure_right h).2 ⟨hq2, hok⟩
    exact cpsBranchWithin_mono_nSteps (by omega)
      (cpsTripleWithin_as_cpsBranchWithin_right _ _ hout)
  -- ===== the failure continuation (status pinned non-zero) =====
  have hfailc : cpsBranchWithin 2 (B + 648) bansfCR
      (fun h => ∃ cur endW k : Word,
        ((((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
          ((.x12 : Reg) ↦ᵣ k) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
          bytesRegion aB acctBytes ** F) **
         ⌜k ≠ (0 : Word)⌝) h)
      (B + 736) (fieldRej aB acctBytes F)
      (B + 652) (fieldInitPost aB fOff fSpanW.toNat acctBytes (B + 644 + 4) F) := by
    refine cpsBranchWithin_exists_pre (fun cur => ?_)
    refine cpsBranchWithin_exists_pre (fun endW => ?_)
    refine cpsBranchWithin_exists_pre (fun k => ?_)
    refine cpsBranchWithin_pure_pre_right (fun hk => ?_)
    -- the BNE at slot 51: taken (status ≠ 0) to the reject stub
    have hbne := bne_spec_gen_within .x12 .x0 (84 : BitVec 13) k (0 : Word) (B + 648)
    rw [show (B + 648) + signExtend13 (84 : BitVec 13) = B + 732 from by
          rw [show signExtend13 (84 : BitVec 13) = (84 : Word) from by decide]
          bv_omega,
        show (B + 648) + 4 = B + 652 from by bv_omega] at hbne
    have hbneL := cpsBranchWithin_extend_code (cr' := bansfCR)
      (fun a i h => CodeReq.union_mono_left a i
        (CodeReq.ofProg_mem_at B (B + 648) bansfProg 162 (.BNE .x12 .x0 (84 : BitVec 13))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) a i h))
      hbne
    have hbneF := cpsBranchWithin_frameR
      (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) ** bytesRegion aB acctBytes ** F)
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
       ((.x11 : Reg) ↦ᵣ endW) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
       ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) ** bytesRegion aB acctBytes ** F)
      (by pcf; exact hF) hrej
    have hchain := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp2 := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp2)
      htaken hrejF
    have hout : cpsTripleWithin 2 (B + 648) (B + 736) bansfCR
        (((.x10 : Reg) ↦ᵣ cur) ** ((.x11 : Reg) ↦ᵣ endW) **
         ((.x12 : Reg) ↦ᵣ k) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
         bytesRegion aB acctBytes ** F)
        (fieldRej aB acctBytes F) := by
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) hchain
      unfold fieldRej
      have hq4 : ((((.x11 : Reg) ↦ᵣ endW) ** ((.x12 : Reg) ↦ᵣ k) **
          ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
          (((.x10 : Reg) ↦ᵣ (1 : Word)) **
           regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
           regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
           ((.x0 : Reg) ↦ᵣ (0 : Word)) **
           bytesRegion aB acctBytes ** F))) h := by
        xperm_hyp hq
      have hq5 := sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12)
          (sepConj_mono (regIs_implies_regOwn .x1) (fun _ x => x))) h hq4
      xperm_hyp hq5
    exact cpsTripleWithin_as_cpsBranchWithin_left _ _ hout
  -- ===== chain: call ; (success ∨ failure) =====
  refine cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp) (fun _ x => x) (fun _ x => x)
    (cpsTripleWithin_seq_branch_same_cr hcallF
      (cpsBranchWithin_weaken (fun h hp => ?_) (fun _ x => x) (fun _ x => x)
        (cpsBranchWithin_pre_or hsucc hfailc)))
  -- pointwise: collapse the nine callee arms into success ∨ failure
  obtain ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, hor⟩, hEx⟩ := hp
  have rebuild : ∀ (arm : Assertion), arm h4 →
      ((((regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
          regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) ** bytesRegion aB acctBytes) ** arm) ** F)) h :=
    fun arm ha => ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hCF, ha⟩, hEx⟩
  rcases hor with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9
  · -- fail arm: status 2 (empty span)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (0 : Word), (2 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a1
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) ** ((.x12 : Reg) ↦ᵣ (2 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ (2 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 1 (not a list)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (1 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a2
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (1 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (1 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- short-list success (status 0)
    refine Or.inl ⟨fOff + 1, ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a3
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, hfacts⟩ := (sepConj_pure_right g4).1 grest2
    obtain ⟨hne0, hge0c, hf8, hcons⟩ := hfacts
    have hx10' : ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + 1))) g1 := by
      rwa [show (aB + BitVec.ofNat 64 fOff) + signExtend12 (1 : BitVec 12)
          = aB + BitVec.ofNat 64 (fOff + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega] at hx10
    have hx11' : ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) g3 := by
      rwa [hendB] at hx11
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + 1))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10', g3, g4, gd2, gu2, hx11', hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + 1))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    refine (sepConj_pure_right h).2 ⟨hflat,
      ⟨bb, List.getElem?_eq_getElem hoffb, ?_, by omega, ?_⟩⟩
    · -- listHeaderSize bb = 1: short-form prefix
      have hlt := ult_lt hf8
      have hzb : (bb.zeroExtend 64).toNat = bb.toNat := by bv_omega
      unfold listHeaderSize
      rw [if_pos (by
        rw [show ((0xf8 : Word)).toNat = 0xf8 from rfl] at hlt
        omega)]
    · -- 1 ≤ span: the consistency equation forces a non-trivial span
      have hlen1 : ((bb.zeroExtend 64 - (0xc0 : Word)) + signExtend12 (1 : BitVec 12))
          = fSpanW := by
        have := hcons
        bv_omega
      have h1 : 1 ≤ fSpanW.toNat := by
        have hgec := not_ult_le hge0c
        rw [← hlen1, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
        bv_omega
      omega
  · -- fail arm: status 3 (short mismatch)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (3 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a4
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (3 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (3 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 4 (long truncated)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (4 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a5
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (4 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (4 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 5 (long leading zero)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (5 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a6
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (5 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (5 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 6 (long non-minimal)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (6 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a7
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (6 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (6 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- fail arm: status 7 (long mismatch)
    refine Or.inr ⟨aB + BitVec.ofNat 64 fOff, (aB + BitVec.ofNat 64 fOff) + fSpanW,
      (7 : Word), ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a8
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, _⟩ := (sepConj_pure_right g4).1 grest2
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (7 : Word)))
      ⟨g1, g2, gd1, gu1, hx10, g3, g4, gd2, gu2, hx11, hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 fOff)) **
        ((.x11 : Reg) ↦ᵣ ((aB + BitVec.ofNat 64 fOff) + fSpanW)) **
        ((.x12 : Reg) ↦ᵣ (7 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    exact (sepConj_pure_right h).2 ⟨hflat, by decide⟩
  · -- long-list success (status 0)
    refine Or.inl ⟨fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
      signExtend12 (1 : BitVec 12)).toNat, ?_⟩
    obtain ⟨g1, g2, gd1, gu1, hx10, grest⟩ := a9
    obtain ⟨g3, g4, gd2, gu2, hx11, grest2⟩ := grest
    obtain ⟨hx12, hfacts⟩ := (sepConj_pure_right g4).1 grest2
    obtain ⟨hne0, hnc0, hnf8, hfit, hmin5, hsum6⟩ := hfacts
    clear hmin5 hsum6 hnc0
    have hgef8 := not_ult_le hnf8
    rw [show ((0xf8 : Word)).toNat = 0xf8 from rfl] at hgef8
    have hzb : (bb.zeroExtend 64).toNat = bb.toNat := by bv_omega
    have hhdrN : ((bb.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12)).toNat
        = 1 + (bb.toNat - 0xf7) := by
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      have hb := bb.isLt
      bv_omega
    have hx10' : ((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
        (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat))) g1 := by
      rwa [show (aB + BitVec.ofNat 64 fOff) +
          ((bb.zeroExtend 64 - (0xf7 : Word)) + signExtend12 (1 : BitVec 12))
          = aB + BitVec.ofNat 64
            (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
              signExtend12 (1 : BitVec 12)).toNat) from by
        bv_omega] at hx10
    have hx11' : ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) g3 := by
      rwa [hendB] at hx11
    have hR := rebuild (((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
        (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)))
      ⟨g1, g2, gd1, gu1, hx10', g3, g4, gd2, gu2, hx11', hx12⟩
    have hflat : ((((.x10 : Reg) ↦ᵣ (aB + BitVec.ofNat 64
        (fOff + ((bb.zeroExtend 64 - (0xf7 : Word)) +
          signExtend12 (1 : BitVec 12)).toNat))) **
        ((.x11 : Reg) ↦ᵣ (aB + BitVec.ofNat 64 (fOff + fSpanW.toNat))) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x1 : Reg) ↦ᵣ (B + 644 + 4)) **
        bytesRegion aB acctBytes ** F)) h := by
      xperm_hyp hR
    refine (sepConj_pure_right h).2 ⟨hflat,
      ⟨bb, List.getElem?_eq_getElem hoffb, ?_, ?_, ?_⟩⟩
    · -- listHeaderSize bb = 1 + (bb - 0xf7): long-form prefix
      unfold listHeaderSize
      rw [if_neg (by omega), hhdrN]
    · -- strictly past the header
      rw [hhdrN]
      omega
    · -- header fits inside the window
      rw [hhdrN]
      have hfit' := not_ult_le hfit
      rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at hfit'
      have hb := bb.isLt
      bv_omega


#print axioms bansf_codeTupleInit161_spec

/-- Normalize a rejected code tuple `walk_init` to the shared station reject boundary. -/
theorem codeTupleInitReject_to_stationRej
    (aB newSp oB n5 v19 v20 s64 s72 : Word)
    (aLen : Nat) (acctBytes : List (BitVec 8)) (G F : Assertion) :
    ∀ h,
      (fieldRej aB acctBytes F **
       (G ** ((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((newSp + 64) ↦ₘ s64) ** ((newSp + 72) ↦ₘ s72) **
        ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        ((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20))) h →
      codeStationRej aB newSp oB aLen acctBytes G F h := by
  intro h hq
  unfold fieldRej at hq
  have hq2 :
      ((((oB + 56) ↦ₘ (0 : Word)) ** ((oB + 64) ↦ₘ (0 : Word)) **
        ((oB + 72) ↦ₘ (0 : Word)) ** ((newSp + 48) ↦ₘ n5) **
        ((newSp + 56) ↦ₘ (aB + BitVec.ofNat 64 aLen)) **
        ((newSp + 64) ↦ₘ s64) ** ((newSp + 72) ↦ₘ s72) **
        ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x19 : Reg) ↦ᵣ v19) **
        ((.x20 : Reg) ↦ᵣ v20)) **
       (G ** ((.x2 : Reg) ↦ᵣ newSp) ** ((.x8 : Reg) ↦ᵣ aB) **
        ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) ** ((.x18 : Reg) ↦ᵣ oB) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 **
        regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
        bytesRegion aB acctBytes ** F)) h := by
    xperm_hyp hq
  have hq3 := sepConj_mono
    (sepConj_mono memIs_implies_memOwn
      (sepConj_mono memIs_implies_memOwn
        (sepConj_mono memIs_implies_memOwn
          (sepConj_mono memIs_implies_memOwn
            (sepConj_mono memIs_implies_memOwn
              (sepConj_mono memIs_implies_memOwn
                (sepConj_mono memIs_implies_memOwn
                  (sepConj_mono (fun _ x => x)
                    (sepConj_mono (regIs_implies_regOwn .x19)
                      (regIs_implies_regOwn .x20))))))))))
    (fun _ x => x) h hq2
  unfold codeStationRej
  xperm_hyp hq3

#print axioms codeTupleInitReject_to_stationRej

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
