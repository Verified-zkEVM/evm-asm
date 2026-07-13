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

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
