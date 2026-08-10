/-
  EvmAsm.Codegen.Programs.RlpItemSpanBody

  Body + whole-routine `cpsTripleWithin` for `rlp_item_span` under the
  short-list outer + WalkedSpanForm domain (#11577).

  Pattern: RlpListNthItemSAsmBase.setupMoves (B+N PCs, ofProg_mem_at,
  frameR, seq_perm, weaken xperm).

  Loop continue machinery lives in `RlpItemSpanLoop.lean` (file-size split).
-/

import EvmAsm.Codegen.Programs.RlpItemSpanLoop
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Codegen
namespace RlpItemSpanSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec
open EvmAsm.Codegen.MptSpliceSlotSpec

/-- Copy ABI args into callee-saved regs: MV s0,a0; ADD s1,a0,a1; MV s2..s4. -/
theorem setup_spec (newSp listBase listLenW indexW outStart outSize
    st sz raVal s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 : Word)
    (bs : List (BitVec 8)) :
    cpsTripleWithin 5 (B + 36) (B + 56) spanCr
      ((.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) **
       (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
       savedFrame newSp
         { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
           s4 := s4, s5 := s5, s6 := s6 } **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
      ((.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
       (.x9 ↦ᵣ (listBase + listLenW)) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
       savedFrame newSp
         { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
           s4 := s4, s5 := s5, s6 := s6 } **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) := by
  -- raw single-instr triples (normalize exit PCs to B+4k form)
  have h0 := mv_spec_gen_within .x8 .x10 listBase s0 (B + 36) (by decide)
  rw [show (B + 36 : Word) + 4 = B + 40 from by decide] at h0
  have h1 := add_spec_gen_within .x9 .x10 .x11 listBase listLenW s1 (B + 40) (by decide)
  rw [show (B + 40 : Word) + 4 = B + 44 from by decide] at h1
  have h2 := mv_spec_gen_within .x18 .x12 indexW s2 (B + 44) (by decide)
  rw [show (B + 44 : Word) + 4 = B + 48 from by decide] at h2
  have h3 := mv_spec_gen_within .x19 .x13 outStart s3 (B + 48) (by decide)
  rw [show (B + 48 : Word) + 4 = B + 52 from by decide] at h3
  have h4 := mv_spec_gen_within .x20 .x14 outSize s4 (B + 52) (by decide)
  rw [show (B + 52 : Word) + 4 = B + 56 from by decide] at h4
  -- lift into spanCr (same shape as RlpListNthItemSAsmBase.setupMoves)
  have l0 := cpsTripleWithin_extend_code
    (mem_at 9 (.MV .x8 .x10) (B + 36)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) h0
  have l1 := cpsTripleWithin_extend_code
    (mem_at 10 (.ADD .x9 .x10 .x11) (B + 40)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) h1
  have l2 := cpsTripleWithin_extend_code
    (mem_at 11 (.MV .x18 .x12) (B + 44)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) h2
  have l3 := cpsTripleWithin_extend_code
    (mem_at 12 (.MV .x19 .x13) (B + 48)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) h3
  have l4 := cpsTripleWithin_extend_code
    (mem_at 13 (.MV .x20 .x14) (B + 52)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) h4
  -- frames
  have f0 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x9 ↦ᵣ s1) ** (.x18 ↦ᵣ s2) **
     (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp
       { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
         s4 := s4, s5 := s5, s6 := s6 } **
     (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) ** (.x13 ↦ᵣ outStart) **
     (.x14 ↦ᵣ outSize) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) l0
  have f1 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp
       { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
         s4 := s4, s5 := s5, s6 := s6 } **
     (.x12 ↦ᵣ indexW) ** (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) l1
  have f2 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x9 ↦ᵣ (listBase + listLenW)) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp
       { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
         s4 := s4, s5 := s5, s6 := s6 } **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x13 ↦ᵣ outStart) **
     (.x14 ↦ᵣ outSize) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) l2
  have f3 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x9 ↦ᵣ (listBase + listLenW)) ** (.x18 ↦ᵣ indexW) ** (.x20 ↦ᵣ s4) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp
       { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
         s4 := s4, s5 := s5, s6 := s6 } **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
     (.x14 ↦ᵣ outSize) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) l3
  have f4 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x9 ↦ᵣ (listBase + listLenW)) ** (.x18 ↦ᵣ indexW) **
     (.x19 ↦ᵣ outStart) ** (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
     savedFrame newSp
       { ra := raVal, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
         s4 := s4, s5 := s5, s6 := s6 } **
     (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
     (.x13 ↦ᵣ outStart) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) l4
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 f1
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 f2
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 f3
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 f4
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp) c04

/-! ## Header → loop (idx 14..26 short path: B+56 → B+108) -/

private theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by bv_omega

/-- Short-list header path lands at loopHdr with cursor = listBase+1, k = 0. -/
theorem header_to_loop (newSp listBase endPtr indexW outStart outSize
    st sz raVal : Word) (saved : Saved) (items : List RLPItem)
    (v5 v6 v7 v10 v11 v12 v13 v14 s5 s6 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ k, k < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hlen_pos : 0 < (encode (.list items)).length) :
    cpsTripleWithin 8 (B + 56) (B + 108) spanCr
      ((.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
       savedFrame newSp saved **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
       (inv newSp listBase endPtr indexW outStart outSize st sz raVal
         saved items 0 v7 v10 v11 v12 v13 v14) := by
  set bs := encode (.list items)
  have hgetD : bs.getD 0 0 = bs[0]'hlen_pos := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_pos]; rfl
  have hlo : 0xc0 ≤ (bs[0]'hlen_pos).toNat := by
    have := short_list_head_lo items hshort
    rwa [← hgetD]
  have hhi : (bs[0]'hlen_pos).toNat < 0xf8 := by
    have := short_list_head_hi items hshort
    rwa [← hgetD]
  have hult_end : BitVec.ult listBase endPtr := by
    have hsum : (listBase + BitVec.ofNat 64 bs.length).toNat
        = listBase.toNat + bs.length := by
      have ha := listBase.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [h_end, BitVec.ult, decide_eq_true_eq, hsum]
    omega
  -- idx14 BGEU x8,x9,+112 @ B+56 — NOT taken → B+60
  have hbr14 := cpsBranchWithin_extend_code
    (mem_at 14 (.BGEU .x8 .x9 (112 : BitVec 13)) (B + 56)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bgeu_spec_gen_within .x8 .x9 (112 : BitVec 13) listBase endPtr (B + 56))
  rw [show (B + 56 : Word) + signExtend13 (112 : BitVec 13) = B + 168 from by
        rw [show signExtend13 (112 : BitVec 13) = (112 : Word) from by decide]; bv_omega,
      show (B + 56 : Word) + 4 = B + 60 from by decide] at hbr14
  have hnt14 := cpsBranchWithin_ntakenStripPure2 hbr14 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult_end)
  -- idx15 LBU x5,0(x8) @ B+60
  have hlbu := bytesRegion_lbu_within .x5 .x8 listBase v5 (B + 60) bs 0
    (by decide) h_align hlen_pos (by omega) (h_valid 0 hlen_pos)
  rw [add_ofNat_zero listBase] at hlbu
  have hlbu' := cpsTripleWithin_extend_code
    (mem_at 15 (.LBU .x5 .x8 (0 : BitVec 12)) (B + 60)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl)) hlbu
  rw [show (B + 60 : Word) + 4 = B + 64 from by decide] at hlbu'
  -- idx16 LI x6, 192 @ B+64
  have hli16 := cpsTripleWithin_extend_code
    (mem_at 16 (.LI .x6 (192 : Word)) (B + 64)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x6 v6 (192 : Word) (B + 64) (by decide))
  rw [show (B + 64 : Word) + 4 = B + 68 from by decide] at hli16
  -- idx17 BLTU x5,x6,+100 @ B+68 — NOT taken (head ≥ 0xc0)
  have hbr17 := cpsBranchWithin_extend_code
    (mem_at 17 (.BLTU .x5 .x6 (100 : BitVec 13)) (B + 68)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bltu_spec_gen_within .x5 .x6 (100 : BitVec 13)
      ((bs[0]'hlen_pos).zeroExtend 64) (192 : Word) (B + 68))
  rw [show (B + 68 : Word) + signExtend13 (100 : BitVec 13) = B + 168 from by
        rw [show signExtend13 (100 : BitVec 13) = (100 : Word) from by decide]; bv_omega,
      show (B + 68 : Word) + 4 = B + 72 from by decide] at hbr17
  have hnult17 : ¬ BitVec.ult ((bs[0]'hlen_pos).zeroExtend 64) (192 : Word) :=
    not_ult_zx_of_ge _ _ (by
      rw [show ((192 : Word)).toNat = 192 from by decide]; exact hlo)
  have hnt17 := cpsBranchWithin_ntakenStripPure2 hbr17 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact hnult17 ((sepConj_pure_right _).1 hQ).2)
  -- idx18 LI x6, 248 @ B+72
  have hli18 := cpsTripleWithin_extend_code
    (mem_at 18 (.LI .x6 (248 : Word)) (B + 72)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x6 (192 : Word) (248 : Word) (B + 72) (by decide))
  rw [show (B + 72 : Word) + 4 = B + 76 from by decide] at hli18
  -- idx19 BLTU x5,x6,+24 @ B+76 — TAKEN (head < 0xf8) → B+100
  have hbr19 := cpsBranchWithin_extend_code
    (mem_at 19 (.BLTU .x5 .x6 (24 : BitVec 13)) (B + 76)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bltu_spec_gen_within .x5 .x6 (24 : BitVec 13)
      ((bs[0]'hlen_pos).zeroExtend 64) (248 : Word) (B + 76))
  rw [show (B + 76 : Word) + signExtend13 (24 : BitVec 13) = B + 100 from by
        rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega,
      show (B + 76 : Word) + 4 = B + 80 from by decide] at hbr19
  have hult19 : BitVec.ult ((bs[0]'hlen_pos).zeroExtend 64) (248 : Word) :=
    ult_zx_of_lt _ _ (by
      rw [show ((248 : Word)).toNat = 248 from by decide]; exact hhi)
  have ht19 := cpsBranchWithin_takenStripPure2 hbr19 (fun _hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 hult19)
  -- idx25 ADDI x21,x8,1 @ B+100
  have haddi25 := cpsTripleWithin_extend_code
    (mem_at 25 (.ADDI .x21 .x8 (1 : BitVec 12)) (B + 100)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (addi_spec_gen_within .x21 .x8 s5 listBase (1 : BitVec 12) (B + 100) (by decide))
  rw [show (B + 100 : Word) + 4 = B + 104 from by decide] at haddi25
  -- idx26 LI x22, 0 @ B+104
  have hli26 := cpsTripleWithin_extend_code
    (mem_at 26 (.LI .x22 (0 : Word)) (B + 104)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x22 s6 (0 : Word) (B + 104) (by decide))
  rw [show (B + 104 : Word) + 4 = B + 108 from by decide] at hli26
  -- frames (stable ambient)
  set Fstable : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
  have f14 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt14
  have f15 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hlbu'
  have f16 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli16
  have f17 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt17
  have f18 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli18
  have f19 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) ht19
  have f25 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ s6) ** savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) **
     (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) haddi25
  have f26 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + signExtend12 (1 : BitVec 12))) **
     savedFrame newSp saved **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) **
     (.x6 ↦ᵣ (248 : Word)) ** (.x7 ↦ᵣ v7) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hli26
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f14 f15
  have c02 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 f16
  have c03 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c02 f17
  have c04 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c03 f18
  have c05 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c04 f19
  have c06 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c05 f25
  have c07 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c06 f26
  have hcur : listBase + signExtend12 (1 : BitVec 12)
      = listBase + BitVec.ofNat 64 (shortCursor items 0) := by
    rw [shortCursor_zero, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    rfl
  have hk0 : (0 : Word) = BitVec.ofNat 64 0 := rfl
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) c07
  -- Goal post is `inv` with regOwn x5/x6; drop concrete head/248 via regIs_implies_regOwn.
  simp only [inv, amb, shortCursor_zero]
  -- Flatten composed post, rewrite cursor/k, then mono x5/x6 to ownership.
  have hq1 :
      ((.x5 ↦ᵣ ((bs[0]'hlen_pos).zeroExtend 64)) **
       (.x6 ↦ᵣ (248 : Word)) **
       (.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz) **
       (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (.x21 ↦ᵣ (listBase + signExtend12 (1 : BitVec 12))) **
       (.x22 ↦ᵣ (0 : Word)) **
       (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h := by
    xperm_hyp hq
  rw [hcur, shortCursor_zero, hk0] at hq1
  have hown :
      ((regOwn .x5) ** (regOwn .x6) **
       (.x2 ↦ᵣ newSp) ** savedFrame newSp saved **
       (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
       (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz) **
       (.x1 ↦ᵣ raVal) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
       (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 1)) **
       (.x22 ↦ᵣ BitVec.ofNat 64 0) **
       (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)) h :=
    sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6) (fun _ hh => hh)) h hq1
  xperm_hyp hown

/-- Loop exit when `k = i`: BEQ taken → exitGate B+136. -/
theorem loop_exit
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v7 v10 v11 v12 v13 v14 : Word)
    (h_idx : indexW = BitVec.ofNat 64 i) :
    cpsTripleWithin 1 (B + 108) (B + 136) spanCr
      (inv newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items i v7 v10 v11 v12 v13 v14)
      (inv newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items i v7 v10 v11 v12 v13 v14) := by
  have hbr27 := cpsBranchWithin_extend_code
    (mem_at 27 (.BEQ .x22 .x18 (28 : BitVec 13)) (B + 108)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (beq_spec_gen_within .x22 .x18 (28 : BitVec 13)
      (BitVec.ofNat 64 i) indexW (B + 108))
  rw [show (B + 108 : Word) + signExtend13 (28 : BitVec 13) = B + 136 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega,
      show (B + 108 : Word) + 4 = B + 112 from by decide] at hbr27
  have heq : BitVec.ofNat 64 i = indexW := by rw [h_idx]
  have ht27 := cpsBranchWithin_takenStripPure2 hbr27 (fun _hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact ((sepConj_pure_right _).1 hQ).2 heq)
  have f27 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) ht27
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [inv, amb, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun h hq => by
      simp only [inv, amb, savedFrame] at hq ⊢
      xperm_chunked hq)
    f27

/-- Exit precall: BGEU ntaken + MV at exitGate → size call site B+144. -/
theorem exit_precall
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v7 v10 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (hi : i < items.length) :
    cpsTripleWithin 2 (B + 136) (B + 144) spanCr
      (inv newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items i v7 v10 v11 v12 v13 v14)
      (amb newSp listBase endPtr indexW outStart outSize st sz raVal saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 i) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))) := by
  set bs := encode (.list items)
  have hbs_len : bs.length = (encode (.list items)).length := rfl
  have hcur_lt := shortCursor_lt items i hi hshort
  have hcur_le : shortCursor items i ≤ bs.length := by
    rw [hbs_len]; exact Nat.le_of_lt hcur_lt
  have hult_cur : BitVec.ult
      (listBase + BitVec.ofNat 64 (shortCursor items i)) endPtr := by
    have hsum_c := listBase_add_toNat listBase (shortCursor items i) bs.length
      hcur_le (by rwa [hbs_len] at h_over ⊢)
    have hsum_e := listBase_add_toNat listBase bs.length bs.length
      (Nat.le_refl _) (by rwa [hbs_len] at h_over ⊢)
    rw [h_end, BitVec.ult, decide_eq_true_eq, hsum_c, hsum_e, hbs_len]
    have : shortCursor items i < (encode (.list items)).length := hcur_lt
    omega
  -- idx34 BGEU ntaken
  have hbr34 := cpsBranchWithin_extend_code
    (mem_at 34 (.BGEU .x21 .x9 (32 : BitVec 13)) (B + 136)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (bgeu_spec_gen_within .x21 .x9 (32 : BitVec 13)
      (listBase + BitVec.ofNat 64 (shortCursor items i)) endPtr (B + 136))
  rw [show (B + 136 : Word) + signExtend13 (32 : BitVec 13) = B + 168 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega,
      show (B + 136 : Word) + 4 = B + 140 from by decide] at hbr34
  have hnt34 := cpsBranchWithin_ntakenStripPure2 hbr34 (fun _hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult_cur)
  -- idx35 MV
  have hmv35 := cpsTripleWithin_extend_code
    (mem_at 35 (.MV .x10 .x21) (B + 140)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (mv_spec_gen_within .x10 .x21
      (listBase + BitVec.ofNat 64 (shortCursor items i)) v10 (B + 140) (by decide))
  rw [show (B + 140 : Word) + 4 = B + 144 from by decide] at hmv35
  have f34 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ BitVec.ofNat 64 i) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hnt34
  have f35 := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x22 ↦ᵣ BitVec.ofNat 64 i) **
     savedFrame newSp saved **
     regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hmv35
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame] at hp ⊢; xperm_chunked hp) f34 f35
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [inv, amb, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun h hq => by
      simp only [amb, savedFrame] at hq ⊢
      xperm_chunked hq)
    c01

/-- Size call at exit B+144: cursor in x10 → length in x10; ra becomes B+148. -/
theorem exit_size_call
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v7 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_walk_i : SpanForm ((encode (items[i]'hi)).getD 0 0)) :
    cpsTripleWithin 13 (B + 144) (B + 148) spanCr
      (amb newSp listBase endPtr indexW outStart outSize st sz raVal saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 i) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)))
      (amb newSp listBase endPtr indexW outStart outSize st sz (B + 148) saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 i) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))) := by
  set bs := encode (.list items)
  set cursor : Word := listBase + BitVec.ofNat 64 (shortCursor items i)
  set itemLenW : Word := BitVec.ofNat 64 (encode (items[i]'hi)).length
  have hbs_len : bs.length = (encode (.list items)).length := rfl
  have hcur_lt := shortCursor_lt items i hi hshort
  have h_off : shortCursor items i < bs.length := by rwa [hbs_len]
  have h_over_off : listBase.toNat + shortCursor items i < 2 ^ 64 := by
    have := hcur_lt; omega
  have hdec := decode_at_shortCursor items i hi hshort
  have hform := span_form_at_shortCursor items i hi hshort h_walk_i
  have hret_even : ((B + 148 : Word) &&& ~~~(1 : Word)) = B + 148 := by decide
  have hsize0 := rlp_item_size_offset_spec_within listBase (shortCursor items i)
    (B + 148) bs (items[i]'hi)
    (encode.encodeItems (items.drop (i + 1)))
    h_align h_off h_over_off (by intro j hj; rw [hbs_len] at hj; exact h_valid j hj)
    (by simpa [bs] using hdec) (by simpa [bs] using hform)
  rw [hret_even] at hsize0
  have hsizeC := cpsTripleWithin_extend_code size_sub hsize0
  have hpc : (B + 144 + 4 : Word) = B + 148 := by decide
  have hsizeW : cpsTripleWithin 12 rlpItemSizeBase (B + 144 + 4) spanCr
      (((.x1 : Reg) ↦ᵣ (B + 144 + 4)) **
        (((.x10 : Reg) ↦ᵣ cursor) **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
         regOwn .x5 ** regOwn .x6))
      (((.x1 : Reg) ↦ᵣ (B + 144 + 4)) **
        (((.x10 : Reg) ↦ᵣ itemLenW) **
         regOwn .x5 ** regOwn .x6 **
         ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)) := by
    rw [hpc]
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [cursor] at hp ⊢
        xperm_chunked hp)
      (fun _ hq => by
        simp only [itemLenW] at hq ⊢
        xperm_chunked hq)
      hsizeC
  have htarget : (B + 144 : Word)
        + signExtend21
            (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 144))
        = rlpItemSizeBase := by
    unfold B rlpItemSpanBase rlpItemSizeBase; decide
  have hcall := callWithin_spec (B + 144) rlpItemSizeBase raVal
    (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 144)) 12
    htarget
    (mem_at 36
      (.JAL .x1 (jalOff GuestAddrs.rlp_item_size (GuestAddrs.rlp_item_span + 144)))
      (B + 144) (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (by pcf) hsizeW
  rw [hpc] at hcall
  have fcall := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
     (.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ BitVec.ofNat 64 i) **
     savedFrame newSp saved **
     (.x7 ↦ᵣ v7) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by pcf) hcall
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [amb, cursor, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun h hq => by
      simp only [amb, cursor, itemLenW, savedFrame] at hq ⊢
      xperm_chunked hq)
    fcall

/-- Finish exit: SUB start, SD start, SD size, LI 0, JAL epi → bodyPost. -/
theorem exit_finish
    (newSp listBase endPtr indexW outStart outSize st sz : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v7 v11 v12 v13 v14 : Word)
    (_hshort : payloadLen items ≤ 55)
    (hi : i < items.length) :
    cpsTripleWithin 5 (B + 148) (B + 172) spanCr
      (amb newSp listBase endPtr indexW outStart outSize st sz (B + 148) saved
          (encode (.list items)) **
        ((.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
         (.x22 ↦ᵣ BitVec.ofNat 64 i) **
         regOwn .x5 ** regOwn .x6 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)))
      (bodyPost newSp listBase endPtr indexW outStart outSize (B + 148)
        saved items i hi) := by
  set bs := encode (.list items)
  set cursor : Word := listBase + BitVec.ofNat 64 (shortCursor items i)
  set itemLenW : Word := BitVec.ofNat 64 (encode (items[i]'hi)).length
  set startOff : Nat := shortCursor items i
  set startOffW : Word := BitVec.ofNat 64 startOff
  have hsub_eq : cursor - listBase = startOffW := by
    simp only [cursor, startOffW, startOff]
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  -- Peel regOwn x6 to concrete v6 for SUB destination.
  refine cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [amb, savedFrame] at hp ⊢
      xperm_chunked hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := amb newSp listBase endPtr indexW outStart outSize st sz (B + 148) saved bs **
        ((.x21 ↦ᵣ cursor) ** (.x22 ↦ᵣ BitVec.ofNat 64 i) **
         regOwn .x5 ** (.x7 ↦ᵣ v7) **
         (.x10 ↦ᵣ itemLenW) **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
         (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14)))
      (fun v6 => ?_))
  -- idx37 SUB x6, x21, x8
  have hsub37 := cpsTripleWithin_extend_code
    (mem_at 37 (.SUB .x6 .x21 .x8) (B + 148)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (sub_spec_gen_within .x6 .x21 .x8 cursor listBase v6 (B + 148) (by decide))
  rw [show (B + 148 : Word) + 4 = B + 152 from by decide] at hsub37
  rw [hsub_eq] at hsub37
  -- idx38 SD x19, x6, 0 — store startOff
  have hsd38 := cpsTripleWithin_extend_code
    (mem_at 38 (.SD .x19 .x6 (0 : BitVec 12)) (B + 152)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (sd_spec_gen_within .x19 .x6 outStart startOffW st (0 : BitVec 12) (B + 152))
  rw [show (B + 152 : Word) + 4 = B + 156 from by decide,
      show outStart + signExtend12 (0 : BitVec 12) = outStart from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at hsd38
  -- idx39 SD x20, x10, 0 — store itemLen
  have hsd39 := cpsTripleWithin_extend_code
    (mem_at 39 (.SD .x20 .x10 (0 : BitVec 12)) (B + 156)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (sd_spec_gen_within .x20 .x10 outSize itemLenW sz (0 : BitVec 12) (B + 156))
  rw [show (B + 156 : Word) + 4 = B + 160 from by decide,
      show outSize + signExtend12 (0 : BitVec 12) = outSize from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at hsd39
  -- idx40 LI x10, 0
  have hli40 := cpsTripleWithin_extend_code
    (mem_at 40 (.LI .x10 (0 : Word)) (B + 160)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (li_spec_gen_within .x10 itemLenW (0 : Word) (B + 160) (by decide))
  rw [show (B + 160 : Word) + 4 = B + 164 from by decide] at hli40
  -- idx41 JAL x0, +8 → bodyExit B+172
  have hjal41 := cpsTripleWithin_extend_code
    (mem_at 41 (.JAL .x0 (8 : BitVec 21)) (B + 164)
      (by bv_omega) (by rw [spanProg_len]; norm_num) (by rfl))
    (jal_x0_spec_gen_within (8 : BitVec 21) (B + 164))
  rw [show (B + 164 : Word) + signExtend21 (8 : BitVec 21) = B + 172 from by
        rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at hjal41
  -- Stable frame pieces
  set Fbase : Assertion :=
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ (B + 148)) ** (.x9 ↦ᵣ endPtr) **
     (.x18 ↦ᵣ indexW) **
     savedFrame newSp saved **
     regOwn .x5 ** (.x7 ↦ᵣ v7) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
     (.x22 ↦ᵣ BitVec.ofNat 64 i))
  have f37 := cpsTripleWithin_frameR
    (Fbase ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
      (.x10 ↦ᵣ itemLenW) ** (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) (by
      simp only [Fbase, savedFrame]; pcf) hsub37
  have f38 := cpsTripleWithin_frameR
    (Fbase ** (.x20 ↦ᵣ outSize) ** (.x8 ↦ᵣ listBase) **
      (.x21 ↦ᵣ cursor) ** (.x10 ↦ᵣ itemLenW) ** (outSize ↦ₘ sz)) (by
      simp only [Fbase, savedFrame]; pcf) hsd38
  have f39 := cpsTripleWithin_frameR
    (Fbase ** (.x19 ↦ᵣ outStart) ** (.x8 ↦ᵣ listBase) **
      (.x21 ↦ᵣ cursor) ** (.x6 ↦ᵣ startOffW) ** (outStart ↦ₘ startOffW)) (by
      simp only [Fbase, savedFrame]; pcf) hsd39
  have f40 := cpsTripleWithin_frameR
    (Fbase ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) ** (.x8 ↦ᵣ listBase) **
      (.x21 ↦ᵣ cursor) ** (.x6 ↦ᵣ startOffW) **
      (outStart ↦ₘ startOffW) ** (outSize ↦ₘ itemLenW)) (by
      simp only [Fbase, savedFrame]; pcf) hli40
  have f41raw := cpsTripleWithin_frameR
    (Fbase ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) ** (.x8 ↦ᵣ listBase) **
      (.x21 ↦ᵣ cursor) ** (.x6 ↦ᵣ startOffW) ** (.x10 ↦ᵣ (0 : Word)) **
      (outStart ↦ₘ startOffW) ** (outSize ↦ₘ itemLenW)) (by
      simp only [Fbase, savedFrame]; pcf) hjal41
  have f41 : cpsTripleWithin 1 (B + 164) (B + 172) spanCr
      (Fbase ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) ** (.x8 ↦ᵣ listBase) **
        (.x21 ↦ᵣ cursor) ** (.x6 ↦ᵣ startOffW) ** (.x10 ↦ᵣ (0 : Word)) **
        (outStart ↦ₘ startOffW) ** (outSize ↦ₘ itemLenW))
      (Fbase ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) ** (.x8 ↦ᵣ listBase) **
        (.x21 ↦ᵣ cursor) ** (.x6 ↦ᵣ startOffW) ** (.x10 ↦ᵣ (0 : Word)) **
        (outStart ↦ₘ startOffW) ** (outSize ↦ₘ itemLenW)) :=
    cpsTripleWithin_weaken
      (fun _ hp => (sepConj_emp_left _).2 hp)
      (fun _ hq => (sepConj_emp_left _).1 hq)
      f41raw
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [Fbase, savedFrame] at hp ⊢; xperm_chunked hp) f37 f38
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [Fbase, savedFrame] at hp ⊢; xperm_chunked hp) c01 f39
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [Fbase, savedFrame] at hp ⊢; xperm_chunked hp) c02 f40
  have c04 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [Fbase, savedFrame] at hp ⊢; xperm_chunked hp) c03 f41
  -- Pre: open to (amb ** … ** x6 ↦ v6); post → bodyPost with regOwns.
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [amb, cursor, itemLenW, Fbase, savedFrame, bs] at hp ⊢
      xperm_chunked hp)
    (fun h hq => by
      -- Rearrange concrete post into amb ** (x10 ** x21 ** x22 ** own5 ** x6↦ ** …)
      have hq1 :
          (amb newSp listBase endPtr indexW outStart outSize
              startOffW itemLenW (B + 148) saved bs **
            ((.x10 ↦ᵣ (0 : Word)) **
             (.x21 ↦ᵣ cursor) **
             (.x22 ↦ᵣ BitVec.ofNat 64 i) **
             regOwn .x5 **
             (.x6 ↦ᵣ startOffW) ** (.x7 ↦ᵣ v7) **
             (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
             (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))) h := by
        simp only [amb, Fbase, savedFrame, cursor, startOffW, itemLenW, bs] at hq ⊢
        xperm_chunked hq
      -- Lift regIs → regOwn on scratch temps (bodyPost shape).
      have hq2 :
          (amb newSp listBase endPtr indexW outStart outSize
              startOffW itemLenW (B + 148) saved bs **
            ((.x10 ↦ᵣ (0 : Word)) **
             (.x21 ↦ᵣ cursor) **
             (.x22 ↦ᵣ BitVec.ofNat 64 i) **
             regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
             regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) h := by
        refine sepConj_mono (fun _ x => x)
          (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x)
              (sepConj_mono (fun _ x => x)
                (sepConj_mono (fun _ x => x)
                  (sepConj_mono (regIs_implies_regOwn .x6)
                    (sepConj_mono (regIs_implies_regOwn .x7)
                      (sepConj_mono (regIs_implies_regOwn .x11)
                        (sepConj_mono (regIs_implies_regOwn .x12)
                          (sepConj_mono (regIs_implies_regOwn .x13)
                            (regIs_implies_regOwn .x14))))))))))
          _ hq1
      simp only [bodyPost, startOff, startOffW, itemLenW, cursor, bs] at hq2 ⊢
      exact hq2)
    c04

/-- Compose exit path: inv at exitGate → bodyPost at bodyExit. -/
theorem exit_stores
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v7 v10 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_walk : WalkedSpanForm items i) :
    cpsTripleWithin 20 (B + 136) (B + 172) spanCr
      (inv newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items i v7 v10 v11 v12 v13 v14)
      (bodyPost newSp listBase endPtr indexW outStart outSize (B + 148)
        saved items i hi) := by
  have h_walk_i : SpanForm ((encode (items[i]'hi)).getD 0 0) :=
    h_walk i (Nat.le_refl _) hi
  have h1 := exit_precall newSp listBase endPtr indexW outStart outSize
    st sz raVal saved items i v7 v10 v11 v12 v13 v14
    hshort h_end h_over hi
  have h2 := exit_size_call newSp listBase endPtr indexW outStart outSize
    st sz raVal saved items i v7 v11 v12 v13 v14
    hshort h_align h_over h_valid hi h_walk_i
  have h3 := exit_finish newSp listBase endPtr indexW outStart outSize
    st sz saved items i v7 v11 v12 v13 v14
    hshort hi
  have c12 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame, amb] at hp ⊢; xperm_chunked hp) h1 h2
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [savedFrame, amb] at hp ⊢; xperm_chunked hp) c12 h3

/-! ## Compose: loop induction, body, abiFrame wrap -/

/-- After `n` continues, ra is the size-call return (`B+124`); else entry ra. -/
private def loopExitRa (n : Nat) (raVal : Word) : Word :=
  if n = 0 then raVal else B + 124

/-- Walk from counter `k` to `i`, landing at the exit gate. -/
theorem loop_to_exit
    (newSp listBase endPtr indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (k i : Nat)
    (v7 v10 v11 v12 v13 v14 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (hk_le : k ≤ i)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i) :
    ∃ v10f,
      cpsTripleWithin (1 + 19 * (i - k)) (B + 108) (B + 136) spanCr
        (inv newSp listBase endPtr indexW outStart outSize st sz raVal
          saved items k v7 v10 v11 v12 v13 v14)
        (inv newSp listBase endPtr indexW outStart outSize st sz
          (loopExitRa (i - k) raVal)
          saved items i v7 v10f v11 v12 v13 v14) := by
  -- Induct on n = i - k via a strengthened motive.
  suffices h : ∀ n k raVal v10,
      n = i - k → k ≤ i →
      ∃ v10f,
        cpsTripleWithin (1 + 19 * (i - k)) (B + 108) (B + 136) spanCr
          (inv newSp listBase endPtr indexW outStart outSize st sz raVal
            saved items k v7 v10 v11 v12 v13 v14)
          (inv newSp listBase endPtr indexW outStart outSize st sz
            (loopExitRa (i - k) raVal)
            saved items i v7 v10f v11 v12 v13 v14) by
    exact h (i - k) k raVal v10 rfl hk_le
  intro n
  induction n with
  | zero =>
    intro k raVal v10 hn hk_le
    have hk_eq : k = i := by omega
    refine ⟨v10, ?_⟩
    have hex :=
      loop_exit newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items i v7 v10 v11 v12 v13 v14 h_idx
    -- after k=i: fuel 1+19*0, ra = loopExitRa 0 raVal = raVal
    rw [hk_eq]
    simpa [loopExitRa, Nat.sub_self] using hex
  | succ n ih =>
    intro k raVal v10 hn hk_le
    have hk_lt : k < i := by omega
    have hstep :=
      loop_continue newSp listBase endPtr indexW outStart outSize st sz raVal
        saved items k i v7 v10 v11 v12 v13 v14
        hshort h_end h_align h_over h_valid hi hk_lt h_idx h_walk
    have hk_items : k < items.length := Nat.lt_trans hk_lt hi
    set v10m : Word :=
      BitVec.ofNat 64 (encode (items[k]'hk_items)).length
    have ⟨v10f, hrest⟩ :=
      ih (k + 1) (B + 124) v10m (by omega) (by omega)
    have hfuel :
        1 + 19 * (i - k) = 19 + (1 + 19 * (i - (k + 1))) := by omega
    have hra :
        loopExitRa (i - (k + 1)) (B + 124) = loopExitRa (i - k) raVal := by
      have hpos : i - k ≠ 0 := by omega
      simp only [loopExitRa, hpos, ↓reduceIte]
      split <;> rfl
    have hrest' :
        cpsTripleWithin (1 + 19 * (i - (k + 1))) (B + 108) (B + 136) spanCr
          (inv newSp listBase endPtr indexW outStart outSize st sz (B + 124)
            saved items (k + 1) v7 v10m v11 v12 v13 v14)
          (inv newSp listBase endPtr indexW outStart outSize st sz
            (loopExitRa (i - k) raVal)
            saved items i v7 v10f v11 v12 v13 v14) := by
      rwa [hra] at hrest
    have c := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by simp only [savedFrame, amb, inv] at hp ⊢; xperm_chunked hp)
      hstep hrest'
    refine ⟨v10f, ?_⟩
    rwa [hfuel]

/-- Full body: setup + short header + loop + exit stores.
    `saved.ra` must equal `raVal` (caller return still in x1 at body entry). -/
theorem body_spec
    (newSp listBase listLenW indexW outStart outSize st sz raVal : Word)
    (saved : Saved) (items : List RLPItem) (i : Nat)
    (v5 v6 v7 : Word)
    (hshort : payloadLen items ≤ 55)
    (h_len : listLenW =
      BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i)
    (hra : saved.ra = raVal) :
    cpsTripleWithin (34 + 19 * i) (B + 36) (B + 172) spanCr
      ((.x2 ↦ᵣ newSp) **
       (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
       (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
       (.x21 ↦ᵣ saved.s5) ** (.x22 ↦ᵣ saved.s6) **
       savedFrame newSp saved **
       (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
       (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
       (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
      (bodyPost newSp listBase (listBase + listLenW) indexW outStart outSize
        (B + 148) saved items i hi) := by
  set bs := encode (.list items)
  set endPtr : Word := listBase + listLenW
  have h_end : endPtr =
      listBase + BitVec.ofNat 64 (encode (.list items)).length := by
    simp only [endPtr]; rw [h_len]
  have hlen_eq := short_list_length items hshort
  have hlen_pos : 0 < bs.length := by
    simp only [bs]; omega
  -- setup constructs Saved.mk raVal s0..; rewrite to `saved`
  -- setup builds Saved.mk raVal s0..; transport via hra
  have hsetup0 := setup_spec newSp listBase listLenW indexW outStart outSize
    st sz raVal saved.s0 saved.s1 saved.s2 saved.s3 saved.s4 saved.s5 saved.s6
    v5 v6 v7 bs
  have hsetup' :
      cpsTripleWithin 5 (B + 36) (B + 56) spanCr
        ((.x2 ↦ᵣ newSp) **
         (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ saved.s0) ** (.x9 ↦ᵣ saved.s1) **
         (.x18 ↦ᵣ saved.s2) ** (.x19 ↦ᵣ saved.s3) ** (.x20 ↦ᵣ saved.s4) **
         (.x21 ↦ᵣ saved.s5) ** (.x22 ↦ᵣ saved.s6) **
         savedFrame newSp saved **
         (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz))
        ((.x2 ↦ᵣ newSp) **
         (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
         (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
         (.x21 ↦ᵣ saved.s5) ** (.x22 ↦ᵣ saved.s6) **
         savedFrame newSp saved **
         (.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bs **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)) := by
    -- savedFrame of mk-raVal equals savedFrame of saved under hra
    have hsf :
        savedFrame newSp
            { ra := raVal, s0 := saved.s0, s1 := saved.s1, s2 := saved.s2,
              s3 := saved.s3, s4 := saved.s4, s5 := saved.s5, s6 := saved.s6 }
          = savedFrame newSp saved := by
      simp only [savedFrame, hra]
    simpa [hsf, endPtr] using hsetup0
  -- header
  have hheader := header_to_loop newSp listBase endPtr indexW outStart outSize
    st sz raVal saved items v5 v6 v7 listBase listLenW indexW outStart outSize
    saved.s5 saved.s6 hshort h_end h_align h_over h_valid hlen_pos
  -- loop 0 → i (entry x10 = listBase)
  have ⟨v10f, hloop⟩ :=
    loop_to_exit newSp listBase endPtr indexW outStart outSize st sz raVal
      saved items 0 i v7 listBase listLenW indexW outStart outSize
      hshort h_end h_align h_over h_valid hi (Nat.zero_le _) h_idx h_walk
  -- exit
  have hexit :=
    exit_stores newSp listBase endPtr indexW outStart outSize st sz
      (loopExitRa i raVal) saved items i
      v7 v10f listLenW indexW outStart outSize
      hshort h_end h_align h_over h_valid hi h_walk
  -- compose 5+8+(1+19*i)+20 = 34+19*i
  -- mid0: setup post ↔ header pre (both flat ABI regs)
  have c01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_chunked hp) hsetup' hheader
  -- mid1: header post = inv k=0 raVal ↔ loop pre (same)
  -- `savedFrame`/`bs` keep the atom shape xperm_chunked expects even when
  -- some simp args fire as no-ops on one side (silence unused-arg linter).
  have c02 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      set_option linter.unusedSimpArgs false in
        simp only [inv, amb, savedFrame, bs] at hp ⊢
      xperm_chunked hp)
    c01 hloop
  -- mid2: loop post = inv i (loopExitRa i raVal) ↔ exit pre
  have c03 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      set_option linter.unusedSimpArgs false in
        simp only [inv, amb, savedFrame, bodyPost, bs, Nat.sub_zero] at hp ⊢
      xperm_chunked hp)
    c02 hexit
  -- fuel association from nested seq
  have hfuel :
      5 + 8 + (1 + 19 * (i - 0)) + 20 = 34 + 19 * i := by omega
  convert c03 using 1
  · exact hfuel.symm

/-- Entry frame-reg map. -/
def spanVals (ret s0 s1 s2 s3 s4 s5 s6 : Word) : Reg → Word
  | .x1 => ret | .x8 => s0 | .x9 => s1 | .x18 => s2
  | .x19 => s3 | .x20 => s4 | .x21 => s5 | .x22 => s6 | _ => 0

/-- Body-exit frame-reg map. -/
def spanVals' (listBase endPtr indexW outStart outSize : Word)
    (items : List RLPItem) (i : Nat) : Reg → Word
  | .x1 => B + 148
  | .x8 => listBase
  | .x9 => endPtr
  | .x18 => indexW
  | .x19 => outStart
  | .x20 => outSize
  | .x21 => listBase + BitVec.ofNat 64 (shortCursor items i)
  | .x22 => BitVec.ofNat 64 i
  | _ => 0

theorem spanVals_saved (ret s0 s1 s2 s3 s4 s5 s6 : Word) :
    spanVals ret s0 s1 s2 s3 s4 s5 s6 =
      savedVals { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3,
                  s4 := s4, s5 := s5, s6 := s6 } := by
  funext r; cases r <;> rfl

/-- Whole-routine success triple under short-list + WalkedSpanForm domain. -/
theorem rlp_item_span_spec_within
    (sp0 ret listBase listLenW indexW outStart outSize st sz : Word)
    (s0 s1 s2 s3 s4 s5 s6 v5 v6 v7 : Word)
    (items : List RLPItem) (i : Nat)
    (hshort : payloadLen items ≤ 55)
    (h_len : listLenW =
      BitVec.ofNat 64 (encode (.list items)).length)
    (h_align : listBase.toNat % 8 = 0)
    (h_over : listBase.toNat + (encode (.list items)).length < 2 ^ 64)
    (h_valid : ∀ j, j < (encode (.list items)).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true)
    (hi : i < items.length)
    (h_idx : indexW = BitVec.ofNat 64 i)
    (h_walk : WalkedSpanForm items i)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (1 + spanFrame.length + (34 + 19 * i) + spanFrame.length + 1 + 1)
      rlpItemSpanBase ret spanCr
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsOwn spanFrame (sp0 + signExtend12 (-64 : BitVec 12)) **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)))
      ((.x2 ↦ᵣ sp0) **
        regsAt spanFrame (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        frameSlotsSaved spanFrame (sp0 + signExtend12 (-64 : BitVec 12))
          (spanVals ret s0 s1 s2 s3 s4 s5 s6) **
        ((.x10 ↦ᵣ (0 : Word)) **
         (outStart ↦ₘ BitVec.ofNat 64 (shortCursor items i)) **
         (outSize ↦ₘ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) := by
  set saved : Saved :=
    { ra := ret, s0 := s0, s1 := s1, s2 := s2, s3 := s3, s4 := s4,
      s5 := s5, s6 := s6 }
  set newSp := sp0 + signExtend12 (-64 : BitVec 12)
  set endPtr := listBase + listLenW
  set vals := spanVals ret s0 s1 s2 s3 s4 s5 s6
  set vals' := spanVals' listBase endPtr indexW outStart outSize items i
  have hentry :
      rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + spanFrame.length))
        = B + 36 := by
    simp only [spanFrame_length, B]; decide
  have hexit :
      rlpItemSpanBase +
          BitVec.ofNat 64 (4 * (1 + spanFrame.length + spanBody.length))
        = B + 172 := by
    simp only [spanFrame_length, spanBody_length, B]; decide
  have hb0 := body_spec newSp listBase listLenW indexW outStart outSize
    st sz ret saved items i v5 v6 v7
    hshort h_len h_align h_over h_valid hi h_idx h_walk (by rfl)
  have hbody : cpsTripleWithin (34 + 19 * i)
      (rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + spanFrame.length)))
      (rlpItemSpanBase + BitVec.ofNat 64 (4 * (1 + spanFrame.length + spanBody.length)))
      spanCr
      ((.x2 ↦ᵣ newSp) ** regsAt spanFrame vals **
        frameSlotsSaved spanFrame newSp vals **
        ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ listLenW) ** (.x12 ↦ᵣ indexW) **
         (.x13 ↦ᵣ outStart) ** (.x14 ↦ᵣ outSize) **
         (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         (outStart ↦ₘ st) ** (outSize ↦ₘ sz)))
      ((.x2 ↦ᵣ newSp) ** regsAt spanFrame vals' **
        frameSlotsSaved spanFrame newSp vals **
        ((.x10 ↦ᵣ (0 : Word)) **
         (outStart ↦ₘ BitVec.ofNat 64 (shortCursor items i)) **
         (outSize ↦ₘ BitVec.ofNat 64 (encode (items[i]'hi)).length) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encode (.list items)) **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14)) := by
    rw [hentry, hexit]
    have hvals : vals = savedVals saved := by
      simp only [vals, saved, spanVals_saved]
    have hslots :
        frameSlotsSaved spanFrame newSp vals = savedFrame newSp saved := by
      rw [hvals]; exact frameSlotsSaved_spanFrame newSp saved
    have hregs :
        regsAt spanFrame vals =
          ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
           (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
           (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6)) := by
      rw [hvals, regsAt_spanFrame]
    have hregs' :
        regsAt spanFrame vals' =
          ((.x1 ↦ᵣ (B + 148)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ endPtr) **
           (.x18 ↦ᵣ indexW) ** (.x19 ↦ᵣ outStart) ** (.x20 ↦ᵣ outSize) **
           (.x21 ↦ᵣ (listBase + BitVec.ofNat 64 (shortCursor items i))) **
           (.x22 ↦ᵣ BitVec.ofNat 64 i)) := by
      simp only [vals', spanVals', regsAt, spanFrame, endPtr, h_idx,
        List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    refine cpsTripleWithin_weaken ?pre ?post hb0
    · intro h hp
      -- hp = abiFrame shape (regsAt/slots); goal = body_spec flat pre
      rw [hregs, hslots] at hp
      simp only [saved] at hp ⊢
      xperm_chunked hp
    · intro h hq
      -- hq = bodyPost flat; goal = abiFrame shape (regsAt/slots)
      -- rewrite goal into flat, then xperm
      simp only [bodyPost, amb] at hq
      rw [hregs', hslots]
      simp only [saved, endPtr, h_idx] at hq ⊢
      xperm_chunked hq
  abi_frame (64 : BitVec 12) halign hbody

end RlpItemSpanSpec
