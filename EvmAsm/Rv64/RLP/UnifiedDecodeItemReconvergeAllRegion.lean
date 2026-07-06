/-
  EvmAsm.Rv64.RLP.UnifiedDecodeItemReconvergeAllRegion

  EL.3 — the 5-class reconverged single-item decoder re-derived over a multi-dword
  `bytesRegion regionBase bs` instead of the single-dword `(dwordAddr ↦ₘ wordVal)`
  model. Region analog of `rlp_decode_single_item_reconverged_all`
  (`UnifiedDecodeItemReconvergeAll.lean`).

  Flat arms (e1/e2/e4) reuse the existing register-only handlers (only the framed
  memory changes `↦ₘ → bytesRegion`); the long arms (e3/e5) use the region arms
  `rlp_phase1_e{3,5}_…_full_region_spec_within` (`Phase1LongFullRegion.lean`); the
  reconvergence wrapper `reconverge_arm_n` is parametric and reused unchanged.
  The item pointer `v13` sits at byte offset `off` (`hv13`). This is the
  `decoderH` the long-item list loop dispatches to.
-/

import EvmAsm.Rv64.RLP.UnifiedDecodeItemReconvergeAll
import EvmAsm.Rv64.RLP.Phase1LongFullRegion

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

-- ============================================================================
-- Region uniform-post helpers (reuse `itemResidue` / `itemX14`)
-- ============================================================================

/-- `x11` decoded payload length per class, reading length bytes from the region. -/
def itemLenRegion (pfx : Byte) (bs : List Byte) (off : Nat) : Word :=
  match classifyPrefix pfx with
  | .singleByte => 1
  | .shortBytes => BitVec.ofNat 64 (rlpPrefixShortBytesPayloadLen pfx)
  | .longBytes  => BitVec.ofNat 64
      (Nat.fromBytesBE ((bs.drop (off + 1)).take (rlpPrefixLongBytesLenOfLen pfx)))
  | .shortList  => BitVec.ofNat 64 (rlpPrefixShortListPayloadLen pfx)
  | .longList   => BitVec.ofNat 64
      (Nat.fromBytesBE ((bs.drop (off + 1)).take (rlpPrefixLongListLenOfLen pfx)))

/-- `x12` scratch per class (long forms hold the last length byte read from the
    region; flat forms leave the framed-in `v12Old`). -/
def itemX12Region (pfx : Byte) (bs : List Byte) (off : Nat) (v12Old : Word) : Word :=
  match classifyPrefix pfx with
  | .longBytes => (bs.getD ((off + 1) + (rlpPrefixLongBytesLenOfLen pfx - 1)) 0).zeroExtend 64
  | .longList  => (bs.getD ((off + 1) + (rlpPrefixLongListLenOfLen pfx - 1)) 0).zeroExtend 64
  | _ => v12Old

/-- `x13` payload pointer per class, as a region offset. -/
def itemPtrRegion (pfx : Byte) (regionBase : Word) (off : Nat) : Word :=
  match classifyPrefix pfx with
  | .singleByte => regionBase + BitVec.ofNat 64 off
  | .shortBytes => regionBase + BitVec.ofNat 64 (off + 1)
  | .longBytes  => regionBase + BitVec.ofNat 64 ((off + 1) + rlpPrefixLongBytesLenOfLen pfx)
  | .shortList  => regionBase + BitVec.ofNat 64 (off + 1)
  | .longList   => regionBase + BitVec.ofNat 64 ((off + 1) + rlpPrefixLongListLenOfLen pfx)

/-- The post pointer after the prefix byte: `(regionBase + off) + 1 = regionBase + (off+1)`. -/
private theorem region_succ_ptr (regionBase : Word) (off : Nat) :
    (regionBase + BitVec.ofNat 64 off) + signExtend12 (1 : BitVec 12)
      = regionBase + BitVec.ofNat 64 (off + 1) := by
  rw [se12_1, word_ofNat_add_one off]; bv_omega

/-- Region long-form-only proof obligations (per-byte region window + loop
    back-edge), gated on the class. Region analog of `rlpDecodeLongHyps`. -/
def rlpDecodeLongHypsRegion (pfx : EvmAsm.EL.RLP.Byte)
    (regionBase : Word) (off : Nat) (bs : List Byte) (base : Word) (back : BitVec 13)
    (e3_target : Word) : Prop :=
  match classifyPrefix pfx with
  | .longBytes =>
      (∀ i, i < rlpPrefixLongBytesLenOfLen pfx →
          (off + 1) + i < bs.length
          ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 ((off + 1) + i)) = true)
        ∧ ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12)
  | .longList =>
      (∀ i, i < rlpPrefixLongListLenOfLen pfx →
          (off + 1) + i < bs.length
          ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 ((off + 1) + i)) = true)
        ∧ ((base + 44) + 20) + signExtend13 back = (base + 44)
  | _ => True

-- ============================================================================
-- Complete 5-class reconverged single-item decode, over `bytesRegion`
-- ============================================================================

/-- **Region reconverged single-item decode.** For any prefix byte, the decoder
    runs from `base`, reading length bytes (for long classes) from
    `bytesRegion regionBase bs`, and a `JAL x0` at the class exit jumps to the
    common `joinPC`. Region analog of `rlp_decode_single_item_reconverged_all`. -/
theorem rlp_decode_single_item_reconverged_all_region
    (pfx : Byte)
    (v10 v11Old v12Old v13 v14Old : Word)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (off1 off2 off3 off4 back : BitVec 13)
    (joff1 joff2 joff3 joff4 joff5 : BitVec 21)
    (base e1_target e2_target e3_target e4_target joinPC : Word) (cr : CodeReq)
    (htarget1 : (base + 4) + signExtend13 off1 = e1_target)
    (htarget2 : (base + 8 + 4) + signExtend13 off2 = e2_target)
    (htarget3 : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (htarget4 : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hv13 : v13 = regionBase + BitVec.ofNat 64 off)
    (hlong : rlpDecodeLongHypsRegion pfx regionBase off bs base back e3_target)
    (hd_e1 : (rlp_phase1_step_code 0x80 off1 base).Disjoint
              (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
    (hd_e2 : ((rlp_phase1_step_code 0x80 off1 base).union
                (rlp_phase1_step_code 0xB8 off2 (base + 8))).Disjoint
              (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
    (hd_e3_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_e3_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
    (hd_e4 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
    (hd_e5_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_e5_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
    (hjoin1 : (e1_target + 4) + signExtend21 joff1 = joinPC)
    (hjoin2 : (e2_target + 8) + signExtend21 joff2 = joinPC)
    (hjoin3 : ((e3_target + 12) + 24) + signExtend21 joff3 = joinPC)
    (hjoin4 : (e4_target + 8) + signExtend21 joff4 = joinPC)
    (hjoin5 : ((base + 44) + 24) + signExtend21 joff5 = joinPC)
    (hd_jal1 : ((rlp_phase1_step_code 0x80 off1 base).union
                  (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog)).Disjoint
                (CodeReq.singleton (e1_target + 4) (.JAL .x0 joff1)))
    (hd_jal2 : (((rlp_phase1_step_code 0x80 off1 base).union
                  (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                  (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).Disjoint
                (CodeReq.singleton (e2_target + 8) (.JAL .x0 joff2)))
    (hd_jal3 : (((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
                  (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
                  (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))).Disjoint
                (CodeReq.singleton ((e3_target + 12) + 24) (.JAL .x0 joff3)))
    (hd_jal4 : (((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).Disjoint
                (CodeReq.singleton (e4_target + 8) (.JAL .x0 joff4)))
    (hd_jal5 : (((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
                  (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))).Disjoint
                (CodeReq.singleton ((base + 44) + 24) (.JAL .x0 joff5)))
    (hsub1 : ∀ a i, (((rlp_phase1_step_code 0x80 off1 base).union
                  (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog)).union
                  (CodeReq.singleton (e1_target + 4) (.JAL .x0 joff1))) a = some i → cr a = some i)
    (hsub2 : ∀ a i, ((((rlp_phase1_step_code 0x80 off1 base).union
                  (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
                  (CodeReq.ofProg e2_target rlp_phase3_short_string_prog)).union
                  (CodeReq.singleton (e2_target + 8) (.JAL .x0 joff2))) a = some i → cr a = some i)
    (hsub3 : ∀ a i, ((((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
                  (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
                  (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))).union
                  (CodeReq.singleton ((e3_target + 12) + 24) (.JAL .x0 joff3))) a = some i →
                cr a = some i)
    (hsub4 : ∀ a i, ((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)).union
                  (CodeReq.singleton (e4_target + 8) (.JAL .x0 joff4))) a = some i → cr a = some i)
    (hsub5 : ∀ a i, ((((((rlp_phase1_step_code 0x80 off1 base).union
                  ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
                    ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
                      (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
                  (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
                  (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))).union
                  (CodeReq.singleton ((base + 44) + 24) (.JAL .x0 joff5))) a = some i →
                cr a = some i) :
    cpsTripleWithin 60 base joinPC cr
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
       (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
       bytesRegion regionBase bs)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs off) **
       (.x12 ↦ᵣ itemX12Region pfx bs off v12Old) ** (.x13 ↦ᵣ itemPtrRegion pfx regionBase off) **
       (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs) := by
  cases h : classifyPrefix pfx with
  | singleByte =>
    have handler := rlp_phase1_e1_single_byte_of_class_spec_within pfx v10 v11Old off1 base
      e1_target htarget1 h hd_e1
    have handler' : cpsTripleWithin 3 base (e1_target + 4)
        ((rlp_phase1_step_code 0x80 off1 base).union
          (CodeReq.ofProg e1_target rlp_phase3_single_byte_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         bytesRegion regionBase bs)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs off) **
         (.x12 ↦ᵣ itemX12Region pfx bs off v12Old) ** (.x13 ↦ᵣ itemPtrRegion pfx regionBase off) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLenRegion, itemPtrRegion, itemX12Region, itemX14, h]
          rw [hv13] at hp
          xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
          (by pcFree) handler)
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin1 hd_jal1 hsub1
  | shortBytes =>
    have handler := rlp_phase1_e2_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 base e2_target htarget2 h hd_e2
    have handler' : cpsTripleWithin 6 base (e2_target + 8)
        (((rlp_phase1_step_code 0x80 off1 base).union
            (rlp_phase1_step_code 0xB8 off2 (base + 8))).union
          (CodeReq.ofProg e2_target rlp_phase3_short_string_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         bytesRegion regionBase bs)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs off) **
         (.x12 ↦ᵣ itemX12Region pfx bs off v12Old) ** (.x13 ↦ᵣ itemPtrRegion pfx regionBase off) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLenRegion, itemPtrRegion, itemX12Region, itemX14, h]
          rw [hv13, region_succ_ptr] at hp
          xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
          (by pcFree) handler)
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin2 hd_jal2 hsub2
  | longBytes =>
    simp only [rlpDecodeLongHypsRegion, h] at hlong
    obtain ⟨hwin, hback⟩ := hlong
    have handler := rlp_phase1_e3_longBytes_full_region_spec_within pfx v10 v11Old v12Old v13 v14Old
      regionBase off bs off1 off2 off3 back base e3_target htarget3 h halign hover hv13 hwin hback
      hd_e3_phase3 hd_e3_loop
    have handler' : cpsTripleWithin (9 + 6 * rlpPrefixLongBytesLenOfLen pfx) base
        ((e3_target + 12) + 24)
        (((((rlp_phase1_step_code 0x80 off1 base).union
            ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
              (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
            (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
            (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         bytesRegion regionBase bs)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs off) **
         (.x12 ↦ᵣ itemX12Region pfx bs off v12Old) ** (.x13 ↦ᵣ itemPtrRegion pfx regionBase off) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLenRegion, itemPtrRegion, itemX12Region, itemX14, h]
          xperm_hyp hp) handler
    have hn := rlpPrefixLongBytesLenOfLen_le_8_of_class h
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin3 hd_jal3 hsub3
  | shortList =>
    have handler := rlp_phase1_e4_full_path_payload_len_of_class_spec_within pfx v10 v11Old v13
      off1 off2 off3 off4 base e4_target htarget4 h hd_e4
    have handler' : cpsTripleWithin 10 base (e4_target + 8)
        (((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
              (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
          (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         bytesRegion regionBase bs)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs off) **
         (.x12 ↦ᵣ itemX12Region pfx bs off v12Old) ** (.x13 ↦ᵣ itemPtrRegion pfx regionBase off) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLenRegion, itemPtrRegion, itemX12Region, itemX14, h]
          rw [hv13, region_succ_ptr] at hp
          xperm_hyp hp)
        (cpsTripleWithin_frameR
          ((.x12 ↦ᵣ v12Old) ** (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
          (by pcFree) handler)
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin4 hd_jal4 hsub4
  | longList =>
    simp only [rlpDecodeLongHypsRegion, h] at hlong
    obtain ⟨hwin, hback⟩ := hlong
    have handler := rlp_phase1_e5_longList_full_region_spec_within pfx v10 v11Old v12Old v13 v14Old
      regionBase off bs off1 off2 off3 off4 back base h halign hover hv13 hwin hback
      hd_e5_phase3 hd_e5_loop
    have handler' : cpsTripleWithin (11 + 6 * rlpPrefixLongListLenOfLen pfx) base
        ((base + 44) + 24)
        (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
              (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
          (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
          (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
         (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old) **
         bytesRegion regionBase bs)
        ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ itemResidue pfx) ** (.x11 ↦ᵣ itemLenRegion pfx bs off) **
         (.x12 ↦ᵣ itemX12Region pfx bs off v12Old) ** (.x13 ↦ᵣ itemPtrRegion pfx regionBase off) **
         (.x14 ↦ᵣ itemX14 pfx v14Old) ** bytesRegion regionBase bs) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hp => by
          simp only [itemResidue, itemLenRegion, itemPtrRegion, itemX12Region, itemX14, h]
          xperm_hyp hp) handler
    have hn := rlpPrefixLongListLenOfLen_le_8_of_class h
    exact reconverge_arm_n (by omega) (by pcFree) handler' hjoin5 hd_jal5 hsub5

end EvmAsm.Rv64.RLP
