/-
  EvmAsm.Codegen.Programs.RlpItemSpanSizeOffset

  Offset / unaligned-cursor variants of the `rlp_item_size` SpanForm triples.
  The aligned forms in `RlpSpliceHelperSpec` frame `bytesRegion ptr bs` with
  `x10 ↦ ptr` and force `ptr % 8 = 0`.  The `rlp_item_span` loop calls size
  with `a0 = listBase + off` where `off` is the cumulative item cursor and is
  *not* 8-aligned after the first item.  These variants re-root the LBU on the
  one aligned `bytesRegion listBase bs` at index `off` (see
  `bytesRegion_lbu_within`: `regionBase` aligned, `rs1 = regionBase + i`).

  Consumed by `RlpItemSpanSpec` machine blocks (#11577).
-/

import EvmAsm.Codegen.Programs.RlpSpliceHelperSpec
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen
namespace RlpItemSpanSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.EL.RLP
open EvmAsm.Codegen.RlpSpliceHelperSpec

/-- Code-membership for a `∀ base` `ofProg` slice. -/
local macro "cmem" k:term:max : tactic =>
  `(tactic| exact CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr _ _ $k _ (by decide) (by decide) (by bv_omega)))

/-- Head byte at an offset into `bs`. -/
theorem head_at_off (bs : List (BitVec 8)) (off : Nat) (h : off < bs.length) :
    (bs.drop off).getD 0 0 = bs[off]'h := by
  have hdrop : 0 < (bs.drop off).length := by simp [List.length_drop]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdrop,
      List.getElem_drop]
  rfl

/-- **`rlp_item_size` single-byte form at unaligned cursor `listBase + off`.** -/
theorem rlp_item_size_single_offset_pinned (base listBase : Word) (off : Nat)
    (raVal v5 v6 : Word) (bs : List (BitVec 8))
    (h_align : listBase.toNat % 8 = 0)
    (h_off : off < bs.length)
    (h_over : listBase.toNat + off < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_b : (bs[off]'h_off).toNat < 0x80) :
    cpsTripleWithin 5 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  set CR := CodeReq.ofProg base rlpItemSize_prog with hCR
  set cursor := listBase + BitVec.ofNat 64 off
  set b := bs[off]'h_off
  -- idx0: LBU x5, 0(x10) at offset `off` inside the aligned region
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 listBase v5 base bs off (by decide)
      h_align h_off h_over (h_valid off h_off))
    (by rw [hCR]; cmem 0)
  -- idx1: LI x6, 0x80
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli
  -- idx2: BGEU x5, x6, +12 — NOT taken
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      (b.zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr
  have hult : BitVec.ult (b.zeroExtend 64) (0x80 : Word) :=
    ult_zx_of_lt _ _ (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; exact h_b)
  have hnt := cpsBranchWithin_ntakenStripPure2 hbr (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult)
  -- idx3: LI x10, 1
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x10 cursor (1 : Word) (base + 12) (by decide))
    (by rw [hCR]; cmem 3)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hli10
  -- idx4: ret
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 16) raVal)
    (by rw [hCR]; cmem 4)
  -- frames
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli
  have hntF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hnt
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0x80 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli10
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0x80 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hret
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 hntF
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli10F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc4
  have hq1 : (((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0x80 : Word)) **
       (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ (1 : Word)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
  xperm_hyp hq2

/-- **`rlp_item_size` short-string form at unaligned cursor.** -/
theorem rlp_item_size_short_string_offset_pinned (base listBase : Word) (off : Nat)
    (raVal v5 v6 : Word) (bs : List (BitVec 8))
    (h_align : listBase.toNat % 8 = 0)
    (h_off : off < bs.length)
    (h_over : listBase.toNat + off < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_lo : 0x80 ≤ (bs[off]'h_off).toNat)
    (h_hi : (bs[off]'h_off).toNat < 0xb8) :
    cpsTripleWithin 8 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs[off]'h_off).toNat - 127)) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  set CR := CodeReq.ofProg base rlpItemSize_prog with hCR
  set cursor := listBase + BitVec.ofNat 64 off
  set b := bs[off]'h_off
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 listBase v5 base bs off (by decide)
      h_align h_off h_over (h_valid off h_off))
    (by rw [hCR]; cmem 0)
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      (b.zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr
  have hnult : ¬ BitVec.ult (b.zeroExtend 64) (0x80 : Word) :=
    not_ult_zx_of_ge _ _ (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; exact h_lo)
  have ht2 := cpsBranchWithin_takenStripPure2 hbr (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact hnult ((sepConj_pure_right _).1 hQ).2)
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 20) (by decide))
    (by rw [hCR]; cmem 5)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hli5
  have hbr6 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 6)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      (b.zeroExtend 64) (0xb8 : Word) (base + 24))
  rw [show (base + 24 : Word) + signExtend13 (16 : BitVec 13) = base + 40 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr6
  have hult6 : BitVec.ult (b.zeroExtend 64) (0xb8 : Word) :=
    ult_zx_of_lt _ _ (by rw [show ((0xb8 : Word)).toNat = 184 from by decide]; exact h_hi)
  have hnt6 := cpsBranchWithin_ntakenStripPure2 hbr6 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2 hult6)
  have ha7 := liftCode (cr' := CR)
    (addi_spec_gen_within .x10 .x5 cursor (b.zeroExtend 64)
      (-128 : BitVec 12) (base + 28) (by decide))
    (by rw [hCR]; cmem 7)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at ha7
  have ha8 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x10
      ((b.zeroExtend 64) + signExtend12 (-128 : BitVec 12))
      (1 : BitVec 12) (base + 32) (by decide))
    (by rw [hCR]; cmem 8)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega,
      ris_result_128 b h_lo] at ha8
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 36) raVal)
    (by rw [hCR]; cmem 9)
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli
  have ht2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) ht2
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli5
  have hnt6F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hnt6
  have ha7F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ (0xb8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) ha7
  have ha8F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xb8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) ha8
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (b.toNat - 127)) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xb8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hret
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ht2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli5F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 hnt6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 ha7F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 ha8F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc7
  have hq1 : (((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0xb8 : Word)) **
       (((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (b.toNat - 127)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
  xperm_hyp hq2

/-- **`rlp_item_size` short-list form at unaligned cursor.** -/
theorem rlp_item_size_short_list_offset_pinned (base listBase : Word) (off : Nat)
    (raVal v5 v6 : Word) (bs : List (BitVec 8))
    (h_align : listBase.toNat % 8 = 0)
    (h_off : off < bs.length)
    (h_over : listBase.toNat + off < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_lo : 0xc0 ≤ (bs[off]'h_off).toNat)
    (h_hi : (bs[off]'h_off).toNat < 0xf8) :
    cpsTripleWithin 12 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
       ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 ((bs[off]'h_off).toNat - 191)) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  set CR := CodeReq.ofProg base rlpItemSize_prog with hCR
  set cursor := listBase + BitVec.ofNat 64 off
  set b := bs[off]'h_off
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x5 .x10 listBase v5 base bs off (by decide)
      h_align h_off h_over (h_valid off h_off))
    (by rw [hCR]; cmem 0)
  have hli := liftCode (cr' := CR)
    (li_spec_gen_within .x6 v6 (0x80 : Word) (base + 4) (by decide))
    (by rw [hCR]; cmem 1)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hli
  have hbr := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 2)
    (h := bgeu_spec_gen_within .x5 .x6 (12 : BitVec 13)
      (b.zeroExtend 64) (0x80 : Word) (base + 8))
  rw [show (base + 8 : Word) + signExtend13 (12 : BitVec 13) = base + 20 from by
        rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega,
      show (base + 8 : Word) + 4 = base + 12 from by bv_omega] at hbr
  have ht2 := cpsBranchWithin_takenStripPure2 hbr (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0x80 : Word)
        (by rw [show ((0x80 : Word)).toNat = 128 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  have hli5 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0x80 : Word) (0xb8 : Word) (base + 20) (by decide))
    (by rw [hCR]; cmem 5)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hli5
  have hbr6 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 6)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      (b.zeroExtend 64) (0xb8 : Word) (base + 24))
  rw [show (base + 24 : Word) + signExtend13 (16 : BitVec 13) = base + 40 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 24 : Word) + 4 = base + 28 from by bv_omega] at hbr6
  have ht6 := cpsBranchWithin_takenStripPure2 hbr6 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xb8 : Word)
        (by rw [show ((0xb8 : Word)).toNat = 184 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  have hli10 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xb8 : Word) (0xc0 : Word) (base + 40) (by decide))
    (by rw [hCR]; cmem 10)
  rw [show (base + 40 : Word) + 4 = base + 44 from by bv_omega] at hli10
  have hbr11 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 11)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      (b.zeroExtend 64) (0xc0 : Word) (base + 44))
  rw [show (base + 44 : Word) + signExtend13 (16 : BitVec 13) = base + 60 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbr11
  have ht11 := cpsBranchWithin_takenStripPure2 hbr11 (fun hp hQf => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQf
    exact (not_ult_zx_of_ge _ (0xc0 : Word)
        (by rw [show ((0xc0 : Word)).toNat = 192 from by decide]; omega))
      ((sepConj_pure_right _).1 hQ).2)
  have hli15 := liftCode (cr' := CR)
    (li_spec_gen_within .x6 (0xc0 : Word) (0xf8 : Word) (base + 60) (by decide))
    (by rw [hCR]; cmem 15)
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at hli15
  have hbr16 := cpsBranchWithin_extend_code (cr' := CR)
    (hmono := by rw [hCR]; cmem 16)
    (h := bgeu_spec_gen_within .x5 .x6 (16 : BitVec 13)
      (b.zeroExtend 64) (0xf8 : Word) (base + 64))
  rw [show (base + 64 : Word) + signExtend13 (16 : BitVec 13) = base + 80 from by
        rw [show signExtend13 (16 : BitVec 13) = (16 : Word) from by decide]; bv_omega,
      show (base + 64 : Word) + 4 = base + 68 from by bv_omega] at hbr16
  have hnt16 := cpsBranchWithin_ntakenStripPure2 hbr16 (fun hp hQt => by
    obtain ⟨_, _, _, _, _, hQ⟩ := hQt
    exact ((sepConj_pure_right _).1 hQ).2
      (ult_zx_of_lt _ _ (by rw [show ((0xf8 : Word)).toNat = 248 from by decide]; exact h_hi)))
  have ha17 := liftCode (cr' := CR)
    (addi_spec_gen_within .x10 .x5 cursor (b.zeroExtend 64)
      (-192 : BitVec 12) (base + 68) (by decide))
    (by rw [hCR]; cmem 17)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at ha17
  have ha18 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x10
      ((b.zeroExtend 64) + signExtend12 (-192 : BitVec 12))
      (1 : BitVec 12) (base + 72) (by decide))
    (by rw [hCR]; cmem 18)
  rw [show (base + 72 : Word) + 4 = base + 76 from by bv_omega,
      ris_result_192 b (by omega)] at ha18
  have hret := liftCode (cr' := CR)
    (EvmAsm.Evm64.ret_spec_within' (base + 76) raVal)
    (by rw [hCR]; cmem 19)
  have hlbuF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hlbu
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli
  have ht2F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) ht2
  have hli5F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli5
  have ht6F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) ht6
  have hli10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli10
  have ht11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) ht11
  have hli15F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hli15
  have hnt16F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x10 : Reg) ↦ᵣ cursor) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) hnt16
  have ha17F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x6 : Reg) ↦ᵣ (0xf8 : Word)) **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs)
    (by pcf) ha17
  have ha18F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ raVal) ** ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xf8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) ha18
  have hretF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (b.toNat - 191)) **
     ((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
     ((.x6 : Reg) ↦ᵣ (0xf8 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bs)
    (by pcf) hret
  have hc1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbuF hliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc1 ht2F
  have hc3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc2 hli5F
  have hc4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc3 ht6F
  have hc5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc4 hli10F
  have hc6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc5 ht11F
  have hc7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc6 hli15F
  have hc8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc7 hnt16F
  have hc9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc8 ha17F
  have hc10 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc9 ha18F
  have hc11 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hc10 hretF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_) hc11
  have hq1 : (((.x5 : Reg) ↦ᵣ (b.zeroExtend 64)) **
      (((.x6 : Reg) ↦ᵣ (0xf8 : Word)) **
       (((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (b.toNat - 191)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs))) h := by
    xperm_hyp hq
  have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
    (sepConj_mono (regIs_to_regOwn .x6 _) (fun _ hh => hh)) h hq1
  xperm_hyp hq2

/-- **Unified offset `rlp_item_size` under `SpanForm`, scratch released.** -/
theorem rlp_item_size_offset_form_own (base listBase : Word) (off : Nat)
    (raVal : Word) (bs : List (BitVec 8)) (item : RLPItem) (rest : List Byte)
    (h_align : listBase.toNat % 8 = 0)
    (h_off : off < bs.length)
    (h_over : listBase.toNat + off < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_decode : decode (bs.drop off) = some (item, rest))
    (h_form : SpanForm ((bs.drop off).getD 0 0)) :
    cpsTripleWithin 12 base (raVal &&& ~~~1)
      (CodeReq.ofProg base rlpItemSize_prog)
      ((((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
       regOwn .x5 ** regOwn .x6)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) := by
  have hb : (bs.drop off).getD 0 0 = bs[off]'h_off := head_at_off bs off h_off
  rw [hb] at h_form
  rw [← risSpan_eq_encode_length (bs.drop off) item rest h_decode (by rwa [hb])]
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P := (((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) ** regOwn .x5)
      (fun v6 => ?_))
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x5)
      (P := (((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
        ((.x6 : Reg) ↦ᵣ v6))
      (fun v5 => ?_))
  rcases h_form with hlt | ⟨hlo, hhi⟩
  · by_cases hsb : (bs[off]'h_off).toNat < 0x80
    · rw [show risSpan ((bs.drop off).getD 0 0) = (1 : Word) from by
          rw [hb]; unfold risSpan; rw [if_pos hsb]]
      exact cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (rlp_item_size_single_offset_pinned base listBase off raVal v5 v6 bs
            h_align h_off h_over h_valid hsb))
    · rw [show risSpan ((bs.drop off).getD 0 0) =
            BitVec.ofNat 64 ((bs[off]'h_off).toNat - 127) from by
          rw [hb]; unfold risSpan; rw [if_neg hsb, if_pos hlt]]
      exact cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
          (rlp_item_size_short_string_offset_pinned base listBase off raVal v5 v6 bs
            h_align h_off h_over h_valid (by omega) hlt))
  · rw [show risSpan ((bs.drop off).getD 0 0) =
          BitVec.ofNat 64 ((bs[off]'h_off).toNat - 191) from by
        rw [hb]; unfold risSpan; rw [if_neg (by omega), if_neg (by omega)]]
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
        (rlp_item_size_short_list_offset_pinned base listBase off raVal v5 v6 bs
          h_align h_off h_over h_valid hlo hhi))

/-- Offset form at the linked guest address of `rlp_item_size`. -/
theorem rlp_item_size_offset_spec_within (listBase : Word) (off : Nat)
    (raVal : Word) (bs : List (BitVec 8)) (item : RLPItem) (rest : List Byte)
    (h_align : listBase.toNat % 8 = 0)
    (h_off : off < bs.length)
    (h_over : listBase.toNat + off < 2 ^ 64)
    (h_valid : ∀ k, k < bs.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (h_decode : decode (bs.drop off) = some (item, rest))
    (h_form : SpanForm ((bs.drop off).getD 0 0)) :
    cpsTripleWithin 12 rlpItemSizeBase (raVal &&& ~~~1) rlpItemSizeCode
      ((((.x1 : Reg) ↦ᵣ raVal) **
        ((.x10 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 off)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) **
       regOwn .x5 ** regOwn .x6)
      (((.x1 : Reg) ↦ᵣ raVal) **
       ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64 (encode item).length) **
       regOwn .x5 ** regOwn .x6 **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bs) :=
  rlp_item_size_offset_form_own rlpItemSizeBase listBase off raVal bs item rest
    h_align h_off h_over h_valid h_decode h_form

end RlpItemSpanSpec
end EvmAsm.Codegen
