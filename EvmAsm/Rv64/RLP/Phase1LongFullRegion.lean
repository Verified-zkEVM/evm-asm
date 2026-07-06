/-
  EvmAsm.Rv64.RLP.Phase1LongFullRegion

  EL.3 — the LONG decoder arms (e3 longBytes, e5 longList) re-derived over a
  multi-dword `bytesRegion regionBase bs` instead of the single-dword
  `(dwordAddr ↦ₘ wordVal)` model. Region analogs of
  `rlp_phase1_e3_longBytes_full_spec_within` (`Phase1E3LongBytesFull.lean`) and
  `rlp_phase1_e5_longList_full_spec_within` (`Phase1E5LongListFull.lean`).

  Phase 1 (cascade) and Phase 3 (long-string/list entry) are register-only and
  reused verbatim; only the Phase 2 length-read loop touches memory, so it is
  swapped from `rlp_phase2_long_loop_n_byte_spec_within` (single dword) to
  `rlp_phase2_long_loop_region_n_spec_within` (region, #9020), and `bytesRegion`
  is framed through the register-only phases. The item pointer `v13` sits at byte
  offset `off` in the region (`hv13`); the `lenOfLen` length bytes start at `off+1`.
  These are the bytesRegion `decoderH`-arms the unified region decoder (next PR)
  dispatches to.
-/

import EvmAsm.Rv64.RLP.Phase1E3FullPath
import EvmAsm.Rv64.RLP.Phase1E5FullPath
import EvmAsm.Rv64.RLP.Phase2LongLoopRegion

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP
open EvmAsm.Rv64.AddrNorm (se12_1)

/-- Region full decode path for an arbitrary long byte-string prefix. Region
    analog of `rlp_phase1_e3_longBytes_full_spec_within`: the `lenOfLen` length
    bytes are read from `bytesRegion regionBase bs` starting at byte `off+1`. -/
theorem rlp_phase1_e3_longBytes_full_region_spec_within
    (pfx : EvmAsm.EL.RLP.Byte)
    (v10 v11Old v12Old v13 v14Old : Word)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx = EvmAsm.EL.RLP.PrefixClass.longBytes)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hv13 : v13 = regionBase + BitVec.ofNat 64 off)
    (hwin : ∀ i, i < rlpPrefixLongBytesLenOfLen pfx →
        (off + 1) + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 ((off + 1) + i)) = true)
    (hback : ((e3_target + 12) + 20) + signExtend13 back = (e3_target + 12))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          (rlp_phase1_step_code 0xC0 off3 (base + 16))))).Disjoint
        (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).Disjoint
        (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))) :
    let n := rlpPrefixLongBytesLenOfLen pfx
    cpsTripleWithin (9 + 6 * n) base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop (off + 1)).take n))) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((off + 1) + n))) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (bs.getD ((off + 1) + (n - 1)) 0).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) := by
  intro n
  have hrange := (EvmAsm.EL.RLP.classifyPrefix_longBytes_iff pfx).mp h_class
  have hmod : pfx.toNat % 18446744073709551616 = pfx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hn1 : 1 ≤ n := by
    show 1 ≤ rlpPrefixLongBytesLenOfLen pfx
    unfold rlpPrefixLongBytesLenOfLen; omega
  have hn8 : n ≤ 8 := by
    show rlpPrefixLongBytesLenOfLen pfx ≤ 8
    unfold rlpPrefixLongBytesLenOfLen; omega
  have hv5_lo :
      ¬ BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0x80 : BitVec 12)) := by
    rw [BitVec.ult_eq_decide]
    simp only [BitVec.toNat_setWidth]
    have hk : (((0 : Word) + signExtend12 (0x80 : BitVec 12)).toNat) = 0x80 := by decide
    rw [hk, hmod]; simp only [decide_eq_true_eq]; omega
  have hv5_mid :
      ¬ BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) := by
    rw [BitVec.ult_eq_decide]
    simp only [BitVec.toNat_setWidth]
    have hk : (((0 : Word) + signExtend12 (0xB8 : BitVec 12)).toNat) = 0xB8 := by decide
    rw [hk, hmod]; simp only [decide_eq_true_eq]; omega
  have hv5_hi :
      BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0xC0 : BitVec 12)) := by
    rw [BitVec.ult_eq_decide]
    simp only [BitVec.toNat_setWidth]
    have hk : (((0 : Word) + signExtend12 (0xC0 : BitVec 12)).toNat) = 0xC0 := by decide
    rw [hk, hmod]; simp only [decide_eq_true_eq]; omega
  have prefixSpec := rlp_phase1_e3_full_path_spec'_within
    (pfx.zeroExtend 64) v10 v11Old v13 v14Old off1 off2 off3 base e3_target
    htarget hv5_lo hv5_mid hv5_hi hd_phase3
  have hx14 : (pfx.zeroExtend 64) + signExtend12 (-(0xB7 : BitVec 12))
      = BitVec.ofNat 64 n := by
    have hs : signExtend12 (-(0xB7 : BitVec 12)) = -(0xB7 : Word) := by decide
    rw [hs, ← BitVec.sub_eq_add_neg,
      ← EvmAsm.EL.RLP.rlpPrefixLongBytesLenOfLen_toWord_of_class pfx h_class]
  rw [hx14] at prefixSpec
  -- Re-express the post pointer `v13 + 1` as the region offset `regionBase + ofNat (off+1)`.
  have hptr : v13 + signExtend12 (1 : BitVec 12) = regionBase + BitVec.ofNat 64 (off + 1) := by
    rw [hv13, se12_1, word_ofNat_add_one off]; bv_omega
  rw [hptr] at prefixSpec
  have prefix' : cpsTripleWithin 9 base (e3_target + 12)
      (((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + 1))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ v12Old) ** bytesRegion regionBase bs) (by pcFree) prefixSpec)
  have loop := rlp_phase2_long_loop_region_n_spec_within n hn1 hn8 regionBase v12Old (off + 1) bs
    (e3_target + 12) back halign hover hwin hback
  have loop' : cpsTripleWithin (6 * n) (e3_target + 12) ((e3_target + 12) + 24)
      (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + 1))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop (off + 1)).take n))) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((off + 1) + n))) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (bs.getD ((off + 1) + (n - 1)) 0).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))))
      (by pcFree) loop
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd_loop prefix' loop'

/-- Region full decode path for an arbitrary long-list prefix. Region analog of
    `rlp_phase1_e5_longList_full_spec_within`. -/
theorem rlp_phase1_e5_longList_full_region_spec_within
    (pfx : EvmAsm.EL.RLP.Byte)
    (v10 v11Old v12Old v13 v14Old : Word)
    (regionBase : Word) (off : Nat) (bs : List Byte)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx = EvmAsm.EL.RLP.PrefixClass.longList)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hv13 : v13 = regionBase + BitVec.ofNat 64 off)
    (hwin : ∀ i, i < rlpPrefixLongListLenOfLen pfx →
        (off + 1) + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 ((off + 1) + i)) = true)
    (hback : ((base + 44) + 20) + signExtend13 back = (base + 44))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
    (hd_loop :
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).Disjoint
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))) :
    let n := rlpPrefixLongListLenOfLen pfx
    cpsTripleWithin (11 + 6 * n) base ((base + 44) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))).union
        (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop (off + 1)).take n))) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((off + 1) + n))) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (bs.getD ((off + 1) + (n - 1)) 0).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) := by
  intro n
  have hrange := (EvmAsm.EL.RLP.classifyPrefix_longList_iff pfx).mp h_class
  have hn1 : 1 ≤ n := by
    show 1 ≤ rlpPrefixLongListLenOfLen pfx
    unfold rlpPrefixLongListLenOfLen; omega
  have hn8 : n ≤ 8 := by
    show rlpPrefixLongListLenOfLen pfx ≤ 8
    unfold rlpPrefixLongListLenOfLen; omega
  have prefixSpec := rlp_phase1_e5_full_path_lenOfLen_of_class_spec_within
    pfx v10 v11Old v13 v14Old off1 off2 off3 off4 base h_class hd_phase3
  have hptr : v13 + signExtend12 (1 : BitVec 12) = regionBase + BitVec.ofNat 64 (off + 1) := by
    rw [hv13, se12_1, word_ofNat_add_one off]; bv_omega
  rw [hptr] at prefixSpec
  have prefix' : cpsTripleWithin 11 base (base + 44)
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** bytesRegion regionBase bs)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + 1))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ v12Old) ** bytesRegion regionBase bs) (by pcFree) prefixSpec)
  have loop := rlp_phase2_long_loop_region_n_spec_within n hn1 hn8 regionBase v12Old (off + 1) bs
    (base + 44) back halign hover hwin hback
  have loop' : cpsTripleWithin (6 * n) (base + 44) ((base + 44) + 24)
      (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + 1))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** bytesRegion regionBase bs)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop (off + 1)).take n))) **
        (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 ((off + 1) + n))) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (bs.getD ((off + 1) + (n - 1)) 0).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))))
      (by pcFree) loop
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd_loop prefix' loop'

-- Sanity: the symbolic counts resolve to the expected length-of-length.
example : rlpPrefixLongBytesLenOfLen (0xBA : EvmAsm.EL.RLP.Byte) = 3 := by decide
example : rlpPrefixLongListLenOfLen (0xFF : EvmAsm.EL.RLP.Byte) = 8 := by decide

end EvmAsm.Rv64.RLP
