/-
  EvmAsm.Rv64.RLP.Phase1E3LongBytesFull

  EL.3 full Phase 1 → Phase 3 → Phase 2 path for an **arbitrary** long
  byte-string prefix (e3, `0xB8`–`0xBF`). Composes the Phase 1 e3 cascade +
  Phase 3 long-string entry (`rlp_phase1_e3_full_path_spec'_within`, leaving the
  counter `x14 = pfx − 0xB7`, rewritten here to `ofNat (rlpPrefixLongBytesLenOfLen
  pfx)`) with the general n-iteration loop closure
  (`rlp_phase2_long_loop_n_byte_spec_within`) at `n = rlpPrefixLongBytesLenOfLen
  pfx ∈ [1,8]`.

  Result: one theorem, over any long byte-string prefix, giving the decoded
  payload length `x11 = ofNat (Nat.fromBytesBE (length bytes))`. Long-string
  analogue of `rlp_phase1_e5_longList_full_spec_within`.
-/

import EvmAsm.Rv64.RLP.Phase1E3FullPath
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

/-- Full decode path for an arbitrary long byte-string prefix `pfx`
    (`classifyPrefix pfx = .longBytes`). The length-of-length
    `n = rlpPrefixLongBytesLenOfLen pfx` is dispatched through the single
    long-form loop; `x11` holds the decoded payload length per `Nat.fromBytesBE`. -/
theorem rlp_phase1_e3_longBytes_full_spec_within
    (pfx : EvmAsm.EL.RLP.Byte)
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 back : BitVec 13)
    (base e3_target : Word)
    (htarget : (base + 16 + 4) + signExtend13 off3 = e3_target)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx = EvmAsm.EL.RLP.PrefixClass.longBytes)
    (hwin : ∀ i, i < rlpPrefixLongBytesLenOfLen pfx →
        alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = dwordAddr
        ∧ isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = true)
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
    let ptr := v13 + signExtend12 (1 : BitVec 12)
    let n := rlpPrefixLongBytesLenOfLen pfx
    cpsTripleWithin (9 + 6 * n) base ((e3_target + 12) + 24)
      (((((rlp_phase1_step_code 0x80 off1 base).union
          ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
            (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
          (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))).union
          (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList wordVal ptr n))) **
        (.x13 ↦ᵣ (ptr + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ
          (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 (n - 1)))).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  intro ptr n
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
  -- Rewrite the counter `x14 = pfx − 0xB7` to `ofNat (lenOfLen pfx)`.
  have hx14 : (pfx.zeroExtend 64) + signExtend12 (-(0xB7 : BitVec 12))
      = BitVec.ofNat 64 n := by
    have hs : signExtend12 (-(0xB7 : BitVec 12)) = -(0xB7 : Word) := by decide
    rw [hs, ← BitVec.sub_eq_add_neg,
      ← EvmAsm.EL.RLP.rlpPrefixLongBytesLenOfLen_toWord_of_class pfx h_class]
  rw [hx14] at prefixSpec
  have prefix' : cpsTripleWithin 9 base (e3_target + 12)
      (((rlp_phase1_step_code 0x80 off1 base).union
         ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
           (rlp_phase1_step_code 0xC0 off3 (base + 16)))).union
         (CodeReq.ofProg e3_target rlp_phase3_long_string_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ v12Old) ** (dwordAddr ↦ₘ wordVal)) (by pcFree) prefixSpec)
  have loop := rlp_phase2_long_loop_n_byte_spec_within n hn1 hn8 ptr v12Old wordVal
    dwordAddr (e3_target + 12) back hwin hback
  have loop' : cpsTripleWithin (6 * n) (e3_target + 12) ((e3_target + 12) + 24)
      (CodeReq.ofProg (e3_target + 12) (rlp_phase2_long_loop_body_prog back))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList wordVal ptr n))) **
        (.x13 ↦ᵣ (ptr + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ
          (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 (n - 1)))).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xC0 : BitVec 12))))
      (by pcFree) loop
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd_loop prefix' loop'

-- Sanity: the symbolic count `n` resolves to the expected length-of-length.
example : rlpPrefixLongBytesLenOfLen (0xBA : EvmAsm.EL.RLP.Byte) = 3 := by decide
example : rlpPrefixLongBytesLenOfLen (0xBF : EvmAsm.EL.RLP.Byte) = 8 := by decide

end EvmAsm.Rv64.RLP
