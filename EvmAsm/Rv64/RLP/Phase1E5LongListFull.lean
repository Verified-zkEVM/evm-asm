/-
  EvmAsm.Rv64.RLP.Phase1E5LongListFull

  EL.3 full Phase 1 → Phase 3 → Phase 2 path for an **arbitrary** long-list
  prefix (e5, `0xF8`–`0xFF`). Composes the class-level Phase 1 + Phase 3 entry
  (`rlp_phase1_e5_full_path_lenOfLen_of_class_spec_within`, which leaves the
  length-of-length counter `x14 = ofNat (rlpPrefixLongListLenOfLen pfx)`) with
  the general n-iteration loop closure (`rlp_phase2_long_loop_n_byte_spec_within`)
  at the symbolic count `n = rlpPrefixLongListLenOfLen pfx ∈ [1,8]`.

  Result: one theorem, over any long-list prefix, giving the decoded payload
  length `x11 = ofNat (Nat.fromBytesBE (length bytes))` and payload pointer
  `x13`. Collapses the eight concrete `rlp_phase1_e5_0x…_…_byte_length_*` paths.
-/

import EvmAsm.Rv64.RLP.Phase1E5FullPath
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

/-- Full decode path for an arbitrary long-list prefix `pfx` (`classifyPrefix
    pfx = .longList`). The length-of-length `n = rlpPrefixLongListLenOfLen pfx`
    is dispatched through the single long-form loop; `x11` holds the decoded
    payload length per the pure spec `Nat.fromBytesBE`. -/
theorem rlp_phase1_e5_longList_full_spec_within
    (pfx : EvmAsm.EL.RLP.Byte)
    (v10 v11Old v12Old v13 v14Old wordVal dwordAddr : Word)
    (off1 off2 off3 off4 back : BitVec 13)
    (base : Word)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx = EvmAsm.EL.RLP.PrefixClass.longList)
    (hwin : ∀ i, i < rlpPrefixLongListLenOfLen pfx →
        alignToDword ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = dwordAddr
        ∧ isValidByteAccess ((v13 + signExtend12 (1 : BitVec 12)) + BitVec.ofNat 64 i) = true)
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
    let ptr := v13 + signExtend12 (1 : BitVec 12)
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
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList wordVal ptr n))) **
        (.x13 ↦ᵣ (ptr + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ
          (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 (n - 1)))).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
  intro ptr n
  have hrange := (EvmAsm.EL.RLP.classifyPrefix_longList_iff pfx).mp h_class
  have hn1 : 1 ≤ n := by
    show 1 ≤ rlpPrefixLongListLenOfLen pfx
    unfold rlpPrefixLongListLenOfLen; omega
  have hn8 : n ≤ 8 := by
    show rlpPrefixLongListLenOfLen pfx ≤ 8
    unfold rlpPrefixLongListLenOfLen; omega
  -- Prefix side: Phase 1 classify + Phase 3 long-list entry, x14 = ofNat n.
  have prefixSpec := rlp_phase1_e5_full_path_lenOfLen_of_class_spec_within
    pfx v10 v11Old v13 v14Old off1 off2 off3 off4 base h_class hd_phase3
  have prefix' : cpsTripleWithin 11 base (base + 44)
      ((((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x12 ↦ᵣ v12Old) ** (.x13 ↦ᵣ v13) **
        (.x14 ↦ᵣ v14Old) ** (dwordAddr ↦ₘ wordVal))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x12 ↦ᵣ v12Old) ** (dwordAddr ↦ₘ wordVal)) (by pcFree) prefixSpec)
  -- Loop side: general n-iteration closure at n = lenOfLen pfx.
  have loop := rlp_phase2_long_loop_n_byte_spec_within n hn1 hn8 ptr v12Old wordVal
    dwordAddr (base + 44) back hwin hback
  have loop' : cpsTripleWithin (6 * n) (base + 44) ((base + 44) + 24)
      (CodeReq.ofProg (base + 44) (rlp_phase2_long_loop_body_prog back))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ v12Old) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (BitVec.ofNat 64 n)) ** (dwordAddr ↦ₘ wordVal))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (rlpLoopByteList wordVal ptr n))) **
        (.x13 ↦ᵣ (ptr + BitVec.ofNat 64 n)) ** (.x14 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ
          (extractByte wordVal (byteOffset (ptr + BitVec.ofNat 64 (n - 1)))).zeroExtend 64) **
        (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))))
      (by pcFree) loop
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd_loop prefix' loop'

-- Sanity: the symbolic count `n` resolves to the expected length-of-length.
example : rlpPrefixLongListLenOfLen (0xFA : EvmAsm.EL.RLP.Byte) = 3 := by decide
example : rlpPrefixLongListLenOfLen (0xFF : EvmAsm.EL.RLP.Byte) = 8 := by decide

end EvmAsm.Rv64.RLP
