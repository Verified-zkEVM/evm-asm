/-
  EvmAsm.Rv64.RLP.Phase1E5FullPath

  EL.3 full Phase 1 → Phase 3 e5 (long-list) chain.
-/

import EvmAsm.Rv64.RLP.Phase1CascadePrefixE5
import EvmAsm.Rv64.RLP.Phase1Disjoint
import EvmAsm.Rv64.RLP.Phase3LongList

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
  `cpsTripleWithin base (base + 44)` for the full Phase 1 e5 long-list path:
  all Phase 1 cascade steps fall through to `base + 32`, then the Phase 3
  long-list entry seeds the long-form length loop.

  Post-state: `x14 = v5 - 0xF7` (length-of-length counter), `x11 = 0`,
  `x13 = v13 + 1`, and `x10 = 0xF8` from the final cascade step.
-/
theorem rlp_phase1_e5_full_path_spec_within
    (v5 v10 v11Old v13 v14Old : Word)
    (off1 off2 off3 off4 : BitVec 13) (base : Word)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_2   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_3   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hv5_hi  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xF8 : BitVec 12)))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)) :
    cpsTripleWithin 11 base (base + 44)
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) := by
  have prefix_ := rlp_phase1_cascade_prefix_e5_spec'_within
    v5 v10 off1 off2 off3 off4 base
    hv5_lo hv5_2 hv5_3 hv5_hi
  have prefix' : cpsTripleWithin 8 base (base + 32)
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
        (by pcFree) prefix_)
  have ph3 := rlp_phase3_long_list_spec_within v5 v11Old v13 v14Old (base + 32)
  have ph3' : cpsTripleWithin 3 (base + 32) (base + 44)
      (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12)))
      (by pcFree) ph3
    rw [show (base + 32 : Word) + 12 = base + 44 from by bv_omega] at framed
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd_phase3 prefix' ph3'

theorem rlp_phase1_e5_full_path_spec'_within
    (v5 v10 v11Old v13 v14Old : Word)
    (off1 off2 off3 off4 : BitVec 13) (base : Word)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_2   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_3   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hv5_hi  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xF8 : BitVec 12)))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)) :
    cpsTripleWithin 11 base (base + 44)
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) :=
  rlp_phase1_e5_full_path_spec_within
    v5 v10 v11Old v13 v14Old off1 off2 off3 off4 base
    hv5_lo hv5_2 hv5_3 hv5_hi hd_phase3

/--
  Class-level long-list wrapper for the full Phase 1 → Phase 3 e5 path.
  The output length-of-length counter is restated as the pure RLP
  `rlpPrefixLongListLenOfLen` value.
-/
theorem rlp_phase1_e5_full_path_lenOfLen_of_class_spec_within
    (pfx : EvmAsm.EL.RLP.Byte) (v10 v11Old v13 v14Old : Word)
    (off1 off2 off3 off4 : BitVec 13) (base : Word)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.longList)
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog)) :
    cpsTripleWithin 11 base (base + 44)
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg (base + 32) rlp_phase3_long_list_prog))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
        (.x14 ↦ᵣ
          (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixLongListLenOfLen pfx) : Word))) := by
  have h_range :=
    (EvmAsm.EL.RLP.classifyPrefix_longList_iff pfx).mp h_class
  have hv5_lo :
      ¬ BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0x80 : BitVec 12)) := by
    native_decide +revert
  have hv5_2 :
      ¬ BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0xB8 : BitVec 12)) := by
    native_decide +revert
  have hv5_3 :
      ¬ BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0xC0 : BitVec 12)) := by
    native_decide +revert
  have hv5_hi :
      ¬ BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0xF8 : BitVec 12)) := by
    native_decide +revert
  have h_add_sub :
      pfx.zeroExtend 64 + signExtend12 (-(0xF7 : BitVec 12)) =
        pfx.zeroExtend 64 - (0xF7 : Word) := by
    native_decide +revert
  have h_len :=
    EvmAsm.EL.RLP.rlpPrefixLongListLenOfLen_toWord_of_class pfx h_class
  have h_add :
      pfx.zeroExtend 64 + signExtend12 (-(0xF7 : BitVec 12)) =
        (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixLongListLenOfLen pfx) : Word) := by
    rw [h_add_sub, ← h_len]
  rw [← h_add]
  exact rlp_phase1_e5_full_path_spec'_within
    (pfx.zeroExtend 64) v10 v11Old v13 v14Old off1 off2 off3 off4 base
    hv5_lo hv5_2 hv5_3 hv5_hi hd_phase3

end EvmAsm.Rv64.RLP
