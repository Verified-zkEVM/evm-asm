/-
  EvmAsm.Rv64.RLP.Phase1E4FullPath

  EL.3 full Phase 1 → Phase 3 e4 (short-list) chain.
-/

import EvmAsm.Rv64.RLP.Phase1CascadePrefixE4
import EvmAsm.Rv64.RLP.Phase1Disjoint
import EvmAsm.Rv64.RLP.Phase3ShortList

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
  `cpsTripleWithin base (e4_target + 8)` for the full Phase 1 e4
  short-list path: cascade prefix to `e4_target`, then the Phase 3
  short-list emitter.

  Post-state: `x11 = v5 - 0xC0` (payload length), `x13 = v13 + 1`
  (data pointer past prefix), `x10 = 0xF8` (cascade-step constant residue),
  with `x5` and `x0` preserved.
-/
theorem rlp_phase1_e4_full_path_spec_within
    (v5 v10 v11Old v13 : Word)
    (off1 off2 off3 off4 : BitVec 13) (base e4_target : Word)
    (htarget : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_2   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_3   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hv5_hi  : BitVec.ult v5 ((0 : Word) + signExtend12 (0xF8 : BitVec 12)))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)) :
    cpsTripleWithin 10 base (e4_target + 8)
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have prefix_ := rlp_phase1_cascade_prefix_e4_spec'_within
    v5 v10 off1 off2 off3 off4 base e4_target
    htarget hv5_lo hv5_2 hv5_3 hv5_hi
  have prefix' : cpsTripleWithin 8 base e4_target
      ((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13)) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13)) (by pcFree) prefix_)
  have ph3 := rlp_phase3_short_list_spec_within v5 v11Old v13 e4_target
  have ph3' : cpsTripleWithin 2 e4_target (e4_target + 8)
      (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) :=
    cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))))
        (by pcFree) ph3)
  exact cpsTripleWithin_seq hd_phase3 prefix' ph3'

theorem rlp_phase1_e4_full_path_spec'_within
    (v5 v10 v11Old v13 : Word)
    (off1 off2 off3 off4 : BitVec 13) (base e4_target : Word)
    (htarget : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (hv5_lo  : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0x80 : BitVec 12)))
    (hv5_2   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xB8 : BitVec 12)))
    (hv5_3   : ¬ BitVec.ult v5 ((0 : Word) + signExtend12 (0xC0 : BitVec 12)))
    (hv5_hi  : BitVec.ult v5 ((0 : Word) + signExtend12 (0xF8 : BitVec 12)))
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)) :
    cpsTripleWithin 10 base (e4_target + 8)
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) :=
  rlp_phase1_e4_full_path_spec_within
    v5 v10 v11Old v13 off1 off2 off3 off4 base e4_target
    htarget hv5_lo hv5_2 hv5_3 hv5_hi hd_phase3

/--
  Class-level short-list wrapper for the full Phase 1 → Phase 3 e4 path.
  The executable path theorem still supplies the branch facts; this restates
  the output length as the pure RLP short-list payload length.
-/
theorem rlp_phase1_e4_full_path_payload_len_of_class_spec_within
    (pfx : EvmAsm.EL.RLP.Byte) (v10 v11Old v13 : Word)
    (off1 off2 off3 off4 : BitVec 13) (base e4_target : Word)
    (htarget : (base + 24 + 4) + signExtend13 off4 = e4_target)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.shortList)
    (hd_phase3 :
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24)))))).Disjoint
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog)) :
    cpsTripleWithin 10 base (e4_target + 8)
      (((rlp_phase1_step_code 0x80 off1 base).union
        ((rlp_phase1_step_code 0xB8 off2 (base + 8)).union
          ((rlp_phase1_step_code 0xC0 off3 (base + 16)).union
            (rlp_phase1_step_code 0xF8 off4 (base + 24))))).union
        (CodeReq.ofProg e4_target rlp_phase3_short_list_prog))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) **
        (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ ((0 : Word) + signExtend12 (0xF8 : BitVec 12))) **
        (.x11 ↦ᵣ
          (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixShortListPayloadLen pfx) : Word)) **
        (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  have h_range :=
    (EvmAsm.EL.RLP.classifyPrefix_shortList_iff pfx).mp h_class
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
      BitVec.ult (pfx.zeroExtend 64)
        ((0 : Word) + signExtend12 (0xF8 : BitVec 12)) := by
    native_decide +revert
  have h_add_sub :
      pfx.zeroExtend 64 + signExtend12 (-(0xC0 : BitVec 12)) =
        pfx.zeroExtend 64 - (0xC0 : Word) := by
    native_decide +revert
  have h_len :=
    EvmAsm.EL.RLP.rlpPrefixShortListPayloadLen_toWord_of_class pfx h_class
  have h_add :
      pfx.zeroExtend 64 + signExtend12 (-(0xC0 : BitVec 12)) =
        (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixShortListPayloadLen pfx) : Word) := by
    rw [h_add_sub, ← h_len]
  rw [← h_add]
  exact rlp_phase1_e4_full_path_spec'_within
    (pfx.zeroExtend 64) v10 v11Old v13 off1 off2 off3 off4 base e4_target
    htarget hv5_lo hv5_2 hv5_3 hv5_hi hd_phase3

end EvmAsm.Rv64.RLP
