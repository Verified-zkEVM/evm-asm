/-
  EvmAsm.Rv64.RLP.Phase3ShortList

  EL.3 Phase 3 (short-list exit): flat decode entry for the short-list
  category.
-/

import EvmAsm.EL.RLP.ProgramSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
  Two-instruction short-list flat-decode emitter:
  `ADDI x11, x5, -0xC0 ; ADDI x13, x13, 1`.

  The first instruction extracts the short-list payload byte length from the
  prefix. The second advances the input pointer past the prefix byte.
-/
def rlp_phase3_short_list_prog : Program :=
  [.ADDI .x11 .x5 (-0xC0), .ADDI .x13 .x13 1]

theorem rlp_phase3_short_list_length :
    rlp_phase3_short_list_prog.length = 2 := rfl

/--
  Step-bounded spec for the short-list Phase 3 entry.

  After the two-instruction block, `x11` holds `prefix - 0xC0` and `x13`
  points at the first payload byte. The caller supplies the prefix-class
  range fact when this arithmetic is interpreted as an RLP payload length.
-/
theorem rlp_phase3_short_list_spec_within (v5 v11Old v13 : Word) (base : Word) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_list_prog)
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
  rw [show CodeReq.ofProg base rlp_phase3_short_list_prog =
      (CodeReq.singleton base (.ADDI .x11 .x5 (-0xC0))).union
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1)) from CodeReq.ofProg_pair]
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x11 .x5 (-0xC0)))
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have s1Base := addi_spec_gen_within .x11 .x5 v11Old v5 (-0xC0) base (by nofun)
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x11 .x5 (-0xC0)))
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
       (.x13 ↦ᵣ v13)) := by
    have framed := cpsTripleWithin_frameR (.x13 ↦ᵣ v13) (by pcFree) s1Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  have s2Base := addi_spec_gen_same_within .x13 v13 1 (base + 4) (by nofun)
  have s2 : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (.ADDI .x13 .x13 1))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
       (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ (v5 + signExtend12 (-(0xC0 : BitVec 12)))))
      (by pcFree) s2Base
    rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at framed
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  exact cpsTripleWithin_seq hd s1 s2

theorem rlp_phase3_short_list_payload_len_of_class_spec_within
    (pfx : EvmAsm.EL.RLP.Byte) (v11Old v13 : Word) (base : Word)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.shortList) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base rlp_phase3_short_list_prog)
      ((.x5 ↦ᵣ pfx.zeroExtend 64) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      ((.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x11 ↦ᵣ
        (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixShortListPayloadLen pfx) : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12)))) := by
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
  exact rlp_phase3_short_list_spec_within (pfx.zeroExtend 64) v11Old v13 base

end EvmAsm.Rv64.RLP
