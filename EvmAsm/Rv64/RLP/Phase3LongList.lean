/-
  EvmAsm.Rv64.RLP.Phase3LongList

  EL.3 Phase 3 (long-list exit): seed the long-form length-of-length loop
  for the long-list category.
-/

import EvmAsm.EL.RLP.ProgramSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
  Three-instruction long-list entry emitter:
  `ADDI x14, x5, -0xF7 ; ADDI x11, x0, 0 ; ADDI x13, x13, 1`.

  The block computes the long-list length-of-length counter, clears the length
  accumulator, and advances the input pointer past the prefix byte.
-/
def rlp_phase3_long_list_prog : Program :=
  [.ADDI .x14 .x5 (-0xF7), .ADDI .x11 .x0 0, .ADDI .x13 .x13 1]

theorem rlp_phase3_long_list_length :
    rlp_phase3_long_list_prog.length = 3 := rfl

/--
  Step-bounded spec for the long-list Phase 3 entry.

  After the block, `x14` holds `prefix - 0xF7`, `x11` is cleared, and `x13`
  points at the first encoded length byte. A caller composes this with the
  Phase 1 long-list exit fact to interpret `x14` as an RLP length-of-length.
-/
theorem rlp_phase3_long_list_spec_within
    (v5 v11Old v13 v14Old : Word) (base : Word) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_list_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) := by
  have hcr_eq : CodeReq.ofProg base rlp_phase3_long_list_prog =
      (CodeReq.singleton base (.ADDI .x14 .x5 (-0xF7))).union
      (CodeReq.ofProg (base + 4) [.ADDI .x11 .x0 0, .ADDI .x13 .x13 1]) := by
    simp only [rlp_phase3_long_list_prog, CodeReq.ofProg_cons]
  rw [hcr_eq]
  have hcr_tail : CodeReq.ofProg (base + 4) [.ADDI .x11 .x0 0, .ADDI .x13 .x13 1] =
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0)).union
      (CodeReq.singleton ((base + 4) + 4) (.ADDI .x13 .x13 1)) :=
    CodeReq.ofProg_pair
  have s1Base := addi_spec_gen_within .x14 .x5 v14Old v5 (-0xF7) base (by nofun)
  have s1 : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x14 .x5 (-0xF7)))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13))
      (by pcFree) s1Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  have s2Base := addi_spec_gen_within .x11 .x0 v11Old (0 : Word) 0 (base + 4) (by nofun)
  have hsig0 : (0 : Word) + signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  rw [hsig0] at s2Base
  have s2 : cpsTripleWithin 1 (base + 4) ((base + 4) + 4)
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12)))))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ v5) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12)))))
      (by pcFree) s2Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  have s3Base := addi_spec_gen_same_within .x13 v13 1 ((base + 4) + 4) (by nofun)
  have s3 : cpsTripleWithin 1 ((base + 4) + 4) (((base + 4) + 4) + 4)
      (CodeReq.singleton ((base + 4) + 4) (.ADDI .x13 .x13 1))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) ** (.x13 ↦ᵣ v13) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12)))))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12))))) := by
    have framed := cpsTripleWithin_frameR
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ v5) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x14 ↦ᵣ (v5 + signExtend12 (-(0xF7 : BitVec 12)))))
      (by pcFree) s3Base
    exact cpsTripleWithin_weaken
      (fun _ hp => by xperm_hyp hp)
      (fun _ hp => by xperm_hyp hp)
      framed
  have hd23 : CodeReq.Disjoint
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0))
      (CodeReq.singleton ((base + 4) + 4) (.ADDI .x13 .x13 1)) :=
    CodeReq.Disjoint.singleton (by bv_omega)
  have s23_raw := cpsTripleWithin_seq hd23 s2 s3
  have hexit : (((base + 4) + 4) + 4 : Word) = base + 12 := by bv_omega
  rw [← hcr_tail, hexit] at s23_raw
  have hd1_23 : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x14 .x5 (-0xF7)))
      (CodeReq.ofProg (base + 4) [.ADDI .x11 .x0 0, .ADDI .x13 .x13 1]) := by
    apply CodeReq.Disjoint.ofProg_cons_right
    · exact CodeReq.Disjoint.singleton (by bv_omega)
    apply CodeReq.Disjoint.ofProg_cons_right
    · exact CodeReq.Disjoint.singleton (by bv_omega)
    exact CodeReq.Disjoint.ofProg_nil_right _ _
  exact cpsTripleWithin_seq hd1_23 s1 s23_raw

theorem rlp_phase3_long_list_lenOfLen_of_class_spec_within
    (pfx : EvmAsm.EL.RLP.Byte) (v11Old v13 v14Old : Word) (base : Word)
    (h_class : EvmAsm.EL.RLP.classifyPrefix pfx =
      EvmAsm.EL.RLP.PrefixClass.longList) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base rlp_phase3_long_list_prog)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x11 ↦ᵣ v11Old) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14Old))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ pfx.zeroExtend 64) **
       (.x11 ↦ᵣ (0 : Word)) **
       (.x13 ↦ᵣ (v13 + signExtend12 (1 : BitVec 12))) **
       (.x14 ↦ᵣ
        (BitVec.ofNat 64 (EvmAsm.EL.RLP.rlpPrefixLongListLenOfLen pfx) : Word))) := by
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
  exact rlp_phase3_long_list_spec_within (pfx.zeroExtend 64) v11Old v13 v14Old base

end EvmAsm.Rv64.RLP
