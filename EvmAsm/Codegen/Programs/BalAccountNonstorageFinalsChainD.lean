/-
  EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainD

  Balance-station glue (bead evm-asm-4ch8f.43.5, slice 4f):

    66  mv a0, s3              (loop exit → tuple span start)
    67  mv a1, s4              (tuple span length)
    70  sd a0, 64(sp)          (tuple-walk cursor spill)
    71  sd a1, 72(sp)          (tuple-walk end spill)

  plus the station-level reject shape shared by every failure path of the
  balance station (field init, find-last loop, tuple items, value capture).
-/

import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsChainC3

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalAccountNonstorageFinalsSpec

/-- Slots 66–67 (`B + 264 → B + 272`): move the last tuple's span
    `(s3, s4)` into the `rlp_walk_init` argument registers. -/
theorem bansf_loopExitMove66_spec (v19 v20 v10 v11 : Word) :
    cpsTripleWithin 2 (B + 264) (B + 272) bansfCode
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11))
      (((.x19 : Reg) ↦ᵣ v19) ** ((.x20 : Reg) ↦ᵣ v20) **
       ((.x10 : Reg) ↦ᵣ v19) ** ((.x11 : Reg) ↦ᵣ v20)) := by
  have s1 := mv_spec_gen_within .x10 .x19 v19 v10 (B + 264) (by decide)
  have s2 := mv_spec_gen_within .x11 .x20 v20 v11 (B + 268) (by decide)
  runBlock s1 s2

#print axioms bansf_loopExitMove66_spec

/-- Slots 70–71 (`B + 280 → B + 288`): spill the tuple-walk cursor and
    window end for the item units. -/
theorem bansf_tupleSpill70_spec (newSp v10 v11 : Word) :
    cpsTripleWithin 2 (B + 280) (B + 288) bansfCR
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       memOwn (newSp + 64) ** memOwn (newSp + 72))
      (((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x2 : Reg) ↦ᵣ newSp) **
       ((newSp + 64) ↦ₘ v10) ** ((newSp + 72) ↦ₘ v11)) := by
  have hsd1 := sd_spec_gen_own_within .x2 .x10 newSp v10 (64 : BitVec 12) (B + 280)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (B + 280) + 4 = B + 284 from by bv_omega] at hsd1
  have hsd1L := liftCode (cr' := bansfCR) hsd1
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 280) bansfProg 70 (.SD .x2 .x10 (64 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd2 := sd_spec_gen_own_within .x2 .x11 newSp v11 (72 : BitVec 12) (B + 284)
  rw [show signExtend12 (72 : BitVec 12) = (72 : Word) from by decide,
      show (B + 284) + 4 = B + 288 from by bv_omega] at hsd2
  have hsd2L := liftCode (cr' := bansfCR) hsd2
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 284) bansfProg 71 (.SD .x2 .x11 (72 : BitVec 12))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) a i h))
  have hsd1F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ v11) ** memOwn (newSp + 72))
    (by pcf) hsd1L
  have hsd2F := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ v10) ** ((newSp + 64) ↦ₘ v10))
    (by pcf) hsd2L
  have hchain := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
    hsd1F hsd2F
  exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq) hchain

#print axioms bansf_tupleSpill70_spec

/-- The station-level reject shape at the epilogue entry (`B + 736`):
    every failure path of the balance station (field init, find-last loop,
    tuple items, value capture) weakens into this.  All station-scratch
    state is released to ownership; the callee-saved anchors survive. -/
def balStationRej (aB newSp oB : Word) (aLen : Nat)
    (acctBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  ((.x10 : Reg) ↦ᵣ (1 : Word)) ** ((.x2 : Reg) ↦ᵣ newSp) **
  memOwn (newSp + 48) ** memOwn (newSp + 56) **
  memOwn (newSp + 64) ** memOwn (newSp + 72) **
  ((.x8 : Reg) ↦ᵣ aB) ** ((.x9 : Reg) ↦ᵣ BitVec.ofNat 64 aLen) **
  ((.x18 : Reg) ↦ᵣ oB) **
  memOwn oB ** memOwnU256 (oB + 8) **
  regOwn .x19 ** regOwn .x20 **
  regOwn .x11 ** regOwn .x12 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x1 **
  bytesRegion aB acctBytes ** F

end BalAccountNonstorageFinalsSpec
end EvmAsm.Codegen
