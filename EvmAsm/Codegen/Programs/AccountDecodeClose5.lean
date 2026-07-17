/-
  `accountDecode_prog` caller-contract composition, part 5 — the four per-field
  backbone merges and the whole-program close.

  Close4 supplied the whole-program outcome model (`adWholePost`), the shared
  failure arm (`adFailArm`) and the generic continue reshape (`adContReshape`).
  This module stitches the four field stages, their length checks and the field
  materialisers into a single `AB+56 → raSaved` triple, then prepends the
  prologue for the whole-program `account_decode_spec_within`.

  Because every field decodes via the same `rlp_list_nth_item` (K20) callee and
  shares the outer frame (`spW = newSp = sp0 - 64`), there is no stack transform:
  ONE `adFailArm` and ONE `adContReshape` cover all four boundaries.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeClose4
import EvmAsm.Codegen.Programs.AccountDecodeLoop
import EvmAsm.Codegen.Programs.AccountDecodeNonceLoop
import EvmAsm.Codegen.Programs.AccountDecodeBalanceLoop

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame regsAt_listNthFrame
  Success Result Failure)
open EvmAsm.Evm64.Terminating (copyIntoRegion)

/-! ## Local register-ownership introduction helpers -/

/-- Introduce THREE owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn3
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 : Reg} {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hO2
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2, hv3⟩, hRb⟩ hpc

/-! ## Copy-loop instruction fetch bundles for the fixed-32 fields -/

/-- The six fetch facts of the storage-root copy loop [90]-[95] (`GB = AB+360`,
    destination register `x20`). -/
def adCopyFetchRoot : CopyFetch .x20 (AB + 360) where
  lbu := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 360) accountDecode_prog 90
    (.LBU .x29 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  sb := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 360 + 4) accountDecode_prog 91
    (.SB .x20 .x29 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  a28 := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 360 + 8) accountDecode_prog 92
    (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  ard := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 360 + 12) accountDecode_prog 93
    (.ADDI .x20 .x20 (1 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  a6 := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 360 + 16) accountDecode_prog 94
    (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  bne := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 360 + 20) accountDecode_prog 95
    (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi

/-- The six fetch facts of the code-hash copy loop [116]-[121] (`GB = AB+464`,
    destination register `x21`). -/
def adCopyFetchCode : CopyFetch .x21 (AB + 464) where
  lbu := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 464) accountDecode_prog 116
    (.LBU .x29 .x28 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  sb := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 464 + 4) accountDecode_prog 117
    (.SB .x21 .x29 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  a28 := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 464 + 8) accountDecode_prog 118
    (.ADDI .x28 .x28 (1 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  ard := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 464 + 12) accountDecode_prog 119
    (.ADDI .x21 .x21 (1 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  a6 := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 464 + 16) accountDecode_prog 120
    (.ADDI .x6 .x6 (-1 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi
  bne := fun a i hi => CodeReq.ofProg_mem_at AB (AB + 464 + 20) accountDecode_prog 121
    (.BNE .x6 .x0 (-20 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide) rfl
    (by rw [ad_length]; decide) a i hi

end EvmAsm.Codegen.AccountDecodeSpec
