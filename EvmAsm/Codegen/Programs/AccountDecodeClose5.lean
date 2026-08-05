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

import EvmAsm.Codegen.Programs.AccountDecodeFold
import EvmAsm.Codegen.Programs.AccountDecodeLoop
import EvmAsm.Codegen.Programs.AccountDecodeNonceLoop
import EvmAsm.Codegen.Programs.AccountDecodeBalanceLoop

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame regsAt_listNthFrame
  listNthFrameRegs_implies_owned Success Result Failure)
open EvmAsm.Evm64.Terminating (copyIntoRegion)

/-! ## Local register-ownership introduction helpers -/

/-- Introduce TWO owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn2
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 : Reg} {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** regOwn r1 ** regOwn r2) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, ⟨v2, hv2⟩⟩ := hO1
  exact h v1 v2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu, ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, hv2⟩, hRb⟩ hpc

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

/-! ## `pcFree` discharge macro for the continue-frame reshapes -/

local macro "pcfa" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | exact pcFree_pure
    | exact pcFree_stackFree _ _
    | exact pcFree_adContFrame _ _ _ _ _ _ _ _ _ _
    | exact pcFree_adScratch _
    | exact pcFree_adCommon _ _ _
    | apply pcFree_sepConj)

/-- The clobbered temporaries (a mix of concrete `regIs` and already-owned
    `regOwn` cells) weaken into `adScratch`; `x0`/`x15` are kept as concrete. -/
theorem adScratch_of_regs (codeOut v5 v6 v7 v11 v12 v28 : Word) : ∀ h,
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
     ((.x28 : Reg) ↦ᵣ v28) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ codeOut)) h →
    adScratch codeOut h := by
  intro h hp
  unfold adScratch
  exact sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
    (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_implies_regOwn .x28)))))))) h hp

/-- Variant of `adScratch_of_regs` for the fail edge, where `x28` is already
    owned (never materialised to a concrete cursor). -/
theorem adScratch_of_regs_own (codeOut v5 v6 v7 v11 v12 : Word) : ∀ h,
    (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
     regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x15 : Reg) ↦ᵣ codeOut)) h →
    adScratch codeOut h := by
  intro h hp
  unfold adScratch
  exact sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
    (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x11)
    (sepConj_mono_left (regIs_implies_regOwn .x12))))) h hp

/-- Variant of `adScratch_of_regs` for a stage fail edge, where `x5/x6/x7` and
    `x28` are all already owned; only `x11`/`x12` are concrete. -/
theorem adScratch_of_regs_own2 (codeOut v11 v12 : Word) : ∀ h,
    (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x15 : Reg) ↦ᵣ codeOut)) h →
    adScratch codeOut h := by
  intro h hp
  unfold adScratch
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono_left (regIs_implies_regOwn .x12)))))
    h hp

/-! ## Field-3 success tail (`AB+448 → raIn`): code copy + `Decoded` tie

    On the `len = 32` continue edge of field 3's length check, the 20-... (32-)
    byte code hash is copied into the final output cell, then `adSuccessEpi`
    stores `a0 := 0` and returns.  The `Decoded` verdict, assembled from the four
    field `Success` facts, is carried through the epilogue and unpacked into the
    whole-program success post. -/

set_option maxRecDepth 8000 in
theorem adField3Success
    (sp0 spW raIn listBase len nonceOut balanceOut rootOut codeOut o0 o1 o2 o3 l0 l1 l2 l3
      x28v x29v v11 v12 : Word)
    (bytes oldRoot oldCode rootCell : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hDecoded : Decoded bytes listBase listLen o0 l0 o1 l1 o2 l2 o3 l3)
    (hrootCell : rootCell = hashCell bytes oldRoot o2 l2.toNat adEmptyTrieRootBytes)
    (hf3 : Success bytes listBase listLen 3 o3 l3)
    (hl3 : l3 = (32 : Word)) :
    let savedCaller : Saved :=
      { ra := raIn, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (4 + (192 + (1 + (1 + 11)))) (AB + 448) raIn fullCode
      (((.x6 : Reg) ↦ᵣ l3) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
       (adLengthAddr ↦ₘ l3) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 424)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ s4v) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x28 : Reg) ↦ᵣ x28v) ** ((.x29 : Reg) ↦ᵣ x29v) **
       regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o3) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
       bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
       bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode ** adFoldConstants)
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hoffnorm : listBase + o3 = listBase + BitVec.ofNat 64 (o3.toNat + 0) := by
    rw [Nat.add_zero]; congr 1
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt o3.isLt]
  have hsrcbound : o3.toNat + 0 + (31 + 1) ≤ bytes.length := by
    have hcb := adSuccessContentBound bytes listBase listLen 3 o3 l3 hslack hover hf3
    rw [hl3] at hcb; simp only [show (32 : Word).toNat = 32 from by decide] at hcb; omega
  -- code copy source-cursor setup [112]-[115].
  have hcs := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ l3) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l3) **
     ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 424)) ** ((.x9 : Reg) ↦ᵣ len) **
     ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ s4v) **
     ((.x21 : Reg) ↦ᵣ codeOut) ** stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x29 : Reg) ↦ᵣ x29v) **
     regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller ** bytesRegion listBase bytes **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode ** adFoldConstants)
    (by pcfa) (adCodeCopySetup listBase o3 adLengthAddr x28v)
  -- code copy loop [116]-[121].
  have hcl := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l3) **
     ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 424)) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) **
     ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ s4v) **
     stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
     ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut (rootCell) ** (adOffsetAddr ↦ₘ o3) ** adFoldConstants)
    (by pcfa)
    (adCopyLoop .x21 (AB + 464) listBase codeOut x29v bytes oldCode o3.toNat 0 0 31
      (by decide) adCopyFetchCode hsalign hcalign hsrcbound (by rw [hcodelen])
      hover (by rw [hcodelen]; exact hcover) hvalid
      (by intro k hk; rw [hcodelen] at hk; exact hcvalid k hk))
  -- bridge copysetup → copyloop.
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show (BitVec.ofNat 64 (31 + 1) : Word) = l3 from by rw [hl3]; decide,
        show listBase + BitVec.ofNat 64 (o3.toNat + 0) = listBase + o3 from hoffnorm.symm,
        show codeOut + BitVec.ofNat 64 (0 + 0) = codeOut from by bv_omega,
        show copyIntoRegion oldCode bytes 0 o3.toNat 0 = oldCode from rfl]
      xperm_hyp hp)
    hcs hcl
  -- the two trailing NOPs [122]-[123] (`AB+488 → AB+496`).
  have hnop1 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 488) accountDecode_prog 122 .NOP (by bv_omega)
        (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) (nop_spec_within (AB + 488)))
  have hnop2 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 492) accountDecode_prog 123 .NOP (by bv_omega)
        (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) (nop_spec_within (AB + 492)))
  -- success tail F: the four output cells, the input, the two data cells, the
  -- reclaimed scratch stack and the clobbered temporaries.
  set F : Assertion :=
    (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
    bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
    bytesRegion rootOut (rootCell) **
    bytesRegion codeOut (fixed32Copied bytes oldCode o3) ** bytesRegion listBase bytes **
    (adOffsetAddr ↦ₘ o3) ** (adLengthAddr ↦ₘ l3) ** stackFree spW 8 ** adScratch codeOut **
    adFoldConstants
    with hFdef
  have hF : F.pcFree := by rw [hFdef]; unfold adScratch; pcfa
  have hepi := adSuccessEpi sp0 spW (0 : Word) savedCaller F hF hspW
    (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)
  -- frame the NOPs by the ambient state at AB+488 / AB+492.
  have hnop1f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o3.toNat + (0 + (31 + 1))))) **
     ((.x21 : Reg) ↦ᵣ (codeOut + BitVec.ofNat 64 (0 + (0 + (31 + 1))))) ** regOwn .x29 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     bytesRegion codeOut (copyIntoRegion oldCode bytes 0 o3.toNat (0 + (31 + 1))) **
     (.x5 ↦ᵣ adOffsetAddr) ** (.x7 ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l3) ** (.x2 ↦ᵣ spW) **
     (.x1 ↦ᵣ (AB + 424)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ nonceOut) **
     (.x19 ↦ᵣ balanceOut) **
     (.x20 ↦ᵣ s4v) ** stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
     (.x15 ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut (rootCell) ** (adOffsetAddr ↦ₘ o3) ** adFoldConstants)
    (by pcfa) hnop1
  rw [sepConj_emp_left'] at hnop1f
  have hnop2f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o3.toNat + (0 + (31 + 1))))) **
     ((.x21 : Reg) ↦ᵣ (codeOut + BitVec.ofNat 64 (0 + (0 + (31 + 1))))) ** regOwn .x29 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     bytesRegion codeOut (copyIntoRegion oldCode bytes 0 o3.toNat (0 + (31 + 1))) **
     (.x5 ↦ᵣ adOffsetAddr) ** (.x7 ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l3) ** (.x2 ↦ᵣ spW) **
     (.x1 ↦ᵣ (AB + 424)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ nonceOut) **
     (.x19 ↦ᵣ balanceOut) **
     (.x20 ↦ᵣ s4v) ** stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ v11) **
     (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
     (.x15 ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut (rootCell) ** (adOffsetAddr ↦ₘ o3) ** adFoldConstants)
    (by pcfa) hnop2
  rw [sepConj_emp_left'] at hnop2f
  -- compose copy ;; nop ;; nop ;; success epilogue.
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hnop1f
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 hnop2f
  have c4 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [hFdef]
      have hg : (((.x10 : Reg) ↦ᵣ (0 : Word)) **
          (((.x2 : Reg) ↦ᵣ spW) **
           (((.x1 : Reg) ↦ᵣ (AB + 424)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
            ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
            ((.x20 : Reg) ↦ᵣ s4v) **
            ((.x21 : Reg) ↦ᵣ (codeOut + BitVec.ofNat 64 (0 + (0 + (31 + 1)))))) **
           savedFrame spW savedCaller) **
          ((nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
           bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
           bytesRegion rootOut (rootCell) **
           bytesRegion codeOut (fixed32Copied bytes oldCode o3) ** bytesRegion listBase bytes **
           (adOffsetAddr ↦ₘ o3) ** (adLengthAddr ↦ₘ l3) ** stackFree spW 8 **
           (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x6 : Reg) ↦ᵣ (0 : Word)) **
            ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
            regOwn .x13 ** regOwn .x14 **
            ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o3.toNat + (0 + (31 + 1))))) **
            regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x15 : Reg) ↦ᵣ codeOut)) ** adFoldConstants)) h := by
        rw [show copyIntoRegion oldCode bytes 0 o3.toNat (0 + (31 + 1))
            = fixed32Copied bytes oldCode o3 from rfl] at hp
        xperm_hyp hp
      exact sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
          listBase len nonceOut balanceOut s4v
          (codeOut + BitVec.ofNat 64 (0 + (0 + (31 + 1)))) h'
          (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (adScratch_of_regs codeOut adOffsetAddr (0 : Word) (32 : Word)
              v11 v12
              (listBase + BitVec.ofNat 64 (o3.toNat + (0 + (31 + 1))))))))))))))) h hg)
    c3 hepi
  -- weaken pre (stated → copysetup pre) and post (epilogue post → whole-program success).
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) c4)
  refine Or.inl ⟨o0, l0, o1, l1, o2, l2, o3, l3, ?_⟩
  refine (sepConj_pure_left h).2 ⟨hDecoded, ?_⟩
  rw [hFdef] at hq
  unfold adSuccessOut
  -- `F` carries `adFoldConstants` at its tail while the post wants it in front of
  -- `adSuccessOut`, so state the split and let `xperm` do the permutation rather
  -- than trying to thread it through the `mono` chain.
  exact sepConj_mono_right (sepConj_mono_right
    (fun h' hF => by
      have hsplit : (adFoldConstants **
          (outputSuccess nonceOut balanceOut rootOut codeOut o0 o1 o2 o3
             l0.toNat l1.toNat l2.toNat l3.toNat bytes oldRoot oldCode **
           bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o3) ** (adLengthAddr ↦ₘ l3) **
           stackFree spW 8 ** adScratch codeOut)) h' := by
        unfold outputSuccess
        rw [← hrootCell, hashCell_of_ne_zero bytes oldCode o3 l3.toNat adEmptyCodeHashBytes
          (by rw [hl3]; decide)]
        xperm_hyp hF
      exact sepConj_mono_right (fun h'' hx => ⟨o3, l3, hx⟩) h' hsplit)) h hq

#print axioms adField3Success

/-! ## Field-3 continue: the success-content tie (`AB+428 → raIn`)

    Field 3's K20 continue exit is the all-fields-decoded success path.  The
    upstream decode facts (fields 0/1/2 `Success` with their length bounds)
    arrive as hypotheses; combined with field 3's own pinned `Success` (from the
    reshape) and the `len = 32` length check they assemble `Decoded`.  The code
    copy loop writes the fourth output cell, then the success tail (`adSuccessEpi`,
    `AB+496 → raIn`) stores `a0 := 0` and returns. -/

set_option maxRecDepth 8000 in
theorem adField3ContEpi
    (sp0 spW raIn listBase len nonceOut balanceOut rootOut codeOut o0 o1 o2 l0 l1 l2 s4reg
      : Word)
    (bytes oldRoot oldCode rootCell : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raIn &&& ~~~(1 : Word) = raIn)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hf1 : Success bytes listBase listLen 1 o1 l1)
    (hf2 : Success bytes listBase listLen 2 o2 l2)
    (hrootCell : rootCell = hashCell bytes oldRoot o2 l2.toNat adEmptyTrieRootBytes)
    (hl0 : l0.toNat ≤ 8) (hl1 : l1.toNat ≤ 32)
    (hl2 : l2.toNat = 32 ∨ l2.toNat = 0) :
    let saved3 : Saved :=
      { ra := AB + 424, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := s4reg, s5 := codeOut }
    let savedCaller : Saved :=
      { ra := raIn, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (5 + 210) (AB + 428) raIn fullCode
      (adK20ContPost spW listBase 3 saved3 bytes listLen **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro saved3 savedCaller
  -- (1) expose the K20 continue existentials, keeping x5/x6/x7 owned.
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ offset len' v11 v12,
      (((⌜Success bytes listBase listLen 3 offset len'⌝ : Assertion) **
        ((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved3) ** stackFree spW 8 **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hcont, hacc⟩ := hp
      unfold adK20ContPost at hcont
      obtain ⟨offset, len', v11, v12, hbody⟩ := hcont
      refine ⟨offset, len', v11, v12, ?_⟩
      have hcomb : (_ ** _) h := ⟨h1, h2, hd, hu, hbody, hacc⟩
      xperm_hyp hcomb)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun offset => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len' => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v11 => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v12 => ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn3 (fun v5 v6 v7 => ?_)
  -- (2) continue reshape into length-check pre plus the ambient continue frame.
  refine cpsTripleWithin_weaken
    (P := (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        (adLengthAddr ↦ₘ len')) **
       (adContFrame spW listBase 3 saved3 bytes listLen offset len' v11 v12 **
        savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
    (fun h hp => by
      have hin : (((⌜Success bytes listBase listLen 3 offset len'⌝ : Assertion) **
          ((((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved3) ** stackFree spW 8) **
           (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
            ((.x7 : Reg) ↦ᵣ v7) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len')))) **
          (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
           bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
           bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
           ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) h := by xperm_hyp hp
      have hout := sepConj_mono_left (adContReshape spW listBase 3 saved3 bytes listLen offset len'
        v11 v12 v5 v6 v7) h hin
      xperm_hyp hout)
    (fun _ hq => hq) ?_
  -- (3) length-check branch, framed by the continue frame plus the output cells.
  have hbr := cpsBranchWithin_frameR
    (adContFrame spW listBase 3 saved3 bytes listLen offset len' v11 v12 **
     savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut))
    (by pcfa) (adCodeLenCheck v5 v6 v7 len')
  refine cpsBranchWithin_merge_same_cr hbr ?fail ?cont
  case fail =>
    -- len ≠ 32: field3Len failure through the shared fail arm.
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (show (1 + 9) ≤ 210 from by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    unfold adContFrame at hp
    rw [regsAt_listNthFrame] at hp
    have hf3 : Success bytes listBase listLen 3 offset len' := by
      obtain ⟨_, _, _, _, _, hr⟩ := hp
      obtain ⟨_, _, _, _, hcf, _⟩ := hr
      exact ((sepConj_pure_left _).1 hcf).1
    have hne32 : len'.toNat ≠ 32 := by
      have hne : len' ≠ (32 : Word) := by
        obtain ⟨_, _, _, _, hfp, _⟩ := hp
        obtain ⟨_, _, _, _, hAgrp, _⟩ := hfp
        obtain ⟨_, _, _, _, _, hA2⟩ := hAgrp
        exact ((sepConj_pure_right _).1 hA2).2
      intro heq; exact hne (by apply BitVec.eq_of_toNat_eq; rw [heq]; decide)
    have hDF : DecodeFailure bytes listBase listLen := DecodeFailure.field3Len offset len' hf3 hne32
    have hgP : ((⌜Success bytes listBase listLen 3 offset len'⌝ : Assertion) **
        (⌜len' ≠ (32 : Word)⌝ : Assertion) **
        ((((.x2 : Reg) ↦ᵣ spW) **
         (((.x1 : Reg) ↦ᵣ (AB + 424)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
          ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
          ((.x20 : Reg) ↦ᵣ saved3.s4) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
         savedFrame spW savedCaller) **
        ((nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
         bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') **
         stackFree spW 8 **
         (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len') ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
          ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x15 : Reg) ↦ᵣ codeOut)))) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) h := by xperm_hyp hp
    have hg := ((sepConj_pure_left h).1 (((sepConj_pure_left h).1 hgP).2)).2
    exact sepConj_mono (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
        listBase len nonceOut balanceOut saved3.s4 codeOut h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
      (fun h' hc => (sepConj_pure_left h').2
        ⟨hDF, beAccum bytes o0.toNat l0.toNat, offset, len', balanceCopied bytes o1 l1.toNat,
          rootCell, oldCode,
          sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (adScratch_of_regs_own codeOut adLengthAddr len' (32 : Word) v11 v12)))))))) h' hc⟩))
      (regIs_implies_regOwn .x10) h hg
  case cont =>
    -- len = 32: the success tie.  Introduce x28/x29 witnesses, extract facts.
    refine cpsTripleWithin_weaken
      (P := ((⌜Success bytes listBase listLen 3 offset len'⌝ : Assertion) **
        (⌜len' = (32 : Word)⌝ : Assertion) **
        ((.x6 : Reg) ↦ᵣ len') ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
        (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 424)) **
        ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
        ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ saved3.s4) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode) **
        regOwn .x28 ** regOwn .x29)
      (fun h hp => by unfold adContFrame at hp; rw [regsAt_listNthFrame] at hp; xperm_hyp hp)
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun x28v x29v => ?_)
    refine cpsTripleWithin_weaken
      (P := (⌜Success bytes listBase listLen 3 offset len'⌝ : Assertion) **
        (⌜len' = (32 : Word)⌝ : Assertion) **
        (((.x6 : Reg) ↦ᵣ len') ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
         (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 424)) **
         ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
         ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ saved3.s4) ** ((.x21 : Reg) ↦ᵣ codeOut) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** ((.x28 : Reg) ↦ᵣ x28v) ** ((.x29 : Reg) ↦ᵣ x29v) **
         regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
         bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode))
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_pure_pre (fun hf3 => ?_)
    refine cpsTripleWithin_pure_pre (fun hl3 => ?_)
    -- `Decoded`'s hash-length clauses are disjunctions post-#11483 (the zero arm is
    -- the `EMPTY_TRIE_ROOT`/`EMPTY_CODE_HASH` fold); this is the exact-32 side.
    have hDecoded : Decoded bytes listBase listLen o0 l0 o1 l1 o2 l2 offset len' :=
      ⟨hf0, hl0, hf1, hl1, hf2, hl2, hf3, Or.inl (by rw [hl3]; decide)⟩
    exact cpsTripleWithin_mono_nSteps (by omega)
      (adField3Success (s4v := saved3.s4) sp0 spW raIn listBase len nonceOut balanceOut rootOut
        codeOut o0 o1 o2 offset l0 l1 l2 len' x28v x29v v11 v12 bytes oldRoot oldCode rootCell
        listLen hspW hret hsalign hslack hover hvalid hcalign hcover hcodelen hcvalid hDecoded
        hrootCell hf3 hl3)

#print axioms adField3ContEpi

/-! ## Field-3 backbone (`AB+392 → raSaved`)

    Merge the field-3 stage's two exits: the parse-fail edge routes through the
    shared `adFailArm` (constructor `DecodeFailure.field3List`), the continue edge
    through `adField3ContEpi` (the success tie).  Both land the whole-program post;
    the four saved slots, the three already-written output cells, the code output
    cell and the live `x15` code pointer are framed ambient across both. -/

set_option maxRecDepth 8000 in
theorem adBBField3
    (sp0 spW raEntry raSaved listBase len nonceOut balanceOut rootOut codeOut s4reg
      oldOffset oldLen v10 v11 v12 v13 v14 o0 o1 o2 l0 l1 l2 : Word)
    (bytes oldRoot oldCode rootCell : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hf1 : Success bytes listBase listLen 1 o1 l1)
    (hf2 : Success bytes listBase listLen 2 o2 l2)
    (hrootCell : rootCell = hashCell bytes oldRoot o2 l2.toNat adEmptyTrieRootBytes)
    (hl0 : l0.toNat ≤ 8) (hl1 : l1.toNat ≤ 32)
    (hl2 : l2.toNat = 32 ∨ l2.toNat = 0) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (((7 + (1 + ((12 + ((85 + 93 * (3 + 2)) + 6)) + 9))) + 1) + 215)
      (AB + 392) raSaved fullCode
      (adCallPre raEntry spW listBase len nonceOut balanceOut s4reg codeOut oldOffset oldLen
        v10 v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hstage := adField3Stage spW raEntry listBase len nonceOut balanceOut s4reg codeOut
    oldOffset oldLen v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hbr := cpsBranchWithin_frameR
    (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)
    (by pcfa) hstage
  refine cpsBranchWithin_merge_same_cr hbr ?fail ?cont
  case cont =>
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (adField3ContEpi sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1 o2
        l0 l1 l2 s4reg bytes oldRoot oldCode rootCell listLen hspW hret hsalign hslack hover hvalid
        hcalign hcover hcodelen hcvalid hf0 hf1 hf2 hrootCell hl0 hl1 hl2)
  case fail =>
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (show (1 + 9) ≤ 215 from by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    obtain ⟨h1, h2, hd, hu, hfail, hacc⟩ := hp
    unfold adK20FailPost at hfail
    obtain ⟨status, offset', len', v11', v12', hbody⟩ := hfail
    have hResPair : Result bytes listBase listLen 3 oldOffset oldLen status offset' len' ∧
        status ≠ (0 : Word) := ((sepConj_pure_left h1).1 hbody).1
    have hFail : Failure bytes listBase listLen 3 := by
      cases hResPair.1 with
      | ok o l hs => exact absurd rfl hResPair.2
      | fail hf => exact hf
    have hDF : DecodeFailure bytes listBase listLen := DecodeFailure.field3List hFail
    have hbig := ((sepConj_pure_left h1).1 hbody).2
    rw [regsAt_listNthFrame] at hbig
    have hgP : (((((.x2 : Reg) ↦ᵣ spW) **
        (((.x1 : Reg) ↦ᵣ (AB + 424)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
         ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
         ((.x20 : Reg) ↦ᵣ s4reg) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
        savedFrame spW savedCaller) **
       (adFoldConstants **
        ((nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (rootCell) ** bytesRegion codeOut oldCode **
        bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset') ** (adLengthAddr ↦ₘ len') **
        stackFree spW 8 **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** ((.x11 : Reg) ↦ᵣ v11') **
         ((.x12 : Reg) ↦ᵣ v12') ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x15 : Reg) ↦ᵣ codeOut))))) ** ((.x10 : Reg) ↦ᵣ status)) h := by
      have hcomb : (_ ** _) h := ⟨h1, h2, hd, hu, hbig, hacc⟩
      xperm_hyp hcomb
    exact sepConj_mono (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
        listBase len nonceOut balanceOut s4reg codeOut h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
      (fun h' hc => (sepConj_pure_left h').2
        ⟨hDF, sepConj_mono_right (fun h'' hx =>
          ⟨beAccum bytes o0.toNat l0.toNat, offset', len', balanceCopied bytes o1 l1.toNat,
           rootCell, oldCode,
           sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
             (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
               (adScratch_of_regs_own2 codeOut v11' v12')))))))) h'' hx⟩) h' hc⟩))
      (regIs_implies_regOwn .x10) h hgP

#print axioms adBBField3

/-! ## Field-2 (storage_root) backbone

    Mirror of the field-3 trio, split one step further (`adField2Copy` +
    `adField2Success` + `adField2ContEpi` + `adBBField2`).  The `len = 32`
    continue edge copies the 32 root bytes into the third output cell and hands
    the register state off to the field-3 backbone `adBBField3`. -/

/-- Introduce FOUR owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn4
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 r4 : Reg} {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, ⟨v4, hv4⟩⟩ := hO3
  exact h v1 v2 v3 v4 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2,
        g6, g7, d4, u4, hv3, hv4⟩, hRb⟩ hpc

/-- Package the regIs→regOwn weakening of the four scratch temporaries
    `x5/x6/x7/x28` into `adCallPre`: the handoff of a field materialiser into the
    next field's call precondition. -/
theorem adCallPre_weaken (raIn spW listBase len s2v s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 v5 v6 v7 v28 : Word) (bytes : List (BitVec 8)) : ∀ h,
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3) **
     ((.x20 : Reg) ↦ᵣ s4) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x10 : Reg) ↦ᵣ v10) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** stackFree spW 8 ** ((.x5 : Reg) ↦ᵣ v5) **
     ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x28 : Reg) ↦ᵣ v28) **
     regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ oldOffset) **
     (adLengthAddr ↦ₘ oldLen)) h →
    adCallPre raIn spW listBase len s2v s3 s4 s5 oldOffset oldLen
      v10 v11 v12 v13 v14 bytes h := by
  intro h hp
  unfold adCallPre
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
        (sepConj_mono (regIs_implies_regOwn .x7)
          (sepConj_mono_left (regIs_implies_regOwn .x28))))))))))))))))))
    h hp

set_option maxRecDepth 8000 in
/-- Field-2 root copy tail (`AB+344 → AB+392`): the 32-byte storage-root copy
    loop plus the two trailing NOPs, reshaping the `len = 32` continue state into
    the field-3 call precondition (`adBBField3`'s `adCallPre`) plus the ambient
    accumulator with the third output cell now written (`fixed32Copied`). -/
theorem adField2Copy
    (spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1 o2 l0 l1
      x28v x29v v11 v12 v13 v14 : Word)
    (bytes oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hf2 : Success bytes listBase listLen 2 o2 l2)
    (hl2 : l2 = (32 : Word)) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (4 + (192 + (1 + 1))) (AB + 344) (AB + 392) fullCode
      (((.x6 : Reg) ↦ᵣ l2) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
       (adLengthAddr ↦ₘ l2) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 320)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
       ((.x28 : Reg) ↦ᵣ x28v) ** ((.x29 : Reg) ↦ᵣ x29v) **
       regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o2) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
       bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
       bytesRegion codeOut oldCode ** bytesRegion rootOut oldRoot ** adFoldConstants)
      (adCallPre (AB + 320) spW listBase len nonceOut balanceOut
        (rootOut + BitVec.ofNat 64 32) codeOut o2 l2 (0 : Word) v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut (fixed32Copied bytes oldRoot o2) ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) := by
  intro savedCaller
  have hoffnorm : listBase + o2 = listBase + BitVec.ofNat 64 (o2.toNat + 0) := by
    rw [Nat.add_zero]; congr 1
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt o2.isLt]
  have hsrcbound : o2.toNat + 0 + (31 + 1) ≤ bytes.length := by
    have hcb := adSuccessContentBound bytes listBase listLen 2 o2 l2 hslack hover hf2
    rw [hl2] at hcb; simp only [show (32 : Word).toNat = 32 from by decide] at hcb; omega
  -- root copy source-cursor setup [86]-[89].
  have hcs := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ l2) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l2) **
     ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 320)) ** ((.x9 : Reg) ↦ᵣ len) **
     ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) **
     ((.x21 : Reg) ↦ᵣ codeOut) ** stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** ((.x29 : Reg) ↦ᵣ x29v) **
     regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller ** bytesRegion listBase bytes **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion codeOut oldCode ** bytesRegion rootOut oldRoot ** adFoldConstants)
    (by pcfa) (adRootCopySetup listBase o2 adLengthAddr x28v)
  -- root copy loop [90]-[95].
  have hcl := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l2) **
     ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 320)) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) **
     ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
     stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
     regOwn .x30 ** regOwn .x31 **
     ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion codeOut oldCode ** (adOffsetAddr ↦ₘ o2) ** adFoldConstants)
    (by pcfa)
    (adCopyLoop .x20 (AB + 360) listBase rootOut x29v bytes oldRoot o2.toNat 0 0 31
      (by decide) adCopyFetchRoot hsalign hralign hsrcbound (by rw [hrootlen])
      hover (by rw [hrootlen]; exact hrover) hvalid
      (by intro k hk; rw [hrootlen] at hk; exact hrvalid k hk))
  -- bridge copysetup → copyloop.
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show (BitVec.ofNat 64 (31 + 1) : Word) = l2 from by rw [hl2]; decide,
        show listBase + BitVec.ofNat 64 (o2.toNat + 0) = listBase + o2 from hoffnorm.symm,
        show rootOut + BitVec.ofNat 64 (0 + 0) = rootOut from by bv_omega,
        show copyIntoRegion oldRoot bytes 0 o2.toNat 0 = oldRoot from rfl]
      xperm_hyp hp)
    hcs hcl
  -- the two trailing NOPs [96]-[97] (`AB+384 → AB+392`).
  have hnop1 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 384) accountDecode_prog 96 .NOP (by bv_omega)
        (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) (nop_spec_within (AB + 384)))
  have hnop2 := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 388) accountDecode_prog 97 .NOP (by bv_omega)
        (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) (nop_spec_within (AB + 388)))
  have hnop1f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o2.toNat + (0 + (31 + 1))))) **
     ((.x20 : Reg) ↦ᵣ (rootOut + BitVec.ofNat 64 (0 + (0 + (31 + 1))))) ** regOwn .x29 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     bytesRegion rootOut (copyIntoRegion oldRoot bytes 0 o2.toNat (0 + (31 + 1))) **
     (.x5 ↦ᵣ adOffsetAddr) ** (.x7 ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l2) ** (.x2 ↦ᵣ spW) **
     (.x1 ↦ᵣ (AB + 320)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ nonceOut) **
     (.x19 ↦ᵣ balanceOut) ** (.x21 ↦ᵣ codeOut) ** stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     regOwn .x30 ** regOwn .x31 **
     (.x15 ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion codeOut oldCode ** (adOffsetAddr ↦ₘ o2) ** adFoldConstants)
    (by pcfa) hnop1
  rw [sepConj_emp_left'] at hnop1f
  have hnop2f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ (0 : Word)) ** ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o2.toNat + (0 + (31 + 1))))) **
     ((.x20 : Reg) ↦ᵣ (rootOut + BitVec.ofNat 64 (0 + (0 + (31 + 1))))) ** regOwn .x29 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
     bytesRegion rootOut (copyIntoRegion oldRoot bytes 0 o2.toNat (0 + (31 + 1))) **
     (.x5 ↦ᵣ adOffsetAddr) ** (.x7 ↦ᵣ (32 : Word)) ** (adLengthAddr ↦ₘ l2) ** (.x2 ↦ᵣ spW) **
     (.x1 ↦ᵣ (AB + 320)) ** (.x8 ↦ᵣ listBase) ** (.x9 ↦ᵣ len) ** (.x18 ↦ᵣ nonceOut) **
     (.x19 ↦ᵣ balanceOut) ** (.x21 ↦ᵣ codeOut) ** stackFree spW 8 ** (.x10 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** (.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14) **
     regOwn .x30 ** regOwn .x31 **
     (.x15 ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion codeOut oldCode ** (adOffsetAddr ↦ₘ o2) ** adFoldConstants)
    (by pcfa) hnop2
  rw [sepConj_emp_left'] at hnop2f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hnop1f
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c2 hnop2f
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) c3)
  rw [show copyIntoRegion oldRoot bytes 0 o2.toNat (0 + (31 + 1))
      = fixed32Copied bytes oldRoot o2 from rfl,
    show (rootOut + BitVec.ofNat 64 (0 + (0 + (31 + 1))) : Word) = rootOut + BitVec.ofNat 64 32
      from by bv_omega] at hq
  exact sepConj_mono_left
    (adCallPre_weaken (AB + 320) spW listBase len nonceOut balanceOut
      (rootOut + BitVec.ofNat 64 32) codeOut o2 l2 (0 : Word) v11 v12 v13 v14
      adOffsetAddr (0 : Word) (32 : Word)
      (listBase + BitVec.ofNat 64 (o2.toNat + (0 + (31 + 1)))) bytes)
    h (by xperm_hyp hq)

#print axioms adField2Copy

set_option maxRecDepth 8000 in
/-- Field-2 success tie (`AB+344 → raSaved`): the root copy (`adField2Copy`)
    followed by the field-3 backbone (`adBBField3`).  Lands the whole-program
    post directly. -/
theorem adField2Success
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1 o2 l0 l1
      x28v x29v v11 v12 v13 v14 : Word)
    (bytes oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hf1 : Success bytes listBase listLen 1 o1 l1)
    (hf2 : Success bytes listBase listLen 2 o2 l2)
    (hl0 : l0.toNat ≤ 8) (hl1 : l1.toNat ≤ 32) (hl2 : l2 = (32 : Word)) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin 999 (AB + 344) raSaved fullCode
      (((.x6 : Reg) ↦ᵣ l2) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
       (adLengthAddr ↦ₘ l2) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 320)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
       ((.x28 : Reg) ↦ᵣ x28v) ** ((.x29 : Reg) ↦ᵣ x29v) **
       regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o2) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
       bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
       bytesRegion codeOut oldCode ** bytesRegion rootOut oldRoot ** adFoldConstants)
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hl2N : l2.toNat = 32 := by rw [hl2]; decide
  have hcopy := adField2Copy spW raSaved listBase len nonceOut balanceOut rootOut codeOut
    o0 o1 o2 l0 l1 x28v x29v v11 v12 v13 v14 bytes oldRoot oldCode listLen
    hsalign hslack hover hvalid hralign hrover hrootlen hrvalid hf2 hl2
  have hbb := adBBField3 sp0 spW (AB + 320) raSaved listBase len nonceOut balanceOut rootOut
    codeOut (rootOut + BitVec.ofNat 64 32) o2 l2 (0 : Word) v11 v12 v13 v14 o0 o1 o2 l0 l1 l2
    bytes oldRoot oldCode (fixed32Copied bytes oldRoot o2) listLen hspW hret hlenW hsalign hslack
    hover hvalid hcalign hcover hcodelen hcvalid hf0 hf1 hf2
    (hashCell_of_ne_zero bytes oldRoot o2 l2.toNat adEmptyTrieRootBytes (by omega)).symm
    hl0 hl1 (Or.inl hl2N)
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcopy hbb)

#print axioms adField2Success

set_option maxRecDepth 8000 in
/-- Field-2 continue (`AB+324 → raSaved`): the storage-root continue edge.  The
    K20 `Success` is pinned; the `len = 32` length check gates the root copy
    (`adField2Success`) or the `field2Len` failure. -/
theorem adField2ContEpi
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1 l0 l1 : Word)
    (bytes oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hf1 : Success bytes listBase listLen 1 o1 l1)
    (hl0 : l0.toNat ≤ 8) (hl1 : l1.toNat ≤ 32) :
    let saved2 : Saved :=
      { ra := AB + 320, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (5 + 999) (AB + 324) raSaved fullCode
      (adK20ContPost spW listBase 2 saved2 bytes listLen **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro saved2 savedCaller
  -- (1) expose the K20 continue existentials, keeping x5/x6/x7 owned.
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ offset len' v11 v12,
      (((⌜Success bytes listBase listLen 2 offset len'⌝ : Assertion) **
        ((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved2) ** stackFree spW 8 **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) h)
    (fun h hp => by
      obtain ⟨h1, h2, hd, hu, hcont, hacc⟩ := hp
      unfold adK20ContPost at hcont
      obtain ⟨offset, len', v11, v12, hbody⟩ := hcont
      refine ⟨offset, len', v11, v12, ?_⟩
      have hcomb : (_ ** _) h := ⟨h1, h2, hd, hu, hbody, hacc⟩
      xperm_hyp hcomb)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_exists_pre_gen (fun offset => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun len' => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v11 => ?_)
  refine cpsTripleWithin_exists_pre_gen (fun v12 => ?_)
  refine cpsTripleWithin_of_forall_regIs_to_regOwn3 (fun v5 v6 v7 => ?_)
  -- (2) continue reshape into length-check pre plus the ambient continue frame.
  refine cpsTripleWithin_weaken
    (P := (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        (adLengthAddr ↦ₘ len')) **
       (adContFrame spW listBase 2 saved2 bytes listLen offset len' v11 v12 **
        savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
    (fun h hp => by
      have hin : (((⌜Success bytes listBase listLen 2 offset len'⌝ : Assertion) **
          ((((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved2) ** stackFree spW 8) **
           (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
            ((.x7 : Reg) ↦ᵣ v7) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len')))) **
          (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
           bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
           bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
           ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) h := by xperm_hyp hp
      have hout := sepConj_mono_left (adContReshape spW listBase 2 saved2 bytes listLen offset len'
        v11 v12 v5 v6 v7) h hin
      xperm_hyp hout)
    (fun _ hq => hq) ?_
  -- (3) length-check branch, framed by the continue frame plus the output cells.
  have hbr := cpsBranchWithin_frameR
    (adContFrame spW listBase 2 saved2 bytes listLen offset len' v11 v12 **
     savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut))
    (by pcfa) (adRootLenCheck v5 v6 v7 len')
  refine cpsBranchWithin_merge_same_cr hbr ?fail ?cont
  case fail =>
    -- len ≠ 32: field2Len failure through the shared fail arm.
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (show (1 + 9) ≤ 999 from by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    unfold adContFrame at hp
    rw [regsAt_listNthFrame] at hp
    have hf2 : Success bytes listBase listLen 2 offset len' := by
      obtain ⟨_, _, _, _, _, hr⟩ := hp
      obtain ⟨_, _, _, _, hcf, _⟩ := hr
      exact ((sepConj_pure_left _).1 hcf).1
    have hne32 : len'.toNat ≠ 32 := by
      have hne : len' ≠ (32 : Word) := by
        obtain ⟨_, _, _, _, hfp, _⟩ := hp
        obtain ⟨_, _, _, _, hAgrp, _⟩ := hfp
        obtain ⟨_, _, _, _, _, hA2⟩ := hAgrp
        exact ((sepConj_pure_right _).1 hA2).2
      intro heq; exact hne (by apply BitVec.eq_of_toNat_eq; rw [heq]; decide)
    have hDF : DecodeFailure bytes listBase listLen := DecodeFailure.field2Len offset len' hf2 hne32
    have hgP : ((⌜Success bytes listBase listLen 2 offset len'⌝ : Assertion) **
        (⌜len' ≠ (32 : Word)⌝ : Assertion) **
        ((((.x2 : Reg) ↦ᵣ spW) **
         (((.x1 : Reg) ↦ᵣ (AB + 320)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
          ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
          ((.x20 : Reg) ↦ᵣ saved2.s4) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
         savedFrame spW savedCaller) **
        ((nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') **
         stackFree spW 8 **
         (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len') ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
          ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x15 : Reg) ↦ᵣ codeOut)))) ** ((.x10 : Reg) ↦ᵣ (0 : Word))) h := by xperm_hyp hp
    have hg := ((sepConj_pure_left h).1 (((sepConj_pure_left h).1 hgP).2)).2
    exact sepConj_mono (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
        listBase len nonceOut balanceOut saved2.s4 codeOut h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
      (fun h' hc => (sepConj_pure_left h').2
        ⟨hDF, beAccum bytes o0.toNat l0.toNat, offset, len', balanceCopied bytes o1 l1.toNat,
          oldRoot, oldCode,
          sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (adScratch_of_regs_own codeOut adLengthAddr len' (32 : Word) v11 v12)))))))) h' hc⟩))
      (regIs_implies_regOwn .x10) h hg
  case cont =>
    -- len = 32: the root-copy success tie.  Introduce x13/x14/x28/x29 witnesses.
    refine cpsTripleWithin_weaken
      (P := ((⌜Success bytes listBase listLen 2 offset len'⌝ : Assertion) **
        (⌜len' = (32 : Word)⌝ : Assertion) **
        ((.x6 : Reg) ↦ᵣ len') ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
        (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 320)) **
        ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
        ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ saved2.s4) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29)
      (fun h hp => by unfold adContFrame at hp; rw [regsAt_listNthFrame] at hp; xperm_hyp hp)
      (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn4 (fun v13 v14 x28v x29v => ?_)
    refine cpsTripleWithin_weaken
      (P := (⌜Success bytes listBase listLen 2 offset len'⌝ : Assertion) **
        (⌜len' = (32 : Word)⌝ : Assertion) **
        (((.x6 : Reg) ↦ᵣ len') ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adLengthAddr) **
         (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 320)) **
         ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
         ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ saved2.s4) ** ((.x21 : Reg) ↦ᵣ codeOut) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
         ((.x28 : Reg) ↦ᵣ x28v) ** ((.x29 : Reg) ↦ᵣ x29v) **
         regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
         bytesRegion codeOut oldCode ** bytesRegion rootOut oldRoot))
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_pure_pre (fun hf2 => ?_)
    refine cpsTripleWithin_pure_pre (fun hl2 => ?_)
    exact adField2Success sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut
      o0 o1 offset l0 l1 x28v x29v v11 v12 v13 v14 bytes oldRoot oldCode listLen hspW hret hlenW
      hsalign hslack hover hvalid hralign hrover hrootlen hrvalid hcalign hcover hcodelen hcvalid
      hf0 hf1 hf2 hl0 hl1 hl2

#print axioms adField2ContEpi

set_option maxRecDepth 8000 in
/-- Field-2 (storage_root) backbone (`AB+288 → raSaved`): merge the field-2
    stage's parse-fail edge (`field2List`) with the continue edge
    (`adField2ContEpi`).  The storage-root output cell is untouched (`oldRoot`)
    on entry. -/
theorem adBBField2
    (sp0 spW raEntry raSaved listBase len nonceOut balanceOut rootOut codeOut
      oldOffset oldLen v10 v11 v12 v13 v14 o0 o1 l0 l1 : Word)
    (bytes oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hf1 : Success bytes listBase listLen 1 o1 l1)
    (hl0 : l0.toNat ≤ 8) (hl1 : l1.toNat ≤ 32) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (((7 + (1 + ((12 + ((85 + 93 * (2 + 2)) + 6)) + 9))) + 1) + 1004)
      (AB + 288) raSaved fullCode
      (adCallPre raEntry spW listBase len nonceOut balanceOut rootOut codeOut oldOffset oldLen
        v10 v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hstage := adField2Stage spW raEntry listBase len nonceOut balanceOut rootOut codeOut
    oldOffset oldLen v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hbr := cpsBranchWithin_frameR
    (savedFrame spW savedCaller ** (nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)
    (by pcfa) hstage
  refine cpsBranchWithin_merge_same_cr hbr ?fail ?cont
  case cont =>
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (adField2ContEpi sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1
        l0 l1 bytes oldRoot oldCode listLen hspW hret hlenW hsalign hslack hover hvalid hralign
        hrover hrootlen hrvalid hcalign hcover hcodelen hcvalid hf0 hf1 hl0 hl1)
  case fail =>
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (show (1 + 9) ≤ 1004 from by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    obtain ⟨h1, h2, hd, hu, hfail, hacc⟩ := hp
    unfold adK20FailPost at hfail
    obtain ⟨status, offset', len', v11', v12', hbody⟩ := hfail
    have hResPair : Result bytes listBase listLen 2 oldOffset oldLen status offset' len' ∧
        status ≠ (0 : Word) := ((sepConj_pure_left h1).1 hbody).1
    have hFail : Failure bytes listBase listLen 2 := by
      cases hResPair.1 with
      | ok o l hs => exact absurd rfl hResPair.2
      | fail hf => exact hf
    have hDF : DecodeFailure bytes listBase listLen := DecodeFailure.field2List hFail
    have hbig := ((sepConj_pure_left h1).1 hbody).2
    rw [regsAt_listNthFrame] at hbig
    have hgP : (((((.x2 : Reg) ↦ᵣ spW) **
        (((.x1 : Reg) ↦ᵣ (AB + 320)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
         ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
         ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
        savedFrame spW savedCaller) **
       (adFoldConstants **
        ((nonceOut ↦ₘ beAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset') ** (adLengthAddr ↦ₘ len') **
        stackFree spW 8 **
        (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** ((.x11 : Reg) ↦ᵣ v11') **
         ((.x12 : Reg) ↦ᵣ v12') ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         ((.x15 : Reg) ↦ᵣ codeOut))))) ** ((.x10 : Reg) ↦ᵣ status)) h := by
      have hcomb : (_ ** _) h := ⟨h1, h2, hd, hu, hbig, hacc⟩
      xperm_hyp hcomb
    exact sepConj_mono (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
        listBase len nonceOut balanceOut rootOut codeOut h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
      (fun h' hc => (sepConj_pure_left h').2
        ⟨hDF, sepConj_mono_right (fun h'' hx =>
          ⟨beAccum bytes o0.toNat l0.toNat, offset', len', balanceCopied bytes o1 l1.toNat,
           oldRoot, oldCode,
           sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
             (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
               (adScratch_of_regs_own2 codeOut v11' v12')))))))) h'' hx⟩) h' hc⟩))
      (regIs_implies_regOwn .x10) h hgP

#print axioms adBBField2

end EvmAsm.Codegen.AccountDecodeSpec
