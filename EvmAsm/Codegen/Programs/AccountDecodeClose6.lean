/-
  `accountDecode_prog` caller-contract composition, part 6 — the field-1
  (balance), field-0 (nonce) backbones and the whole-program close.

  Mirrors the field-2/field-3 trios of `AccountDecodeClose5`.  The balance and
  nonce materialisers differ (right-aligned 32-byte copy / big-endian u64
  accumulate), but the backbone shape (stage merge → length check → materialiser
  handoff) is uniform.  The whole program is `adPrologue ;; adBBField0`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeClose5
import EvmAsm.Rv64.Tactics.ExtractPure

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame savedFrame regsAt_listNthFrame
  listNthFrameRegs_implies_owned Success Result Failure)
open EvmAsm.Evm64.Terminating (copyIntoRegion)

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

/-! ## Extra owned-register introductions and the balance-copy handoff -/

/-- Introduce FIVE owned registers' values at once (trailing `regOwn` chain). -/
theorem cpsTripleWithin_of_forall_regIs_to_regOwn5
    {nSteps : Nat} {entry exit_ : Word} {r1 r2 r3 r4 r5 : Reg} {P Q : Assertion} {cr : CodeReq}
    (h : ∀ v1 v2 v3 v4 v5, cpsTripleWithin nSteps entry exit_ cr
      (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** (r5 ↦ᵣ v5)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** regOwn r5) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨g0, g1, d1, u1, hP0, hO1⟩ := hPP
  obtain ⟨g2, g3, d2, u2, ⟨v1, hv1⟩, hO2⟩ := hO1
  obtain ⟨g4, g5, d3, u3, ⟨v2, hv2⟩, hO3⟩ := hO2
  obtain ⟨g6, g7, d4, u4, ⟨v3, hv3⟩, hO4⟩ := hO3
  obtain ⟨g8, g9, d5, u5, ⟨v4, hv4⟩, ⟨v5, hv5⟩⟩ := hO4
  exact h v1 v2 v3 v4 v5 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨g0, g1, d1, u1, hP0, g2, g3, d2, u2, hv1, g4, g5, d3, u3, hv2,
        g6, g7, d4, u4, hv3, g8, g9, d5, u5, hv4, hv5⟩, hRb⟩ hpc

/-- Variant of `adCallPre_weaken` weakening FIVE concrete scratch temporaries
    `x5/x6/x7/x28/x29` (used after the balance/nonce loops, which leave the
    destination cursor `x29` live). -/
theorem adCallPre_weaken5 (raIn spW listBase len s2v s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 w5 w6 w7 w28 w29 : Word) (bytes : List (BitVec 8)) : ∀ h,
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3) **
     ((.x20 : Reg) ↦ᵣ s4) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x10 : Reg) ↦ᵣ v10) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** stackFree spW 8 ** ((.x5 : Reg) ↦ᵣ w5) **
     ((.x6 : Reg) ↦ᵣ w6) ** ((.x7 : Reg) ↦ᵣ w7) ** ((.x28 : Reg) ↦ᵣ w28) **
     ((.x29 : Reg) ↦ᵣ w29) ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
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
        (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono_left (regIs_implies_regOwn .x29)))))))))))))))))))
    h hp

set_option maxRecDepth 8000 in
/-- Field-1 balance copy tail (`AB+284 → AB+336`): zero cell + right-align setup,
    then forward-copy of the *significant* balance bytes. Entry already has
    `x6 = sigN`, `x28 = sigPtr` from `adBalLenCheck`. -/
theorem adField1Copy
    (spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1 l0
      x29v x30v v11 v12 v13 v14 : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hf1 : Success bytes listBase listLen 1 o1 l1)
    (hl1 : balanceValueOk bytes o1 l1) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let sigN := significantLen (fieldContent bytes o1.toNat l1.toNat)
    let sigO := significantOff bytes o1.toNat l1.toNat
    cpsTripleWithin (6 + (7 * sigN + 1)) (AB + 284) (AB + 336) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sigN) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
       ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
       (adLengthAddr ↦ₘ l1) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 220)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
       ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 sigO)) ** ((.x29 : Reg) ↦ᵣ x29v) **
       ((.x30 : Reg) ↦ᵣ x30v) **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o1) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
       bytesRegion balanceOut oldBal **
       bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants)
      (adCallPre (AB + 220) spW listBase len nonceOut balanceOut rootOut codeOut o1 l1
        (0 : Word) v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut (balanceCopied bytes o1 l1.toNat) **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) := by
  intro savedCaller sigN sigO
  have hbound1 : o1.toNat + l1.toNat ≤ bytes.length := by
    have hcb := adSuccessContentBound bytes listBase listLen 1 o1 l1 hslack hover hf1
    omega
  have hsigEq : sigN = l1.toNat - nlzWin bytes o1.toNat l1.toNat := by
    dsimp only [sigN, fieldContent]
    exact significantLen_eq_nlzWin bytes o1.toNat l1.toNat hbound1
  have hnlzEq : nlzWin bytes o1.toNat l1.toNat =
      numLeadingZerosBE (fieldContent bytes o1.toNat l1.toNat) := by
    dsimp only [fieldContent]
    exact nlzWin_eq_numLeadingZerosBE bytes o1.toNat l1.toNat hbound1
  have hsigOEq : sigO = o1.toNat + nlzWin bytes o1.toNat l1.toNat := by
    dsimp only [sigO, significantOff]; rw [hnlzEq]
  have hsrcbound : sigO + 0 + sigN ≤ bytes.length := by
    rw [hsigOEq, hsigEq]; have := nlzWin_le bytes o1.toNat l1.toNat; omega
  have hsigNle : sigN ≤ 32 := by
    dsimp only [sigN]; exact hl1
  have hdstbound : (32 - sigN) + 0 + sigN ≤ 32 := by omega
  have hsubToNat : ((32 : Word) - BitVec.ofNat 64 sigN).toNat = 32 - sigN := by
    have hs : (BitVec.ofNat 64 sigN).toNat = sigN := by
      rw [BitVec.toNat_ofNat]; omega
    have h32 : (32 : Word).toNat = 32 := by decide
    rw [BitVec.toNat_sub, hs, h32]; omega
  have hdstPtr : balanceOut + BitVec.ofNat 64 ((32 - sigN) + 0) =
      balanceOut + ((32 : Word) - BitVec.ofNat 64 sigN) := by
    apply BitVec.eq_of_toNat_eq
    rw [Nat.add_zero, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hsubToNat]
    omega
  -- 4×SD zero + SUB + ADD right-align
  have hbs := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (AB + 220)) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
     ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
     stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
     ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 sigO)) **
     ((.x30 : Reg) ↦ᵣ x30v) ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     (adLengthAddr ↦ₘ l1) ** (adOffsetAddr ↦ₘ o1) ** adFoldConstants)
    (by pcfa) (adBalanceSetup balanceOut (BitVec.ofNat 64 sigN) x29v
      (packBytes (oldBal.take 8)) (packBytes ((oldBal.drop 8).take 8))
      (packBytes (((oldBal.drop 8).drop 8).take 8))
      (packBytes ((((oldBal.drop 8).drop 8).drop 8).take 8)))
  -- forward copy of significant bytes into right-aligned dest
  have hbl := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** (adLengthAddr ↦ₘ l1) ** ((.x1 : Reg) ↦ᵣ (AB + 220)) **
     ((.x2 : Reg) ↦ᵣ spW) ** ((.x7 : Reg) ↦ᵣ ((32 : Word) - BitVec.ofNat 64 sigN)) **
     ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
     ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) ** stackFree spW 8 **
     ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
     ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) ** regOwn .x31 **
     ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
     (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** (adOffsetAddr ↦ₘ o1) **
     adFoldConstants)
    (by pcfa)
    (adBalLoop listBase balanceOut x30v bytes (List.replicate 32 (0 : BitVec 8))
      sigO (32 - sigN) 0 sigN hsalign hbalign hsrcbound
      (by simp only [List.length_replicate]; exact hdstbound) hover
      (by simp only [List.length_replicate]; exact hbover) hvalid
      (by simp only [List.length_replicate]; exact hbvalid))
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show listBase + BitVec.ofNat 64 (sigO + 0) =
            listBase + BitVec.ofNat 64 sigO from by rw [Nat.add_zero],
        hdstPtr,
        show copyIntoRegion (List.replicate 32 (0 : BitVec 8)) bytes (32 - sigN) sigO 0
          = List.replicate 32 (0 : BitVec 8) from rfl]
      xperm_hyp hp)
    hbs hbl
  refine cpsTripleWithin_weaken (fun h hp => by
      rw [bytesRegion32_dwords_eq balanceOut oldBal hballen] at hp
      xperm_hyp hp)
    (fun h hq => ?_) c1
  have hloop : copyIntoRegion (List.replicate 32 (0 : BitVec 8)) bytes (32 - sigN) sigO
      (0 + sigN) = balanceCopied bytes o1 l1.toNat := by
    rw [Nat.zero_add]
    exact balanceCopied_eq_loop bytes o1 l1.toNat hbound1
  rw [hloop] at hq
  exact sepConj_mono_left
    (adCallPre_weaken5 (AB + 220) spW listBase len nonceOut balanceOut rootOut codeOut o1 l1
      (0 : Word) v11 v12 v13 v14 adOffsetAddr (0 : Word)
      ((32 : Word) - BitVec.ofNat 64 sigN)
      (listBase + BitVec.ofNat 64 (sigO + (0 + sigN)))
      (balanceOut + BitVec.ofNat 64 ((32 - sigN) + (0 + sigN))) bytes)
    h (by xperm_hyp hq)

#print axioms adField1Copy

set_option maxRecDepth 8000 in
/-- Field-1 success tie (`AB+220 → raSaved`): the balance copy (`adField1Copy`)
    followed by the field-2 backbone (`adBBField2`). -/
theorem adField1Success
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 o1 l0
      x29v x30v v11 v12 v13 v14 : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
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
    (hl0 : nonceValueOk bytes o0 l0) (hl1 : balanceValueOk bytes o1 l1) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let sigN := significantLen (fieldContent bytes o1.toNat l1.toNat)
    let sigO := significantOff bytes o1.toNat l1.toNat
    cpsTripleWithin (1508 + 7 * sigN) (AB + 284) raSaved fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sigN) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) **
       ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
       (adLengthAddr ↦ₘ l1) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 220)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
       ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 sigO)) ** ((.x29 : Reg) ↦ᵣ x29v) **
       ((.x30 : Reg) ↦ᵣ x30v) **
       regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o1) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
       bytesRegion balanceOut oldBal **
       bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants)
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller sigN sigO
  have hcopy := adField1Copy spW raSaved listBase len nonceOut balanceOut rootOut codeOut
    o0 o1 l0 x29v x30v v11 v12 v13 v14 bytes oldBal oldRoot oldCode listLen
    hsalign hslack hover hvalid hbalign hbover hballen hbvalid hf1 hl1
  have hbb := adBBField2 sp0 spW (AB + 220) raSaved listBase len nonceOut balanceOut rootOut
    codeOut o1 l1 (0 : Word) v11 v12 v13 v14 o0 o1 l0 l1 bytes oldRoot oldCode listLen hspW hret
    hlenW hsalign hslack hover hvalid hralign hrover hrootlen hrvalid hcalign hcover hcodelen
    hcvalid hf0 hf1 hl0 hl1
  exact cpsTripleWithin_mono_nSteps (by
      dsimp only [sigN]; have := hl1; unfold balanceValueOk at this; omega)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcopy hbb)

#print axioms adField1Success

set_option maxRecDepth 8000 in
/-- Field-1 continue (`AB+200 → raSaved`): the balance continue edge.  The
    `len ≤ 32` length check gates the balance copy (`adField1Success`) or the
    `field1Len` failure. -/
theorem adField1ContEpi
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 l0 : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hl0 : nonceValueOk bytes o0 l0) :
    let saved1 : Saved :=
      { ra := AB + 220, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin ((6 * listLen + 12) + 1732) (AB + 224) raSaved fullCode
      (adK20ContPost spW listBase 1 saved1 bytes listLen **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro saved1 savedCaller
  -- (1) expose the K20 continue existentials, keeping x5/x6/x7 owned.
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ offset len' v11 v12,
      (((⌜Success bytes listBase listLen 1 offset len'⌝ : Assertion) **
        ((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved1) ** stackFree spW 8 **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7) h)
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
       (adContFrame spW listBase 1 saved1 bytes listLen offset len' v11 v12 **
        savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
    (fun h hp => by
      have hin : (((⌜Success bytes listBase listLen 1 offset len'⌝ : Assertion) **
          ((((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved1) ** stackFree spW 8) **
           (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
            ((.x7 : Reg) ↦ᵣ v7) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len')))) **
          (savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
           bytesRegion balanceOut oldBal **
           bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
           ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) h := by xperm_hyp hp
      have hout := sepConj_mono_left (adContReshape spW listBase 1 saved1 bytes listLen offset len'
        v11 v12 v5 v6 v7) h hin
      xperm_hyp hout)
    (fun _ hq => hq) ?_
  -- (3) Expand cont frame; pull len-check atoms into focus; Success pure leftmost.
  refine cpsTripleWithin_weaken
    (P := (⌜Success bytes listBase listLen 1 offset len'⌝ : Assertion) **
        (((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          ((.x8 : Reg) ↦ᵣ listBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (adLengthAddr ↦ₘ len') ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes) **
         ((.x2 : Reg) ↦ᵣ spW) **
         (((.x1 : Reg) ↦ᵣ (AB + 220)) ** ((.x9 : Reg) ↦ᵣ len) **
          ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
          ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants) **
        regOwn .x28 ** regOwn .x29))
    (fun h hp => by
      unfold adContFrame at hp; rw [regsAt_listNthFrame] at hp; xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hf1 => ?_)
  have hbound : offset.toNat + len'.toNat ≤ bytes.length := by
    have hcb := adSuccessContentBound bytes listBase listLen 1 offset len' hslack hover hf1
    omega
  have hoff : listBase.toNat + offset.toNat < 2 ^ 64 := by
    have hcb := adSuccessContentBound bytes listBase listLen 1 offset len' hslack hover hf1
    omega
  -- regOwn x28/x29 already rightmost → introduce values.
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v28 v29 => ?_)
  -- Restore len-check focus on the left.
  refine cpsTripleWithin_weaken
    (P := ((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          ((.x8 : Reg) ↦ᵣ listBase) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (adLengthAddr ↦ₘ len') ** (adOffsetAddr ↦ₘ offset) **
          bytesRegion listBase bytes) **
         ((.x2 : Reg) ↦ᵣ spW) **
         (((.x1 : Reg) ↦ᵣ (AB + 220)) ** ((.x9 : Reg) ↦ᵣ len) **
          ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
          ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  have hbr := cpsBranchWithin_frameR
    (((.x2 : Reg) ↦ᵣ spW) **
     (((.x1 : Reg) ↦ᵣ (AB + 220)) ** ((.x9 : Reg) ↦ᵣ len) **
      ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
      ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
     stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
     savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)
    (by pcfa)
    (adBalLenCheck listBase offset len' bytes v5 v6 v7 v28 v29
      hsalign hbound hover hoff hvalid)
  have hbr_le : 6 * len'.toNat + 12 ≤ 6 * listLen + 12 := by
    have hcb : offset.toNat + len'.toNat ≤ listLen :=
      adSuccessContentBound bytes listBase listLen 1 offset len' hslack hover hf1
    omega
  have hbr' := cpsBranchWithin_mono_nSteps hbr_le hbr
  refine cpsBranchWithin_merge_same_cr hbr' ?fail ?cont
  case fail =>
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    extract_pure_deep hp
    obtain ⟨hult, hp⟩ := hp
    have hn : len'.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (BitVec.isLt len') (by decide)
    have hsig_gt : 32 < len'.toNat - nlzWin bytes offset.toNat len'.toNat :=
      (ad_sigLen_ult32_public bytes offset.toNat len'.toNat hn).mp hult
    have hoven : ¬ balanceValueOk bytes offset len' := by
      intro hok
      have := (ad_balanceValueOk_iff bytes offset len' hbound).mp hok
      omega
    have hDF : DecodeFailure bytes listBase listLen :=
      DecodeFailure.field1Len offset len' hf1 hoven
    have hgP : (((((.x2 : Reg) ↦ᵣ spW) **
        (((.x1 : Reg) ↦ᵣ (AB + 220)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
         ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
         ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
        savedFrame spW savedCaller) **
       (adFoldConstants **
        ((nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') **
         stackFree spW 8 **
         (((.x5 : Reg) ↦ᵣ adOffsetAddr) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
            (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
          ((.x7 : Reg) ↦ᵣ (32 : Word)) **
          ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
            (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x15 : Reg) ↦ᵣ codeOut))))) **
       ((.x10 : Reg) ↦ᵣ (0 : Word))) h := by xperm_hyp hp
    exact sepConj_mono (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
        listBase len nonceOut balanceOut rootOut codeOut h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
      (fun h' hc => (sepConj_pure_left h').2
        ⟨hDF, sepConj_mono_right (fun h'' hx =>
          ⟨nonceAccum bytes o0.toNat l0.toNat, offset, len', oldBal, oldRoot, oldCode,
           sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
             (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
               (adScratch_of_regs_own_x28is codeOut adOffsetAddr
                 (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))
                 (32 : Word) v11 v12
                 (listBase + BitVec.ofNat 64
                   (offset.toNat + nlzWin bytes offset.toNat len'.toNat))))))))))
             h'' hx⟩) h' hc⟩))
      (regIs_implies_regOwn .x10) h hgP
  case cont =>
    -- Match Close5 cont shape: pures + regs, regOwn x13/x14 at outer right first.
    refine cpsTripleWithin_weaken
      (P := ((⌜¬ BitVec.ult (32 : Word)
            (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))⌝ : Assertion) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
          (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
        ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
        (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 220)) **
        ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
        ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) **
        ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
          (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants) **
        regOwn .x13 ** regOwn .x14)
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v13 v14 => ?_)
    refine cpsTripleWithin_weaken
      (P := ((⌜¬ BitVec.ult (32 : Word)
            (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))⌝ : Assertion) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
          (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
        ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
        (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 220)) **
        ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
        ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
        ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
          (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants) **
        regOwn .x29 ** regOwn .x30)
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun x29v x30v => ?_)
    refine cpsTripleWithin_weaken
      (P := (⌜¬ BitVec.ult (32 : Word)
            (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))⌝ : Assertion) **
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
            (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
         ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
         (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 220)) **
         ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
         ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
         ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
           (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
         ((.x29 : Reg) ↦ᵣ x29v) ** ((.x30 : Reg) ↦ᵣ x30v) **
         regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants))
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_pure_pre (fun hult => ?_)
    have hl1 : balanceValueOk bytes offset len' := by
      apply (ad_balanceValueOk_iff bytes offset len' hbound).mpr
      have hn : len'.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (BitVec.isLt len') (by decide)
      set hsig := len'.toNat - nlzWin bytes offset.toNat len'.toNat with hsig_def
      have hsig_le : hsig ≤ len'.toNat := Nat.sub_le _ _
      have hsig_lt : hsig < 2 ^ 64 := Nat.lt_of_le_of_lt hsig_le hn
      have hto : (BitVec.ofNat 64 hsig).toNat = hsig := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsig_lt]
      have h32 : (32 : Word).toNat = 32 := by decide
      -- hult : ¬ BitVec.ult 32 (ofNat hsig)  ⇒  ¬ (32 < hsig)  ⇒  hsig ≤ 32
      simp only [BitVec.ult, hto, h32, decide_eq_true_eq, not_lt] at hult
      exact hult
    have hsigEq : significantLen (fieldContent bytes offset.toNat len'.toNat) =
        len'.toNat - nlzWin bytes offset.toNat len'.toNat := by
      dsimp only [fieldContent]
      exact significantLen_eq_nlzWin bytes offset.toNat len'.toNat hbound
    have hsigOEq : significantOff bytes offset.toNat len'.toNat =
        offset.toNat + nlzWin bytes offset.toNat len'.toNat := by
      unfold significantOff fieldContent
      rw [← nlzWin_eq_numLeadingZerosBE bytes offset.toNat len'.toNat hbound]
    have hS := adField1Success sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut
      o0 offset l0 x29v x30v v11 v12 v13 v14
      bytes oldBal oldRoot oldCode listLen hspW hret hlenW hsalign hslack hover hvalid
      hbalign hbover hballen hbvalid hralign hrover hrootlen hrvalid hcalign hcover hcodelen
      hcvalid hf0 hf1 hl0 hl1
    exact cpsTripleWithin_mono_nSteps (by
        have hle : significantLen (fieldContent bytes offset.toNat len'.toNat) ≤ 32 := hl1
        omega)
      (cpsTripleWithin_weaken
        (fun h hp => by
          have hx6 : BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat) =
              BitVec.ofNat 64 (significantLen (fieldContent bytes offset.toNat len'.toNat)) := by
            rw [hsigEq]
          have hx28 : listBase + BitVec.ofNat 64
                (offset.toNat + nlzWin bytes offset.toNat len'.toNat) =
              listBase + BitVec.ofNat 64 (significantOff bytes offset.toNat len'.toNat) := by
            rw [hsigOEq]
          rw [hx6, hx28] at hp
          xperm_hyp hp)
        (fun _ hq => hq) hS)

#print axioms adField1ContEpi

set_option maxRecDepth 8000 in
/-- Field-1 (balance) backbone (`AB+164 → raSaved`): merge the field-1 stage's
    parse-fail edge (`field1List`) with the continue edge (`adField1ContEpi`).
    The balance output cell is untouched (`oldBal`) on entry. -/
theorem adBBField1
    (sp0 spW raEntry raSaved listBase len nonceOut balanceOut rootOut codeOut
      oldOffset oldLen v10 v11 v12 v13 v14 o0 l0 : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hl0 : nonceValueOk bytes o0 l0) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (((7 + (1 + ((12 + ((85 + 93 * (1 + 2)) + 6)) + 9))) + 1) + ((6 * listLen + 12) + 1732))
      (AB + 188) raSaved fullCode
      (adCallPre raEntry spW listBase len nonceOut balanceOut rootOut codeOut oldOffset oldLen
        v10 v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hstage := adField1Stage spW raEntry listBase len nonceOut balanceOut rootOut codeOut
    oldOffset oldLen v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hbr := cpsBranchWithin_frameR
    (savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
     bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)
    (by pcfa) hstage
  refine cpsBranchWithin_merge_same_cr hbr ?fail ?cont
  case cont =>
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (adField1ContEpi sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 l0
        bytes oldBal oldRoot oldCode listLen hspW hret hlenW hsalign hslack hover hvalid hbalign
        hbover hballen hbvalid hralign hrover hrootlen hrvalid hcalign hcover hcodelen hcvalid
        hf0 hl0)
  case fail =>
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (show (1 + 9) ≤ (6 * listLen + 12) + 1732 from by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    obtain ⟨h1, h2, hd, hu, hfail, hacc⟩ := hp
    unfold adK20FailPost at hfail
    obtain ⟨status, offset', len', v11', v12', hbody⟩ := hfail
    have hResPair : Result bytes listBase listLen 1 oldOffset oldLen status offset' len' ∧
        status ≠ (0 : Word) := ((sepConj_pure_left h1).1 hbody).1
    have hFail : Failure bytes listBase listLen 1 := by
      cases hResPair.1 with
      | ok o l hs => exact absurd rfl hResPair.2
      | fail hf => exact hf
    have hDF : DecodeFailure bytes listBase listLen := DecodeFailure.field1List hFail
    have hbig := ((sepConj_pure_left h1).1 hbody).2
    rw [regsAt_listNthFrame] at hbig
    have hgP : (((((.x2 : Reg) ↦ᵣ spW) **
        (((.x1 : Reg) ↦ᵣ (AB + 220)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
         ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
         ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
        savedFrame spW savedCaller) **
       (adFoldConstants **
       ((nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
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
          ⟨nonceAccum bytes o0.toNat l0.toNat, offset', len', oldBal,
           oldRoot, oldCode,
           sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
             (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
               (adScratch_of_regs_own2 codeOut v11' v12')))))))) h'' hx⟩) h' hc⟩))
      (regIs_implies_regOwn .x10) h hgP

#print axioms adBBField1

/-- Variant of `adCallPre_weaken` weakening THREE concrete scratch temporaries
    `x5/x6/x7` (used after the nonce loop, which leaves `x28/x29` owned). -/
theorem adCallPre_weaken3 (raIn spW listBase len s2v s3 s4 s5 oldOffset oldLen
    v10 v11 v12 v13 v14 w5 w6 w7 : Word) (bytes : List (BitVec 8)) : ∀ h,
    (((.x1 : Reg) ↦ᵣ raIn) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ s2v) ** ((.x19 : Reg) ↦ᵣ s3) **
     ((.x20 : Reg) ↦ᵣ s4) ** ((.x21 : Reg) ↦ᵣ s5) ** ((.x10 : Reg) ↦ᵣ v10) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** stackFree spW 8 ** ((.x5 : Reg) ↦ᵣ w5) **
     ((.x6 : Reg) ↦ᵣ w6) ** ((.x7 : Reg) ↦ᵣ w7) ** regOwn .x28 ** regOwn .x29 **
     regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
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
        (sepConj_mono_left (regIs_implies_regOwn .x7)))))))))))))))))
    h hp

set_option maxRecDepth 8000 in
/-- Field-0 nonce copy tail (`AB+152 → AB+188`): after the value-check continue
    edge, `x6 = sigLen` and `x28 = sigPtr`.  `li x7,0` + big-endian accumulate +
    dword store hand off to field-1 with the nonce cell written (`nonceAccum`). -/
theorem adField0Copy
    (spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 oldNonce
      x29v v11 v12 v13 v14 : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (_hl0 : nonceValueOk bytes o0 l0) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let sigN := significantLen (fieldContent bytes o0.toNat l0.toNat)
    let sigO := significantOff bytes o0.toNat l0.toNat
    cpsTripleWithin (1 + ((7 * sigN + 1) + 1)) (AB + 152) (AB + 188) fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sigN) ** ((.x7 : Reg) ↦ᵣ (8 : Word)) **
       ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
       (adLengthAddr ↦ₘ l0) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 88)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
       ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 sigO)) ** ((.x29 : Reg) ↦ᵣ x29v) **
       regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o0) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
       bytesRegion balanceOut oldBal **
       bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants)
      (adCallPre (AB + 88) spW listBase len nonceOut balanceOut rootOut codeOut o0 l0
        (0 : Word) v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ nonceAccum bytes o0.toNat l0.toNat) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) := by
  intro savedCaller sigN sigO
  have hbound0 : o0.toNat + l0.toNat ≤ bytes.length := by
    have hcb := adSuccessContentBound bytes listBase listLen 0 o0 l0 hslack hover hf0
    omega
  have hsigEq : sigN = l0.toNat - nlzWin bytes o0.toNat l0.toNat := by
    dsimp only [sigN, fieldContent]
    exact significantLen_eq_nlzWin bytes o0.toNat l0.toNat hbound0
  have hnlzEq : nlzWin bytes o0.toNat l0.toNat =
      numLeadingZerosBE (fieldContent bytes o0.toNat l0.toNat) := by
    dsimp only [fieldContent]
    exact nlzWin_eq_numLeadingZerosBE bytes o0.toNat l0.toNat hbound0
  have hsigOEq : sigO = o0.toNat + nlzWin bytes o0.toNat l0.toNat := by
    dsimp only [sigO, significantOff]; rw [hnlzEq]
  have hsrcbound : sigO + 0 + sigN ≤ bytes.length := by
    rw [hsigOEq, hsigEq]; have := nlzWin_le bytes o0.toNat l0.toNat; omega
  -- li x7, 0
  have hns := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sigN) ** (adLengthAddr ↦ₘ l0) ** ((.x2 : Reg) ↦ᵣ spW) **
     ((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
     ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
     stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
     ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 sigO)) ** ((.x29 : Reg) ↦ᵣ x29v) **
     regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o0) ** ((.x15 : Reg) ↦ᵣ codeOut) **
     savedFrame spW savedCaller **
     (nonceOut ↦ₘ oldNonce) ** bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants)
    (by pcfa) (adNonceSetup (8 : Word))
  -- nonce accumulate over significant bytes
  have hnl := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** (adLengthAddr ↦ₘ l0) ** ((.x2 : Reg) ↦ᵣ spW) **
     ((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
     ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) **
     ((.x21 : Reg) ↦ᵣ codeOut) ** stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** regOwn .x30 ** regOwn .x31 ** ((.x15 : Reg) ↦ᵣ codeOut) **
     savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) ** bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** (adOffsetAddr ↦ₘ o0) **
     adFoldConstants)
    (by pcfa) (adNonceLoop listBase bytes sigO sigN 0 x29v hsalign hsrcbound hover hvalid)
  -- nonce store
  have hst := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** (adLengthAddr ↦ₘ l0) ** ((.x2 : Reg) ↦ᵣ spW) **
     ((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
     ((.x6 : Reg) ↦ᵣ (0 : Word)) ** ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) **
     ((.x21 : Reg) ↦ᵣ codeOut) ** stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) **
     ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) **
     ((.x14 : Reg) ↦ᵣ v14) ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes ** ((.x15 : Reg) ↦ᵣ codeOut) **
     savedFrame spW savedCaller ** bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** (adOffsetAddr ↦ₘ o0) **
     adFoldConstants)
    (by pcfa) (adNonceStore nonceOut (beAccum bytes sigO (0 + sigN)) oldNonce)
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show beAccum bytes sigO 0 = (0 : Word) from rfl,
        show listBase + BitVec.ofNat 64 (sigO + 0) = listBase + BitVec.ofNat 64 sigO
          from by rw [Nat.add_zero]]
      xperm_hyp hp)
    hns hnl
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) c1 hst
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) c2)
  have hna : beAccum bytes sigO (0 + sigN) = nonceAccum bytes o0.toNat l0.toNat := by
    rw [Nat.zero_add]
    dsimp only [nonceAccum, significantOff, significantLen, sigO, sigN]
  rw [hna] at hq
  exact sepConj_mono_left
    (adCallPre_weaken3 (AB + 88) spW listBase len nonceOut balanceOut rootOut codeOut o0 l0
      (0 : Word) v11 v12 v13 v14 adOffsetAddr (0 : Word)
      (nonceAccum bytes o0.toNat l0.toNat) bytes)
    h (by xperm_hyp hq)

#print axioms adField0Copy

set_option maxRecDepth 8000 in
/-- Field-0 success tie (`AB+152 → raSaved`): the nonce copy (`adField0Copy`)
    followed by the field-1 backbone (`adBBField1`). -/
theorem adField0Success
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut o0 oldNonce
      x29v v11 v12 v13 v14 : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true)
    (hf0 : Success bytes listBase listLen 0 o0 l0)
    (hl0 : nonceValueOk bytes o0 l0) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let sigN := significantLen (fieldContent bytes o0.toNat l0.toNat)
    let sigO := significantOff bytes o0.toNat l0.toNat
    cpsTripleWithin ((2144 + 7 * sigN) + (6 * listLen + 12)) (AB + 152) raSaved fullCode
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sigN) ** ((.x7 : Reg) ↦ᵣ (8 : Word)) **
       ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
       (adLengthAddr ↦ₘ l0) ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 88)) **
       ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
       ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
       ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
       ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 sigO)) ** ((.x29 : Reg) ↦ᵣ x29v) **
       regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ o0) ** ((.x15 : Reg) ↦ᵣ codeOut) **
       savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
       bytesRegion balanceOut oldBal **
       bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants)
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller sigN sigO
  have hcopy := adField0Copy spW raSaved listBase len nonceOut balanceOut rootOut codeOut
    o0 oldNonce x29v v11 v12 v13 v14 bytes oldBal oldRoot oldCode listLen
    hsalign hslack hover hvalid hf0 hl0
  have hbb := adBBField1 sp0 spW (AB + 88) raSaved listBase len nonceOut balanceOut rootOut
    codeOut o0 l0 (0 : Word) v11 v12 v13 v14 o0 l0 bytes oldBal oldRoot oldCode listLen hspW hret
    hlenW hsalign hslack hover hvalid hbalign hbover hballen hbvalid hralign hrover hrootlen
    hrvalid hcalign hcover hcodelen hcvalid hf0 hl0
  exact cpsTripleWithin_mono_nSteps (by
      dsimp only [sigN]
      have hle : significantLen (fieldContent bytes o0.toNat l0.toNat) ≤ 8 := hl0
      omega)
    (cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hcopy hbb)

#print axioms adField0Success

set_option maxRecDepth 8000 in
/-- Field-0 continue (`AB+92 → raSaved`): the nonce continue edge.  The `len ≤ 8`
    length check gates the nonce copy (`adField0Success`) or the `field0Len`
    failure. -/
theorem adField0ContEpi
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut oldNonce : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true) :
    let saved0 : Saved :=
      { ra := AB + 88, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin ((6 * listLen + 12) + ((2144 + 56) + (6 * listLen + 12))) (AB + 92) raSaved fullCode
      (adK20ContPost spW listBase 0 saved0 bytes listLen **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro saved0 savedCaller
  -- (1) expose the K20 continue existentials, keeping x5/x6/x7 owned.
  refine cpsTripleWithin_weaken
    (P := fun h => ∃ offset len' v11 v12,
      (((⌜Success bytes listBase listLen 0 offset len'⌝ : Assertion) **
        ((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved0) ** stackFree spW 8 **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ oldNonce) ** bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7) h)
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
       (adContFrame spW listBase 0 saved0 bytes listLen offset len' v11 v12 **
        savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
    (fun h hp => by
      have hin : (((⌜Success bytes listBase listLen 0 offset len'⌝ : Assertion) **
          ((((.x2 : Reg) ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved0) ** stackFree spW 8) **
           (((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) **
            ((.x7 : Reg) ↦ᵣ v7) ** ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
            regOwn .x13 ** regOwn .x14 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
            (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len')))) **
          (savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
           bytesRegion balanceOut oldBal **
           bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
           ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)) h := by xperm_hyp hp
      have hout := sepConj_mono_left (adContReshape spW listBase 0 saved0 bytes listLen offset len'
        v11 v12 v5 v6 v7) h hin
      xperm_hyp hout)
    (fun _ hq => hq) ?_
  -- (3) Expand cont frame; pull len-check atoms into focus; Success pure leftmost.
  refine cpsTripleWithin_weaken
    (P := (⌜Success bytes listBase listLen 0 offset len'⌝ : Assertion) **
        (((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          ((.x8 : Reg) ↦ᵣ listBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          (adLengthAddr ↦ₘ len') ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes) **
         ((.x2 : Reg) ↦ᵣ spW) **
         (((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x9 : Reg) ↦ᵣ len) **
          ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
          ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants) **
        regOwn .x28 ** regOwn .x29))
    (fun h hp => by
      unfold adContFrame at hp; rw [regsAt_listNthFrame] at hp; xperm_hyp hp)
    (fun _ hq => hq) ?_
  refine cpsTripleWithin_pure_pre (fun hf0 => ?_)
  have hbound : offset.toNat + len'.toNat ≤ bytes.length := by
    have hcb := adSuccessContentBound bytes listBase listLen 0 offset len' hslack hover hf0
    omega
  have hoff : listBase.toNat + offset.toNat < 2 ^ 64 := by
    have hcb := adSuccessContentBound bytes listBase listLen 0 offset len' hslack hover hf0
    omega
  refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v28 v29 => ?_)
  refine cpsTripleWithin_weaken
    (P := ((((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
          ((.x8 : Reg) ↦ᵣ listBase) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (adLengthAddr ↦ₘ len') ** (adOffsetAddr ↦ₘ offset) **
          bytesRegion listBase bytes) **
         ((.x2 : Reg) ↦ᵣ spW) **
         (((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x9 : Reg) ↦ᵣ len) **
          ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
          ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
    (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  have hbr := cpsBranchWithin_frameR
    (((.x2 : Reg) ↦ᵣ spW) **
     (((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x9 : Reg) ↦ᵣ len) **
      ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
      ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
     stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
     ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 ** regOwn .x30 ** regOwn .x31 **
     savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
     bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)
    (by pcfa)
    (adNonceLenCheck listBase offset len' bytes v5 v6 v7 v28 v29
      hsalign hbound hover hoff hvalid)
  have hbr_le : 6 * len'.toNat + 12 ≤ 6 * listLen + 12 := by
    have hcb : offset.toNat + len'.toNat ≤ listLen :=
      adSuccessContentBound bytes listBase listLen 0 offset len' hslack hover hf0
    omega
  have hbr' := cpsBranchWithin_mono_nSteps hbr_le hbr
  refine cpsBranchWithin_merge_same_cr hbr' ?fail ?cont
  case fail =>
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    extract_pure_deep hp
    obtain ⟨hult, hp⟩ := hp
    have hn : len'.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (BitVec.isLt len') (by decide)
    have hsig_gt : 8 < len'.toNat - nlzWin bytes offset.toNat len'.toNat :=
      (ad_sigLen_ult8_public bytes offset.toNat len'.toNat hn).mp hult
    have hoven : ¬ nonceValueOk bytes offset len' := by
      intro hok
      have := (ad_nonceValueOk_iff bytes offset len' hbound).mp hok
      omega
    have hDF : DecodeFailure bytes listBase listLen :=
      DecodeFailure.field0Len offset len' hf0 hoven
    have hgP : (((((.x2 : Reg) ↦ᵣ spW) **
        (((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
         ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
         ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
        savedFrame spW savedCaller) **
       (adFoldConstants **
        ((nonceOut ↦ₘ oldNonce) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len') **
         stackFree spW 8 **
         (((.x5 : Reg) ↦ᵣ adOffsetAddr) **
          ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
            (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
          ((.x7 : Reg) ↦ᵣ (8 : Word)) **
          ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
          ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
            (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x15 : Reg) ↦ᵣ codeOut))))) **
       ((.x10 : Reg) ↦ᵣ (0 : Word))) h := by xperm_hyp hp
    exact sepConj_mono (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left (fun h' hr => listNthFrameRegs_implies_owned
        listBase len nonceOut balanceOut rootOut codeOut h'
        (sepConj_mono_left (regIs_implies_regOwn .x1) h' hr))))
      (fun h' hc => (sepConj_pure_left h').2
        ⟨hDF, sepConj_mono_right (fun h'' hx =>
          ⟨oldNonce, offset, len', oldBal, oldRoot, oldCode,
           sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
             (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
               (adScratch_of_regs_own_x28is codeOut adOffsetAddr
                 (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))
                 (8 : Word) v11 v12
                 (listBase + BitVec.ofNat 64
                   (offset.toNat + nlzWin bytes offset.toNat len'.toNat))))))))))
             h'' hx⟩) h' hc⟩))
      (regIs_implies_regOwn .x10) h hgP
  case cont =>
    refine cpsTripleWithin_weaken
      (P := ((⌜¬ BitVec.ult (8 : Word)
            (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))⌝ : Assertion) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
          (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
        ((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
        (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 88)) **
        ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
        ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) **
        ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
          (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) ** savedFrame spW savedCaller **
        (nonceOut ↦ₘ oldNonce) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants) **
        regOwn .x13 ** regOwn .x14)
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (fun v13 v14 => ?_)
    -- x30 stays regOwn (Success wants it); introduce only x29
    refine cpsTripleWithin_weaken
      (P := ((⌜¬ BitVec.ult (8 : Word)
            (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))⌝ : Assertion) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
          (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
        ((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
        (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 88)) **
        ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
        ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
        ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
          (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
        regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) **
        savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants) **
        regOwn .x29)
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun x29v => ?_)
    refine cpsTripleWithin_weaken
      (P := (⌜¬ BitVec.ult (8 : Word)
            (BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat))⌝ : Assertion) **
        (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64
            (len'.toNat - nlzWin bytes offset.toNat len'.toNat)) **
         ((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x5 : Reg) ↦ᵣ adOffsetAddr) **
         (adLengthAddr ↦ₘ len') ** ((.x2 : Reg) ↦ᵣ spW) ** ((.x1 : Reg) ↦ᵣ (AB + 88)) **
         ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) ** ((.x18 : Reg) ↦ᵣ nonceOut) **
         ((.x19 : Reg) ↦ᵣ balanceOut) ** ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut) **
         stackFree spW 8 ** ((.x10 : Reg) ↦ᵣ (0 : Word)) ** ((.x11 : Reg) ↦ᵣ v11) **
         ((.x12 : Reg) ↦ᵣ v12) ** ((.x13 : Reg) ↦ᵣ v13) ** ((.x14 : Reg) ↦ᵣ v14) **
         ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64
           (offset.toNat + nlzWin bytes offset.toNat len'.toNat))) **
         ((.x29 : Reg) ↦ᵣ x29v) **
         regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ offset) ** ((.x15 : Reg) ↦ᵣ codeOut) **
         savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
         bytesRegion balanceOut oldBal **
         bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants))
      (fun h hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_pure_pre (fun hult => ?_)
    have hl0' : nonceValueOk bytes offset len' := by
      apply (ad_nonceValueOk_iff bytes offset len' hbound).mpr
      have hn : len'.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (BitVec.isLt len') (by decide)
      set hsig := len'.toNat - nlzWin bytes offset.toNat len'.toNat with hsig_def
      have hsig_le : hsig ≤ len'.toNat := Nat.sub_le _ _
      have hsig_lt : hsig < 2 ^ 64 := Nat.lt_of_le_of_lt hsig_le hn
      have hto : (BitVec.ofNat 64 hsig).toNat = hsig := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsig_lt]
      have h8 : (8 : Word).toNat = 8 := by decide
      simp only [BitVec.ult, hto, h8, decide_eq_true_eq, not_lt] at hult
      exact hult
    have hsigEq : significantLen (fieldContent bytes offset.toNat len'.toNat) =
        len'.toNat - nlzWin bytes offset.toNat len'.toNat := by
      dsimp only [fieldContent]
      exact significantLen_eq_nlzWin bytes offset.toNat len'.toNat hbound
    have hsigOEq : significantOff bytes offset.toNat len'.toNat =
        offset.toNat + nlzWin bytes offset.toNat len'.toNat := by
      unfold significantOff fieldContent
      rw [← nlzWin_eq_numLeadingZerosBE bytes offset.toNat len'.toNat hbound]
    have hS := adField0Success sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut
      offset oldNonce x29v v11 v12 v13 v14 bytes oldBal oldRoot oldCode listLen hspW hret
      hlenW hsalign hslack hover hvalid hbalign hbover hballen hbvalid hralign hrover hrootlen
      hrvalid hcalign hcover hcodelen hcvalid hf0 hl0'
    exact cpsTripleWithin_mono_nSteps (by
        have hle : significantLen (fieldContent bytes offset.toNat len'.toNat) ≤ 8 := hl0'
        omega)
      (cpsTripleWithin_weaken
        (fun h hp => by
          have hx6 : BitVec.ofNat 64 (len'.toNat - nlzWin bytes offset.toNat len'.toNat) =
              BitVec.ofNat 64 (significantLen (fieldContent bytes offset.toNat len'.toNat)) := by
            rw [hsigEq]
          have hx28 : listBase + BitVec.ofNat 64
                (offset.toNat + nlzWin bytes offset.toNat len'.toNat) =
              listBase + BitVec.ofNat 64 (significantOff bytes offset.toNat len'.toNat) := by
            rw [hsigOEq]
          rw [hx6, hx28] at hp
          xperm_hyp hp)
        (fun _ hq => hq) hS)

#print axioms adField0ContEpi

set_option maxRecDepth 8000 in
/-- Field-0 (nonce) backbone (`AB+56 → raSaved`): merge the field-0 stage's
    parse-fail edge (`field0List`) with the continue edge (`adField0ContEpi`).
    All four output cells are untouched on entry. -/
theorem adBBField0
    (sp0 spW raEntry raSaved listBase len nonceOut balanceOut rootOut codeOut
      oldOffset oldLen v10 v11 v12 v13 v14 oldNonce : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (((7 + (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))) + 1) + ((6 * listLen + 12) + ((2144 + 56) + (6 * listLen + 12))))
      (AB + 56) raSaved fullCode
      (adCallPre raEntry spW listBase len nonceOut balanceOut rootOut codeOut oldOffset oldLen
        v10 v11 v12 v13 v14 bytes **
       (savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
        bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
        ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hstage := adField0Stage spW raEntry listBase len nonceOut balanceOut rootOut codeOut
    oldOffset oldLen v10 v11 v12 v13 v14 bytes listLen hlenW hsalign hslack hover hvalid
  have hbr := cpsBranchWithin_frameR
    (savedFrame spW savedCaller ** (nonceOut ↦ₘ oldNonce) **
     bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode **
     ((.x15 : Reg) ↦ᵣ codeOut) ** adFoldConstants)
    (by pcfa) hstage
  refine cpsBranchWithin_merge_same_cr hbr ?fail ?cont
  case cont =>
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun _ hq => hq)
      (adField0ContEpi sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut oldNonce
        bytes oldBal oldRoot oldCode listLen hspW hret hlenW hsalign hslack hover hvalid hbalign
        hbover hballen hbvalid hralign hrover hrootlen hrvalid hcalign hcover hcodelen hcvalid)
  case fail =>
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
      (cpsTripleWithin_mono_nSteps (show (1 + 9) ≤ (6 * listLen + 12) + ((2144 + 56) + (6 * listLen + 12)) from by omega)
        (adFailArm sp0 spW savedCaller listBase bytes oldRoot oldCode listLen hspW
          (show savedCaller.ra &&& ~~~(1 : Word) = savedCaller.ra from hret)))
    obtain ⟨h1, h2, hd, hu, hfail, hacc⟩ := hp
    unfold adK20FailPost at hfail
    obtain ⟨status, offset', len', v11', v12', hbody⟩ := hfail
    have hResPair : Result bytes listBase listLen 0 oldOffset oldLen status offset' len' ∧
        status ≠ (0 : Word) := ((sepConj_pure_left h1).1 hbody).1
    have hFail : Failure bytes listBase listLen 0 := by
      cases hResPair.1 with
      | ok o l hs => exact absurd rfl hResPair.2
      | fail hf => exact hf
    have hDF : DecodeFailure bytes listBase listLen := DecodeFailure.field0List hFail
    have hbig := ((sepConj_pure_left h1).1 hbody).2
    rw [regsAt_listNthFrame] at hbig
    have hgP : (((((.x2 : Reg) ↦ᵣ spW) **
        (((.x1 : Reg) ↦ᵣ (AB + 88)) ** ((.x8 : Reg) ↦ᵣ listBase) ** ((.x9 : Reg) ↦ᵣ len) **
         ((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x19 : Reg) ↦ᵣ balanceOut) **
         ((.x20 : Reg) ↦ᵣ rootOut) ** ((.x21 : Reg) ↦ᵣ codeOut)) **
        savedFrame spW savedCaller) **
       (adFoldConstants **
       ((nonceOut ↦ₘ oldNonce) **
        bytesRegion balanceOut oldBal **
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
          ⟨oldNonce, offset', len', oldBal, oldRoot, oldCode,
           sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
             (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
               (adScratch_of_regs_own2 codeOut v11' v12')))))))) h'' hx⟩) h' hc⟩))
      (regIs_implies_regOwn .x10) h hgP

#print axioms adBBField0

/-! ## Top-level whole-program caller contract (`AB → raSaved`) -/

set_option maxRecDepth 8000 in
/-- **Whole-program caller contract** for `accountDecode_prog`: the ABI prologue
    (`adPrologue`) followed by the four field backbones (`adBBField0`), landing
    the abstract decode outcome `adWholePost`.  On `a0 = 0` the four output cells
    hold the genuine `Decoded` account fields; on `a0 = 1` a `DecodeFailure` is
    witnessed and the owned leftover retained.

    Honest preconditions: the caller passes the RLP pointer/length and the four
    output pointers in the callee-saved registers `x8/x9/x18/x19/x20/x21` (also
    mirrored into the argument registers `a0..a5`), owns the frame slots, the K20
    scratch stack, the seven temporaries, the input region `bytesRegion listBase`,
    the two guest scratch cells and the four output slots (nonce dword +
    balance/root/code 32-byte regions); the buffer fits (`listLen + 9 ≤ length`),
    `listBase`/output alignments, the return-address low-bit invariant, the
    over-bounds and per-byte `isValidByteAccess` facts. -/
theorem account_decode_spec_within
    (sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut oldOffset oldLen oldNonce
      : Word)
    (bytes oldBal oldRoot oldCode : List (BitVec 8)) (listLen : Nat)
    (hspW : spW = sp0 + signExtend12 (-64 : BitVec 12))
    (hret : raSaved &&& ~~~(1 : Word) = raSaved)
    (hlenW : len = BitVec.ofNat 64 listLen)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hbalign : balanceOut.toNat % 8 = 0)
    (hbover : balanceOut.toNat + 32 < 2 ^ 64)
    (hballen : oldBal.length = 32)
    (hbvalid : ∀ k, k < 32 → isValidByteAccess (balanceOut + BitVec.ofNat 64 k) = true)
    (hralign : rootOut.toNat % 8 = 0)
    (hrover : rootOut.toNat + 32 < 2 ^ 64)
    (hrootlen : oldRoot.length = 32)
    (hrvalid : ∀ k, k < 32 → isValidByteAccess (rootOut + BitVec.ofNat 64 k) = true)
    (hcalign : codeOut.toNat % 8 = 0)
    (hcover : codeOut.toNat + 32 < 2 ^ 64)
    (hcodelen : oldCode.length = 32)
    (hcvalid : ∀ k, k < 32 → isValidByteAccess (codeOut + BitVec.ofNat 64 k) = true) :
    let savedCaller : Saved :=
      { ra := raSaved, s0 := listBase, s1 := len, s2 := nonceOut, s3 := balanceOut,
        s4 := rootOut, s5 := codeOut }
    cpsTripleWithin (14 + (((7 + (1 + ((12 + ((85 + 93 * (0 + 2)) + 6)) + 9))) + 1) + ((6 * listLen + 12) + ((2144 + 56) + (6 * listLen + 12)))))
      AB raSaved fullCode
      ((((.x2 : Reg) ↦ᵣ sp0) ** regsAt listNthFrame (savedVals savedCaller) **
       frameSlotsOwn listNthFrame spW **
       (((.x10 : Reg) ↦ᵣ listBase) ** ((.x11 : Reg) ↦ᵣ len) ** ((.x12 : Reg) ↦ᵣ nonceOut) **
        ((.x13 : Reg) ↦ᵣ balanceOut) ** ((.x14 : Reg) ↦ᵣ rootOut) ** ((.x15 : Reg) ↦ᵣ codeOut))) **
       (stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen) **
        (nonceOut ↦ₘ oldNonce) ** bytesRegion balanceOut oldBal **
        bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants))
      (adWholePost sp0 spW savedCaller listBase listLen bytes oldRoot oldCode) := by
  intro savedCaller
  have hpro := adPrologue sp0 spW raSaved listBase len nonceOut balanceOut rootOut codeOut
    listBase len nonceOut balanceOut rootOut codeOut hspW
  have hproF := cpsTripleWithin_frameR
    (stackFree spW 8 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
     regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     bytesRegion listBase bytes ** (adOffsetAddr ↦ₘ oldOffset) ** (adLengthAddr ↦ₘ oldLen) **
     (nonceOut ↦ₘ oldNonce) ** bytesRegion balanceOut oldBal **
     bytesRegion rootOut oldRoot ** bytesRegion codeOut oldCode ** adFoldConstants)
    (by pcfa) hpro
  have hbb := adBBField0 sp0 spW raSaved raSaved listBase len nonceOut balanceOut rootOut codeOut
    oldOffset oldLen listBase len nonceOut balanceOut rootOut oldNonce
    bytes oldBal oldRoot oldCode listLen hspW hret hlenW hsalign hslack hover hvalid hbalign
    hbover hballen hbvalid hralign hrover hrootlen hrvalid hcalign hcover hcodelen hcvalid
  refine cpsTripleWithin_seq_perm_same_cr (fun h hp => ?_) hproF hbb
  unfold adCallPre
  xperm_hyp hp

#print axioms account_decode_spec_within

end EvmAsm.Codegen.AccountDecodeSpec
