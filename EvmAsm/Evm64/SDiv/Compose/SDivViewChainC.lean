/-
  EvmAsm.Evm64.SDiv.Compose.SDivViewChainC

  Shared declaration home for SDIV base, absolute-value, and sign views.
-/

import EvmAsm.Evm64.SDiv.Compose.CodeHandles
import EvmAsm.Evm64.SDiv.Compose.SignCodeSlices
import EvmAsm.Evm64.SDiv.Compose.DividendAbsPre
import EvmAsm.Evm64.SDiv.Compose.DividendAbsPost
import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPre
import EvmAsm.Evm64.SDiv.Compose.SaveRaDividendAbsPost
import EvmAsm.Evm64.SDiv.Compose.BaseSignSequence
import EvmAsm.Evm64.SDiv.Compose.DivisorAbsPost

/-
  EvmAsm.Evm64.SDiv.Compose.BaseCode

  CodeReq handles and sub-block inclusion lemmas for the SDIV wrapper.
-/


namespace EvmAsm.Evm64.SDiv.Compose

/-- Structural slice helper: if dropping `idx` instructions off `full` exposes
    `b` as a prefix, then taking `b.length` recovers `b`. This is the
    kernel-checkable replacement for the `h_slice` argument of
    `CodeReq.ofProg_mono_sub`; the `hdrop` premise is discharged by shallow
    `rfl`/`drop_append_length` reduction rather than enumerating the whole
    390-instruction list. -/
theorem sdivCodeV4_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold dividendAbsCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 5
    (by simp [dividendAbsOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divisorAbsCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 26
    (by simp [divisorAbsOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_signXor_sub {base : Word} :
    ∀ a i, (signXorCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold signXorCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + signXorOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Rv64.XOR' .x8 .x8 .x9) 47
    (by simp [signXorOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
        EvmAsm.Rv64.XOR' EvmAsm.Rv64.single
      simp only [EvmAsm.Rv64.seq, List.length_cons, List.length_nil]; rfl)
    (by
      unfold EvmAsm.Rv64.XOR' EvmAsm.Rv64.single
      rw [EvmAsm.Evm64.evm_sdiv_v4_length]; simp)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divCall_sub {base : Word} :
    ∀ a i, (divCallCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divCallCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divCallOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff) 48
    (by simp [divCallOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_div_call_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold resultSignFixCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold savedRaRetCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by
      apply EvmAsm.Evm64.SDiv.Compose.sdiv_slice_of_drop
      rw [EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_length]
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_sdiv_wrapper
      simp only [EvmAsm.Rv64.seq]; rfl)
    (by
      rw [EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_length, EvmAsm.Evm64.evm_sdiv_v4_length]
      omega)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divCallable_sub {base : Word} :
    ∀ a i, (divCallableCodeV4 base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divCallableCodeV4 sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_div_callable_v4 71
    (by simp [wrapperEndOff])
    (by
      unfold EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Rv64.seq
      rw [← EvmAsm.Evm64.evm_sdiv_wrapper_length]
      have h_drop :
          List.drop EvmAsm.Evm64.evm_sdiv_wrapper.length
              (EvmAsm.Evm64.evm_sdiv_wrapper ++ EvmAsm.Evm64.evm_div_callable_v4) =
            EvmAsm.Evm64.evm_div_callable_v4 := List.drop_append_length
      rw [h_drop]
      simp only [List.take_length])
    (by
      rw [EvmAsm.Evm64.evm_div_callable_v4_length, EvmAsm.Evm64.evm_sdiv_v4_length])
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (signXorCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divCallCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divCallableCodeV4 base) a = some i → (sdivCodeV4 base) a = some i) := by
  exact ⟨sdivCodeV4_saveRa_sub, sdivCodeV4_dividendSign_sub,
    sdivCodeV4_divisorSign_sub, sdivCodeV4_dividendAbs_sub,
    sdivCodeV4_divisorAbs_sub, sdivCodeV4_signXor_sub, sdivCodeV4_divCall_sub,
    sdivCodeV4_resultSignFix_sub, sdivCodeV4_savedRaRet_sub,
    sdivCodeV4_divCallable_sub⟩

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsBlockSpec

  Leaf SDIV wrapper spec for the dividend absolute-value block.
-/


namespace EvmAsm.Evm64.SDiv.Compose

theorem dividendAbs_spec_in_sdivCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (sdivCodeV4 base)
      (dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (dividendAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [dividendAbsPre_unfold, dividendAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsSequence

  SDIV wrapper composition through the dividend absolute-value block.
-/


namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_then_dividendAbs_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 26 base ((base + dividendAbsOff) + 84) (sdivCodeV4 base)
      (saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        divisorTop maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop)
      (saveRaSignsThenDividendAbsPost vRa sp divisorTop
        limb0 limb1 limb2 dividendTop) := by
  rw [saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold]
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let mem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let mem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let mem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let xored0 := limb0 ^^^ mask
  let sum0 := xored0 + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let xored1 := limb1 ^^^ mask
  let sum1 := xored1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let xored2 := limb2 ^^^ mask
  let sum2 := xored2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let xored3 := dividendTop ^^^ mask
  let sum3 := xored3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  let extra : EvmAsm.Rv64.Assertion :=
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
      (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
     ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
  let pre : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
      ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 5 base (base + dividendAbsOff)
      (sdivCodeV4 base) pre mid := by
    dsimp [pre, mid, extra, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc,
      saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
        (by pcFree)
        (saveRa_dividendSign_then_divisorSign_spec_in_sdivCodeV4
          vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop
          base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (sdivCodeV4 base) absPre post := by
    have hSpec := dividendAbs_spec_in_sdivCodeV4
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    rw [dividendAbsPre_unfold, dividendAbsPost_unfold] at hSpec
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
          ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))))
        (by pcFree)
        hSpec
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsSequence

  SDIV wrapper base spec for the divisor absolute-value block.
-/


namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV divisor-abs (conditional 2's-complement
    negation) block. Mirrors `dividendAbsPre` but with the sign in `x9`
    and limb memory cells at the `+32 … +56` divisor slots. Wrapped
    `@[irreducible]` so downstream proofs do not re-unfold the sepConj
    atoms at each use site. -/
@[irreducible]
def divisorAbsPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
  ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
  ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
  ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ limb3)

theorem divisorAbsPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
       ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
       ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
       ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ limb3)) := by
  delta divisorAbsPre
  rfl

/-- Postcondition for the SDIV divisor-abs block: mirrors
    `dividendAbsPost` but with the sign register `x9` and the divisor
    memory slots `+32 … +56`. Wrapped `@[irreducible]` to hide the let
    chain from downstream proofs. -/
@[irreducible]
def divisorAbsPost (sp sign limb0 limb1 limb2 limb3 : Word) : EvmAsm.Rv64.Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ sum0) **
  ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ sum1) **
  ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ sum2) **
  ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ sum3)

theorem divisorAbsPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    divisorAbsPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ sum0) **
       ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ sum1) **
       ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ sum2) **
       ((sp + EvmAsm.Rv64.signExtend12 (56 : BitVec 12)) ↦ₘ sum3)) := by
  delta divisorAbsPost
  rfl

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsBlockSpec

  Leaf SDIV wrapper spec for the divisor absolute-value block.
-/


namespace EvmAsm.Evm64.SDiv.Compose

theorem divisorAbs_spec_in_sdivCodeV4
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (sdivCodeV4 base)
      (divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (divisorAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [divisorAbsPre_unfold, divisorAbsPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x9 .x10 .x7 .x11 32 40 48 56
          (base + divisorAbsOff)) a = some i →
        (sdivCodeV4 base) a = some i := by
    intro a i h
    exact sdivCodeV4_divisorAbs_sub (base := base) a i
      (by simpa [divisorAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact EvmAsm.Rv64.cpsTripleWithin_extend_code hmono hSpec

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.DivisorAbsSequence

  Composed SDIV prefix through the divisor absolute-value block:
  takes the entry shape (saved-`ra` slot + dividend/divisor limbs in
  memory) through dividend-abs, divisor-abs, and emits both operands
  in absolute value with both signs in `x8`/`x9`. Split out from
  `Compose/Base.lean` to respect the per-file line cap on Compose files.
-/


namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics

theorem saveRa_signs_abs_then_divisorAbs_spec_in_sdivCodeV4
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 47 base ((base + divisorAbsOff) + 84) (sdivCodeV4 base)
      (saveRaSignsAbsThenDivisorAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
      (saveRaSignsAbsThenDivisorAbsPost vRa sp
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) := by
  rw [saveRaSignsAbsThenDivisorAbsPre_unfold,
      saveRaSignsAbsThenDivisorAbsPost_unfold]
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendXored0 := dividendLimb0 ^^^ dividendMask
  let dividendSum0 := dividendXored0 + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendXored1 := dividendLimb1 ^^^ dividendMask
  let dividendSum1 := dividendXored1 + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendXored2 := dividendLimb2 ^^^ dividendMask
  let dividendSum2 := dividendXored2 + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendXored3 := dividendTop ^^^ dividendMask
  let dividendSum3 := dividendXored3 + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorXored0 := divisorLimb0 ^^^ divisorMask
  let divisorSum0 := divisorXored0 + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorXored1 := divisorLimb1 ^^^ divisorMask
  let divisorSum1 := divisorXored1 + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorXored2 := divisorLimb2 ^^^ divisorMask
  let divisorSum2 := divisorXored2 + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorXored3 := divisorTop ^^^ divisorMask
  let divisorSum3 := divisorXored3 + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  let dividendCarry3 := if BitVec.ult dividendSum3 dividendCarry2 then (1 : Word) else 0
  let divisorLower : EvmAsm.Rv64.Assertion :=
    ((divisorMem0 ↦ₘ divisorLimb0) ** (divisorMem1 ↦ₘ divisorLimb1) **
     (divisorMem2 ↦ₘ divisorLimb2))
  let pre : EvmAsm.Rv64.Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         (dividendMem3 ↦ₘ dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
      (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       ((dividendMem0 ↦ₘ dividendLimb0) **
        (dividendMem1 ↦ₘ dividendLimb1) **
        (dividendMem2 ↦ₘ dividendLimb2)))) **
     divisorLower)
  let mid : EvmAsm.Rv64.Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
       ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ dividendSign) **
       (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
       (.x11 ↦ᵣ dividendCarry3) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     divisorLower)
  let absPre : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
      (.x11 ↦ᵣ dividendCarry3) **
      (divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2) **
      (divisorMem3 ↦ₘ divisorTop)))
  let post : EvmAsm.Rv64.Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  have hPrefix : EvmAsm.Rv64.cpsTripleWithin 26 base (base + divisorAbsOff)
      (sdivCodeV4 base) pre mid := by
    dsimp [pre, mid, divisorLower, dividendSign, divisorSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, dividendCarry3]
    simpa [dividendAbsOff, divisorAbsOff, BitVec.add_assoc,
      saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold] using
      (EvmAsm.Rv64.cpsTripleWithin_frameR
        ((divisorMem0 ↦ₘ divisorLimb0) **
         (divisorMem1 ↦ₘ divisorLimb1) **
         (divisorMem2 ↦ₘ divisorLimb2))
        (by pcFree)
        (saveRa_signs_then_dividendAbs_spec_in_sdivCodeV4
          vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop base))
  have hAbs : EvmAsm.Rv64.cpsTripleWithin 21 (base + divisorAbsOff)
      ((base + divisorAbsOff) + 84) (sdivCodeV4 base) absPre post := by
    simpa [absPre, post, divisorMem0, divisorMem1, divisorMem2, divisorMem3,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, divisorMask, divisorXored0,
      divisorSum0, divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3, divisorAbsPre_unfold, divisorAbsPost_unfold] using
      EvmAsm.Rv64.cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
          ((.x8 ↦ᵣ dividendSign) **
           (dividendMem0 ↦ₘ dividendSum0) **
           (dividendMem1 ↦ₘ dividendSum1) **
           (dividendMem2 ↦ₘ dividendSum2) **
           (dividendMem3 ↦ₘ dividendSum3))))
        (by pcFree)
        (divisorAbs_spec_in_sdivCodeV4
          sp divisorSign dividendMask dividendSum3 dividendCarry3
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hSeq := EvmAsm.Rv64.cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, divisorLower] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.SignXorPre

  Irreducible precondition for the SDIV prefix through sign-XOR.
-/


namespace EvmAsm.Evm64.SDiv.Compose

/-- Precondition for the SDIV save-ra/signs/dividendAbs/divisorAbs/signXor
    block: identical to the entry shape consumed by the divisorAbs
    sequence. The memory-slot addresses (`dividendMem0..3`, `divisorMem0..3`)
    are computed internally from `sp` so the theorem signature stays flat.
    Wrapped `@[irreducible]` so downstream proofs do not re-reduce the
    18-atom sepConj at each use site. -/
@[irreducible]
def saveRaSignsAbsThenSignXorPre
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
       (dividendMem3 ↦ₘ dividendTop))) **
     ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
      (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
     ((dividendMem0 ↦ₘ dividendLimb0) **
      (dividendMem1 ↦ₘ dividendLimb1) **
      (dividendMem2 ↦ₘ dividendLimb2)))) **
   ((divisorMem0 ↦ₘ divisorLimb0) **
    (divisorMem1 ↦ₘ divisorLimb1) **
    (divisorMem2 ↦ₘ divisorLimb2))

theorem saveRaSignsAbsThenSignXorPre_unfold
    {vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaSignsAbsThenSignXorPre vRa vSavedOld sp sDividendOld sDivisorOld
        dividendMaskOld dividendValueOld dividendCarryOld
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
       let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
       let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
           ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
            (dividendMem3 ↦ₘ dividendTop))) **
          ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
         (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
           (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
          ((dividendMem0 ↦ₘ dividendLimb0) **
           (dividendMem1 ↦ₘ dividendLimb1) **
           (dividendMem2 ↦ₘ dividendLimb2)))) **
        ((divisorMem0 ↦ₘ divisorLimb0) **
         (divisorMem1 ↦ₘ divisorLimb1) **
         (divisorMem2 ↦ₘ divisorLimb2))) := by
  delta saveRaSignsAbsThenSignXorPre
  rfl

end EvmAsm.Evm64.SDiv.Compose

/-
  EvmAsm.Evm64.SDiv.Compose.SignXorPost

  Irreducible postcondition for the SDIV prefix through sign-XOR.
-/


namespace EvmAsm.Evm64.SDiv.Compose

/-- Postcondition for the SDIV save-ra/signs/dividendAbs/divisorAbs/signXor
    block: `x8` holds the result sign (dividendSign ⊕ divisorSign),
    `x9` holds the divisor sign, the rest of the frame matches the
    divisorAbs postcondition. The full ~30-line derived-value let-chain
    (signs, masks, mems, sums, carries) is computed internally so the
    theorem signature stays flat. Wrapped `@[irreducible]`. -/
@[irreducible]
def saveRaSignsAbsThenSignXorPost
    (vRa sp dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmAsm.Rv64.Assertion :=
  let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let resultSign := dividendSign ^^^ divisorSign
  let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
  let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
  let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
  let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
  let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
  let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
  let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let dividendMask := (0 : Word) - dividendSign
  let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
  let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
  let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
  let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
  let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
  let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
  let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
  let divisorMask := (0 : Word) - divisorSign
  let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
  let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
  let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
  let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
  let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
  let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
  let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
  let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
  (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
   (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
    ((dividendMem0 ↦ₘ dividendSum0) **
     (dividendMem1 ↦ₘ dividendSum1) **
     (dividendMem2 ↦ₘ dividendSum2) **
     (dividendMem3 ↦ₘ dividendSum3) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
     (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
     (.x11 ↦ᵣ divisorCarry3) **
     (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
     (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))))

theorem saveRaSignsAbsThenSignXorPost_unfold
    {vRa sp dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaSignsAbsThenSignXorPost vRa sp
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let resultSign := dividendSign ^^^ divisorSign
       let dividendMem0 := sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)
       let dividendMem1 := sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)
       let dividendMem2 := sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)
       let dividendMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem0 := sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)
       let divisorMem1 := sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)
       let divisorMem2 := sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)
       let divisorMem3 := sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       let dividendMask := (0 : Word) - dividendSign
       let dividendSum0 := (dividendLimb0 ^^^ dividendMask) + dividendSign
       let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
       let dividendSum1 := (dividendLimb1 ^^^ dividendMask) + dividendCarry0
       let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
       let dividendSum2 := (dividendLimb2 ^^^ dividendMask) + dividendCarry1
       let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
       let dividendSum3 := (dividendTop ^^^ dividendMask) + dividendCarry2
       let divisorMask := (0 : Word) - divisorSign
       let divisorSum0 := (divisorLimb0 ^^^ divisorMask) + divisorSign
       let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
       let divisorSum1 := (divisorLimb1 ^^^ divisorMask) + divisorCarry0
       let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
       let divisorSum2 := (divisorLimb2 ^^^ divisorMask) + divisorCarry1
       let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
       let divisorSum3 := (divisorTop ^^^ divisorMask) + divisorCarry2
       let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
       (((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign)) **
        (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)))) **
         ((dividendMem0 ↦ₘ dividendSum0) **
          (dividendMem1 ↦ₘ dividendSum1) **
          (dividendMem2 ↦ₘ dividendSum2) **
          (dividendMem3 ↦ₘ dividendSum3) **
          (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) **
          (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
          (.x11 ↦ᵣ divisorCarry3) **
          (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
          (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))))) := by
  delta saveRaSignsAbsThenSignXorPost
  rfl

end EvmAsm.Evm64.SDiv.Compose
