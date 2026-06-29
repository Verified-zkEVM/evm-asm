/-
  EvmAsm.Evm64.AddMod.Pow256Spec

  Composition specs for ADDMOD pow256 helper blocks.
-/

import EvmAsm.Evm64.AddMod.LimbSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev evm_addmod_pow256_prepare_plus_one_mod_args_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_addmod_pow256_prepare_plus_one_mod_args

abbrev evm_addmod_pow256_minus_one_shift_code (base : Word) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_prepare_minus_one_mod_args_code base)
    (CodeReq.singleton (base + 52) (.ADDI .x12 .x12 (64 : BitVec 12)))

/-- Prepare `(-1 mod N)` callable-MOD arguments and point `x12` at the callable window. -/
theorem evm_addmod_pow256_minus_one_shift_spec_within
    (sp base x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word) :
    cpsTripleWithin 14 base (base + 56)
      (evm_addmod_pow256_minus_one_shift_code base)
      (evmAddModPow256PrepareMinusOnePre sp
        x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := by
  have P := evm_addmod_pow256_prepare_minus_one_mod_args_spec_within
    sp base x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3
  have Pp : cpsTripleWithin 13 base (base + 52)
      (evm_addmod_pow256_prepare_minus_one_mod_args_code base)
      (evmAddModPow256PrepareMinusOnePre sp
        x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3)
      ((.x12 ↦ᵣ sp) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) :=
    cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        rw [evmAddModPow256PrepareMinusOnePost_unfold] at hp
        exact hp)
      P
  have A := addi_spec_gen_same_within .x12 sp 64 (base + 52) (by nofun)
  have Af := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3))
    (by pcFree) A
  have h_exit : (base + 52 : Word) + 4 = base + 56 := by bv_omega
  rw [h_exit] at Af
  have Ap : cpsTripleWithin 1 (base + 52) (base + 56)
      (CodeReq.singleton (base + 52) (.ADDI .x12 .x12 (64 : BitVec 12)))
      ((.x12 ↦ᵣ sp) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := Af
  seqFrame Pp Ap


abbrev evm_addmod_pow256_minus_one_first_call_code (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_minus_one_shift_code base)
    (CodeReq.singleton (base + 56) (.JAL .x1 modOff))

abbrev evm_addmod_pow256_minus_one_call_restore_code
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) : CodeReq :=
  (evm_addmod_pow256_minus_one_first_call_code base modOff).union
    (callableCode.union
      (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))

/-- Prepare `(-1 mod N)` callable-MOD arguments, point `x12` at the callable window,
    and jump to the MOD body. -/
theorem evm_addmod_pow256_minus_one_first_call_spec_within
    (sp base x1Old x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word)
    (modOff : BitVec 21) :
    cpsTripleWithin 15 base ((base + 56) + signExtend21 modOff)
      (evm_addmod_pow256_minus_one_first_call_code base modOff)
      ((evmAddModPow256PrepareMinusOnePre sp
          x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3) **
       (.x1 ↦ᵣ x1Old))
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
       (.x1 ↦ᵣ ((base + 56) + 4))) := by
  have S := evm_addmod_pow256_minus_one_shift_spec_within
    sp base x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3
  have Sf := cpsTripleWithin_frameR (.x1 ↦ᵣ x1Old) (by pcFree) S
  have J := jal_spec_within .x1 x1Old modOff (base + 56) (by nofun)
  have Jf := cpsTripleWithin_frameL
    ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
     (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
     ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3))
    (by pcFree) J
  seqFrame Sf Jf


/-- Restore the ADDMOD frame pointer after a pow256 callable-MOD return, preserving
    any PC-free frame. The callable is entered at `sp + 64` and returns with
    `x12 = sp + 96`; this step applies the `-96` immediate. -/
theorem evm_addmod_pow256_call_mod_restore_frame_spec_within
    {F : Assertion} (hF : F.pcFree) (sp base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x12 .x12 (4000 : BitVec 12)))
      ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)
      ((.x12 ↦ᵣ sp) ** F) := by
  have R := evm_addmod_pow256_call_mod_restore_spec_within
    (sp + signExtend12 (96 : BitVec 12)) base
  have h96 : signExtend12 (96 : BitVec 12) = (96 : Word) := by decide
  have h4000 : signExtend12 (4000 : BitVec 12) = (-96 : Word) := by decide
  have h_restore : (sp + signExtend12 (96 : BitVec 12)) + signExtend12 (4000 : BitVec 12) = sp := by
    rw [h96, h4000]
    bv_omega
  rw [h_restore] at R
  exact cpsTripleWithin_frameR F hF R

/-- Compose a pow256 callable-MOD body that returns to the restore instruction
    with the frame-pointer restore step. -/
theorem evm_addmod_pow256_callable_then_restore_frame_spec_within
    {nSteps : Nat} {callableCode : CodeReq} {P F : Assertion}
    (hF : F.pcFree) (sp callableBase restoreBase : Word)
    (hd : callableCode.Disjoint
      (CodeReq.singleton restoreBase (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hCallable : cpsTripleWithin nSteps callableBase restoreBase callableCode P
      ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)) :
    cpsTripleWithin (nSteps + 1) callableBase (restoreBase + 4)
      (callableCode.union
        (CodeReq.singleton restoreBase (.ADDI .x12 .x12 (4000 : BitVec 12))))
      P
      ((.x12 ↦ᵣ sp) ** F) := by
  have R := evm_addmod_pow256_call_mod_restore_frame_spec_within hF sp restoreBase
  exact cpsTripleWithin_seq hd hCallable R

/-- Compose the first pow256 MOD-call setup with an abstract callable body and
    the frame-pointer restore instruction. -/
theorem evm_addmod_pow256_minus_one_call_restore_spec_within
    {nSteps : Nat} {callableCode : CodeReq} {F : Assertion}
    (hF : F.pcFree)
    (sp base x1Old x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 : Word)
    (modOff : BitVec 21)
    (hdEntry : (evm_addmod_pow256_minus_one_first_call_code base modOff).Disjoint
      (callableCode.union
        (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdRestore : callableCode.Disjoint
      (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hCallable : cpsTripleWithin nSteps ((base + 56) + signExtend21 modOff) ((base + 56) + 4)
      callableCode
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
       (.x1 ↦ᵣ ((base + 56) + 4)))
      ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)) :
    cpsTripleWithin (15 + (nSteps + 1)) base (((base + 56) + 4) + 4)
      (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode)
      ((evmAddModPow256PrepareMinusOnePre sp
          x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3) **
       (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ sp) ** F) := by
  have E := evm_addmod_pow256_minus_one_first_call_spec_within
    sp base x1Old x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 modOff
  have R := evm_addmod_pow256_callable_then_restore_frame_spec_within
    hF sp ((base + 56) + signExtend21 modOff) ((base + 56) + 4) hdRestore hCallable
  exact cpsTripleWithin_seq hdEntry E R


/-- Compose the full helper that prepares the second callable MOD arguments for
    materializing `2^256 mod N` from the first `(-1 mod N)` remainder. -/
theorem evm_addmod_pow256_prepare_plus_one_mod_args_spec_within
    (sp base : Word) (x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3 : Word) :
    let sum0 := r0 + signExtend12 (1 : BitVec 12)
    let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
    let sum1 := r1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := r2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := r3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 24 base (base + 96)
      (evm_addmod_pow256_prepare_plus_one_mod_args_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := by
  dsimp only
  let sum0 := r0 + signExtend12 (1 : BitVec 12)
  let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
  let sum1 := r1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := r2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := r3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  have L0 := ld_spec_gen_within .x5 .x12 sp x5Old r0 96 base (by nofun)
  have A0 := addi_spec_gen_within .x6 .x5 x6Old r0 1 (base + 4) (by nofun)
  have C0 := sltiu_spec_gen_within .x7 .x6 x7Old sum0 1 (base + 8) (by nofun)
  have S0 := sd_spec_gen_within .x12 .x6 sp sum0 w0 64 (base + 12)
  have L1 := ld_spec_gen_within .x5 .x12 sp r0 r1 104 (base + 16) (by nofun)
  have A1 := add_spec_gen_within .x6 .x5 .x7 r1 carry0 sum0 (base + 20) (by nofun)
  have C1 := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 sum1 carry0 (base + 24) (by nofun)
  have S1 := sd_spec_gen_within .x12 .x6 sp sum1 w1 72 (base + 28)
  have L2 := ld_spec_gen_within .x5 .x12 sp r1 r2 112 (base + 32) (by nofun)
  have A2 := add_spec_gen_within .x6 .x5 .x7 r2 carry1 sum1 (base + 36) (by nofun)
  have C2 := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 sum2 carry1 (base + 40) (by nofun)
  have S2 := sd_spec_gen_within .x12 .x6 sp sum2 w2 80 (base + 44)
  have L3 := ld_spec_gen_within .x5 .x12 sp r2 r3 120 (base + 48) (by nofun)
  have A3 := add_spec_gen_within .x6 .x5 .x7 r3 carry2 sum2 (base + 52) (by nofun)
  have C3 := sltu_spec_gen_rd_eq_rs2_within .x7 .x6 sum3 carry2 (base + 56) (by nofun)
  have S3 := sd_spec_gen_within .x12 .x6 sp sum3 w3 88 (base + 60)
  have N0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load0_spec_within
    sp r3 (base + 64) n0
  have D0 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy0_spec_within
    sp (base + 68) n0 r0
  have N1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load1_spec_within
    sp (base + 72) n0 n1
  have D1 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy1_spec_within
    sp (base + 76) n1 r1
  have N2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load2_spec_within
    sp (base + 80) n1 n2
  have D2 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy2_spec_within
    sp (base + 84) n2 r2
  have N3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_load3_spec_within
    sp (base + 88) n2 n3
  have D3 := evm_addmod_pow256_prepare_minus_one_mod_args_tail_copy3_spec_within
    sp (base + 92) n3 r3
  simp only [sum0, carry0, sum1, carry1, sum2, carry2, sum3] at *
  runBlock L0 A0 C0 S0 L1 A1 C1 S1 L2 A2 C2 S2 L3 A3 C3 S3 N0 D0 N1 D1 N2 D2 N3 D3


abbrev evm_addmod_pow256_plus_one_shift_code (base : Word) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_prepare_plus_one_mod_args_code base)
    (CodeReq.singleton (base + 96) (.ADDI .x12 .x12 (64 : BitVec 12)))

/-- Prepare `(((-1 mod N) + 1) mod N)` callable-MOD arguments and point `x12`
    at the callable window. -/
theorem evm_addmod_pow256_plus_one_shift_spec_within
    (sp base : Word) (x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3 : Word) :
    let sum0 := r0 + signExtend12 (1 : BitVec 12)
    let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
    let sum1 := r1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := r2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := r3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 25 base (base + 100)
      (evm_addmod_pow256_plus_one_shift_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
       (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := by
  dsimp only
  let sum0 := r0 + signExtend12 (1 : BitVec 12)
  let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
  let sum1 := r1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := r2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := r3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  have P := evm_addmod_pow256_prepare_plus_one_mod_args_spec_within
    sp base x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3
  have A := addi_spec_gen_same_within .x12 sp 64 (base + 96) (by nofun)
  have Af := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
     ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3))
    (by pcFree) A
  have h_exit : (base + 96 : Word) + 4 = base + 100 := by bv_omega
  rw [h_exit] at Af
  have Ap : cpsTripleWithin 1 (base + 96) (base + 100)
      (CodeReq.singleton (base + 96) (.ADDI .x12 .x12 (64 : BitVec 12)))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n3) ** (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3))
      ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
       (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
       ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
       ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
       ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
       ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
       ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) := Af

  seqFrame P Ap

abbrev evm_addmod_pow256_plus_one_first_call_code (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.union (evm_addmod_pow256_plus_one_shift_code base)
    (CodeReq.singleton (base + 100) (.JAL .x1 modOff))

abbrev evm_addmod_pow256_plus_one_call_restore_code
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) : CodeReq :=
  (evm_addmod_pow256_plus_one_first_call_code base modOff).union
    (callableCode.union
      (CodeReq.singleton ((base + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))

/-- Prepare `(((-1 mod N) + 1) mod N)` callable-MOD arguments, point `x12` at
    the callable window, and jump to the MOD body. -/
theorem evm_addmod_pow256_plus_one_first_call_spec_within
    (sp base x1Old : Word)
    (x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3 : Word)
    (modOff : BitVec 21) :
    let sum0 := r0 + signExtend12 (1 : BitVec 12)
    let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
    let sum1 := r1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := r2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := r3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 26 base ((base + 100) + signExtend21 modOff)
      (evm_addmod_pow256_plus_one_first_call_code base modOff)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3)) **
       (.x1 ↦ᵣ x1Old))
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
        (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
       (.x1 ↦ᵣ ((base + 100) + 4))) := by
  dsimp only
  let sum0 := r0 + signExtend12 (1 : BitVec 12)
  let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
  let sum1 := r1 + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := r2 + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := r3 + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  have S := evm_addmod_pow256_plus_one_shift_spec_within
    sp base x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3
  have Sf := cpsTripleWithin_frameR (.x1 ↦ᵣ x1Old) (by pcFree) S
  have J := jal_spec_within .x1 x1Old modOff (base + 100) (by nofun)
  have Jf := cpsTripleWithin_frameL
    ((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
     (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
     ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
     ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
     ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
     ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
     ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
     ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
     ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
     ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
     ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3))
    (by pcFree) J
  seqFrame Sf Jf

/-- Compose the second pow256 MOD-call setup with an abstract callable body and
    the frame-pointer restore instruction. -/
theorem evm_addmod_pow256_plus_one_call_restore_spec_within
    {nSteps : Nat} {callableCode : CodeReq} {F : Assertion}
    (hF : F.pcFree)
    (sp base x1Old : Word)
    (x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3 : Word)
    (modOff : BitVec 21)
    (hdEntry : (evm_addmod_pow256_plus_one_first_call_code base modOff).Disjoint
      (callableCode.union
        (CodeReq.singleton ((base + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdRestore : callableCode.Disjoint
      (CodeReq.singleton ((base + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hCallable :
      let sum0 := r0 + signExtend12 (1 : BitVec 12)
      let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
      let sum1 := r1 + carry0
      let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
      let sum2 := r2 + carry1
      let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
      let sum3 := r3 + carry2
      let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
      cpsTripleWithin nSteps ((base + 100) + signExtend21 modOff) ((base + 100) + 4)
        callableCode
        (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
          (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
          ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
          ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
         (.x1 ↦ᵣ ((base + 100) + 4)))
        ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)) :
    cpsTripleWithin (26 + (nSteps + 1)) base (((base + 100) + 4) + 4)
      (evm_addmod_pow256_plus_one_call_restore_code base modOff callableCode)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3)) **
       (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ sp) ** F) := by
  have E := evm_addmod_pow256_plus_one_first_call_spec_within
    sp base x1Old x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3 modOff
  have R := evm_addmod_pow256_callable_then_restore_frame_spec_within
    hF sp ((base + 100) + signExtend21 modOff) ((base + 100) + 4) hdRestore hCallable
  exact cpsTripleWithin_seq hdEntry E R

abbrev evmAddModPow256PlusOneCallPreFrame (sp x1Old : Word)
    (x5Old x6Old x7Old r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3 : Word) : Assertion :=
  ((.x5 ↦ᵣ x5Old) ** (.x6 ↦ᵣ x6Old) ** (.x7 ↦ᵣ x7Old) **
   ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
   ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
   ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
   ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
   ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ w0) **
   ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ w1) **
   ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ w2) **
   ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ w3) **
   ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ r0) **
   ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ r1) **
   ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ r2) **
   ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ r3)) **
  (.x1 ↦ᵣ x1Old)

abbrev evm_addmod_pow256_two_call_restore_code
    (base : Word) (modOff : BitVec 21) (callableCode1 callableCode2 : CodeReq) : CodeReq :=
  (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode1).union
    (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode2)


abbrev evm_addmod_pow256_mod_n_shared_code
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) : CodeReq :=
  (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode).union
    (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode)


abbrev evm_addmod_pow256_mod_n_with_callable_code
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) : CodeReq :=
  (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).union callableCode

abbrev evm_addmod_pow256_minus_one_local_call_restore_code
    (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.ofProg base
    (evm_addmod_pow256_prepare_minus_one_mod_args ;;
     evm_addmod_pow256_call_mod modOff)

/-- The first local pow256 prepare/call/restore prefix is part of the concrete helper program. -/
theorem evm_addmod_pow256_minus_one_local_call_restore_program_sub
    (base : Word) (modOff : BitVec 21) :
    ∀ a i, (evm_addmod_pow256_minus_one_local_call_restore_code base modOff) a = some i →
      (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)) a = some i := by
  unfold evm_addmod_pow256_minus_one_local_call_restore_code evm_addmod_pow256_mod_n
  exact CodeReq.ofProg_mono_append_left base
    (evm_addmod_pow256_prepare_minus_one_mod_args ;;
     evm_addmod_pow256_call_mod modOff)
    (evm_addmod_pow256_prepare_plus_one_mod_args ;;
     evm_addmod_pow256_call_mod modOff)



abbrev evm_addmod_pow256_plus_one_local_call_restore_code
    (base : Word) (modOff : BitVec 21) : CodeReq :=
  CodeReq.ofProg
    (base + BitVec.ofNat 64 (4 *
      (evm_addmod_pow256_prepare_minus_one_mod_args ;;
       evm_addmod_pow256_call_mod modOff).length))
    (evm_addmod_pow256_prepare_plus_one_mod_args ;;
     evm_addmod_pow256_call_mod modOff)



/-- The second local pow256 prepare/call/restore suffix is part of the concrete helper program. -/
theorem evm_addmod_pow256_plus_one_local_call_restore_program_sub
    (base : Word) (modOff : BitVec 21) :
    ∀ a i, (evm_addmod_pow256_plus_one_local_call_restore_code base modOff) a = some i →
      (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)) a = some i := by
  unfold evm_addmod_pow256_plus_one_local_call_restore_code evm_addmod_pow256_mod_n
  exact CodeReq.ofProg_mono_append_right base
    (evm_addmod_pow256_prepare_minus_one_mod_args ;;
     evm_addmod_pow256_call_mod modOff)
    (evm_addmod_pow256_prepare_plus_one_mod_args ;;
     evm_addmod_pow256_call_mod modOff)
    (by
      have hbound : 4 * (evm_addmod_pow256_mod_n modOff).length < 2^64 := by
        rw [evm_addmod_pow256_mod_n_length]
        decide
      unfold evm_addmod_pow256_mod_n at hbound
      exact hbound)

/-- The concrete pow256 helper program is the left half of the helper+callable code. -/
theorem evm_addmod_pow256_mod_n_program_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) :
    ∀ a i, (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)) a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_mod_n_with_callable_code
  exact CodeReq.union_mono_left

/-- The callable body is the right half of the helper+callable code. -/
theorem evm_addmod_pow256_mod_n_callable_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode) :
    ∀ a i, callableCode a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_mod_n_with_callable_code
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

abbrev evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) : CodeReq :=
  (evm_addmod_pow256_minus_one_local_call_restore_code base modOff).union callableCode

/-- The first local pow256 helper segment plus callable body is subsumed by the
    concrete helper+callable code region. -/
theorem evm_addmod_pow256_minus_one_local_call_restore_with_callable_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode) :
    ∀ a i, (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
        base modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
  exact CodeReq.union_sub
    (fun a i h => evm_addmod_pow256_mod_n_program_sub base modOff callableCode a i
      (evm_addmod_pow256_minus_one_local_call_restore_program_sub base modOff a i h))
    (evm_addmod_pow256_mod_n_callable_sub base modOff callableCode hd)

abbrev evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) : CodeReq :=
  (evm_addmod_pow256_plus_one_local_call_restore_code base modOff).union callableCode

/-- The second local pow256 helper segment plus callable body is subsumed by the
    concrete helper+callable code region. -/
theorem evm_addmod_pow256_plus_one_local_call_restore_with_callable_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode) :
    ∀ a i, (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
        base modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
  exact CodeReq.union_sub
    (fun a i h => evm_addmod_pow256_mod_n_program_sub base modOff callableCode a i
      (evm_addmod_pow256_plus_one_local_call_restore_program_sub base modOff a i h))
    (evm_addmod_pow256_mod_n_callable_sub base modOff callableCode hd)

/-- First pow256 call/restore block is the left half of the shared helper code. -/
theorem evm_addmod_pow256_mod_n_shared_code_first_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq) :
    ∀ a i, (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_shared_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_mod_n_shared_code
  exact CodeReq.union_mono_left

/-- Second pow256 call/restore block is the right half of the shared helper code. -/
theorem evm_addmod_pow256_mod_n_shared_code_second_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode).Disjoint
      (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode)) :
    ∀ a i, (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_shared_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_mod_n_shared_code
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Compose both pow256 callable-MOD calls and their frame-pointer restore steps.
    The concrete MOD bodies remain abstract hypotheses. -/
theorem evm_addmod_pow256_two_call_restore_spec_within
    {nSteps1 nSteps2 : Nat} {callableCode1 callableCode2 : CodeReq} {F : Assertion}
    (hF : F.pcFree)
    (sp base x1Old x1Mid x5Old x5Mid x6Mid x7Mid : Word)
    (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 r0 r1 r2 r3 : Word)
    (modOff : BitVec 21)
    (hdFirstEntry : (evm_addmod_pow256_minus_one_first_call_code base modOff).Disjoint
      (callableCode1.union
        (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdFirstRestore : callableCode1.Disjoint
      (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hdSecondEntry : (evm_addmod_pow256_plus_one_first_call_code (base + 64) modOff).Disjoint
      (callableCode2.union
        (CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdSecondRestore : callableCode2.Disjoint
      (CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hdSeq : (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode1).Disjoint
      (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode2))
    (hCallable1 : cpsTripleWithin nSteps1 ((base + 56) + signExtend21 modOff) ((base + 56) + 4)
      callableCode1
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
       (.x1 ↦ᵣ ((base + 56) + 4)))
      ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) **
       evmAddModPow256PlusOneCallPreFrame sp x1Mid
        x5Mid x6Mid x7Mid r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3))
    (hCallable2 :
      let sum0 := r0 + signExtend12 (1 : BitVec 12)
      let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
      let sum1 := r1 + carry0
      let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
      let sum2 := r2 + carry1
      let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
      let sum3 := r3 + carry2
      let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
      cpsTripleWithin nSteps2 (((base + 64) + 100) + signExtend21 modOff) (((base + 64) + 100) + 4)
        callableCode2
        (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
          (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
          ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
          ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
         (.x1 ↦ᵣ (((base + 64) + 100) + 4)))
        ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)) :
    cpsTripleWithin ((15 + (nSteps1 + 1)) + (26 + (nSteps2 + 1)))
      base ((((base + 64) + 100) + 4) + 4)
      (evm_addmod_pow256_two_call_restore_code base modOff callableCode1 callableCode2)
      ((evmAddModPow256PrepareMinusOnePre sp
          x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3) **
       (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ sp) ** F) := by
  have H1 := evm_addmod_pow256_minus_one_call_restore_spec_within
    (by pcFree) sp base x1Old x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3
    modOff hdFirstEntry hdFirstRestore hCallable1
  have H2 := evm_addmod_pow256_plus_one_call_restore_spec_within
    hF sp (base + 64) x1Mid x5Mid x6Mid x7Mid r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3
    modOff hdSecondEntry hdSecondRestore hCallable2
  have h_mid : (base + 56 : Word) + 4 + 4 = base + 64 := by bv_omega
  rw [h_mid] at H1
  exact cpsTripleWithin_seq_with_perm hdSeq (fun h hp => by
    dsimp only [evmAddModPow256PlusOneCallPreFrame] at hp
    exact (sepConj_assoc h).mpr hp) H1 H2

/-- Compose both pow256 callable-MOD calls over a shared code region.
    This is the shape needed when both calls reuse the same callable MOD body:
    callers only need to show each local call/restore block is subsumed by the
    shared `CodeReq`. -/
theorem evm_addmod_pow256_two_call_restore_shared_code_spec_within
    {nSteps1 nSteps2 : Nat} {callableCode sharedCode : CodeReq} {F : Assertion}
    (hF : F.pcFree)
    (sp base x1Old x1Mid x5Old x5Mid x6Mid x7Mid : Word)
    (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 r0 r1 r2 r3 : Word)
    (modOff : BitVec 21)
    (hmonoFirst : ∀ a i,
      (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode) a = some i →
        sharedCode a = some i)
    (hmonoSecond : ∀ a i,
      (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode) a = some i →
        sharedCode a = some i)
    (hdFirstEntry : (evm_addmod_pow256_minus_one_first_call_code base modOff).Disjoint
      (callableCode.union
        (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdFirstRestore : callableCode.Disjoint
      (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hdSecondEntry : (evm_addmod_pow256_plus_one_first_call_code (base + 64) modOff).Disjoint
      (callableCode.union
        (CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdSecondRestore : callableCode.Disjoint
      (CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hCallable1 : cpsTripleWithin nSteps1 ((base + 56) + signExtend21 modOff) ((base + 56) + 4)
      callableCode
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
       (.x1 ↦ᵣ ((base + 56) + 4)))
      ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) **
       evmAddModPow256PlusOneCallPreFrame sp x1Mid
        x5Mid x6Mid x7Mid r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3))
    (hCallable2 :
      let sum0 := r0 + signExtend12 (1 : BitVec 12)
      let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
      let sum1 := r1 + carry0
      let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
      let sum2 := r2 + carry1
      let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
      let sum3 := r3 + carry2
      let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
      cpsTripleWithin nSteps2 (((base + 64) + 100) + signExtend21 modOff) (((base + 64) + 100) + 4)
        callableCode
        (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
          (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
          ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
          ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
         (.x1 ↦ᵣ (((base + 64) + 100) + 4)))
        ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)) :
    cpsTripleWithin ((15 + (nSteps1 + 1)) + (26 + (nSteps2 + 1)))
      base ((((base + 64) + 100) + 4) + 4)
      sharedCode
      ((evmAddModPow256PrepareMinusOnePre sp
          x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3) **
       (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ sp) ** F) := by
  have H1 := evm_addmod_pow256_minus_one_call_restore_spec_within
    (by pcFree) sp base x1Old x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3
    modOff hdFirstEntry hdFirstRestore hCallable1
  have H2 := evm_addmod_pow256_plus_one_call_restore_spec_within
    hF sp (base + 64) x1Mid x5Mid x6Mid x7Mid r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3
    modOff hdSecondEntry hdSecondRestore hCallable2
  have H1e := cpsTripleWithin_extend_code hmonoFirst H1
  have H2e := cpsTripleWithin_extend_code hmonoSecond H2
  have h_mid : (base + 56 : Word) + 4 + 4 = base + 64 := by bv_omega
  rw [h_mid] at H1e
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => by
    dsimp only [evmAddModPow256PlusOneCallPreFrame] at hp
    exact (sepConj_assoc h).mpr hp) H1e H2e

/-- Compose both pow256 callable-MOD calls over the named shared helper code. -/
theorem evm_addmod_pow256_mod_n_shared_code_spec_within
    {nSteps1 nSteps2 : Nat} {callableCode : CodeReq} {F : Assertion}
    (hF : F.pcFree)
    (sp base x1Old x1Mid x5Old x5Mid x6Mid x7Mid : Word)
    (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 r0 r1 r2 r3 : Word)
    (modOff : BitVec 21)
    (hdSeq : (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode).Disjoint
      (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode))
    (hdFirstEntry : (evm_addmod_pow256_minus_one_first_call_code base modOff).Disjoint
      (callableCode.union
        (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdFirstRestore : callableCode.Disjoint
      (CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hdSecondEntry : (evm_addmod_pow256_plus_one_first_call_code (base + 64) modOff).Disjoint
      (callableCode.union
        (CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)))))
    (hdSecondRestore : callableCode.Disjoint
      (CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12))))
    (hCallable1 : cpsTripleWithin nSteps1 ((base + 56) + signExtend21 modOff) ((base + 56) + 4)
      callableCode
      (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ n3) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
        ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ signExtend12 (4095 : BitVec 12)) **
        ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
        ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
        ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
        ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
       (.x1 ↦ᵣ ((base + 56) + 4)))
      ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) **
       evmAddModPow256PlusOneCallPreFrame sp x1Mid
        x5Mid x6Mid x7Mid r0 r1 r2 r3 n0 n1 n2 n3 w0 w1 w2 w3))
    (hCallable2 :
      let sum0 := r0 + signExtend12 (1 : BitVec 12)
      let carry0 := if BitVec.ult sum0 (signExtend12 (1 : BitVec 12)) then (1 : Word) else 0
      let sum1 := r1 + carry0
      let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
      let sum2 := r2 + carry1
      let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
      let sum3 := r3 + carry2
      let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
      cpsTripleWithin nSteps2 (((base + 64) + 100) + signExtend21 modOff) (((base + 64) + 100) + 4)
        callableCode
        (((.x12 ↦ᵣ (sp + signExtend12 (64 : BitVec 12))) ** (.x5 ↦ᵣ n3) **
          (.x6 ↦ᵣ sum3) ** (.x7 ↦ᵣ carry3) **
          ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ n3) **
          ((sp + signExtend12 (64 : BitVec 12)) ↦ₘ sum0) **
          ((sp + signExtend12 (72 : BitVec 12)) ↦ₘ sum1) **
          ((sp + signExtend12 (80 : BitVec 12)) ↦ₘ sum2) **
          ((sp + signExtend12 (88 : BitVec 12)) ↦ₘ sum3) **
          ((sp + signExtend12 (96 : BitVec 12)) ↦ₘ n0) **
          ((sp + signExtend12 (104 : BitVec 12)) ↦ₘ n1) **
          ((sp + signExtend12 (112 : BitVec 12)) ↦ₘ n2) **
          ((sp + signExtend12 (120 : BitVec 12)) ↦ₘ n3)) **
         (.x1 ↦ᵣ (((base + 64) + 100) + 4)))
        ((.x12 ↦ᵣ (sp + signExtend12 (96 : BitVec 12))) ** F)) :
    cpsTripleWithin ((15 + (nSteps1 + 1)) + (26 + (nSteps2 + 1)))
      base ((((base + 64) + 100) + 4) + 4)
      (evm_addmod_pow256_mod_n_shared_code base modOff callableCode)
      ((evmAddModPow256PrepareMinusOnePre sp
          x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3) **
       (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ sp) ** F) := by
  exact evm_addmod_pow256_two_call_restore_shared_code_spec_within hF
    sp base x1Old x1Mid x5Old x5Mid x6Mid x7Mid
    n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 r0 r1 r2 r3 modOff
    (evm_addmod_pow256_mod_n_shared_code_first_sub base modOff callableCode)
    (evm_addmod_pow256_mod_n_shared_code_second_sub base modOff callableCode hdSeq)
    hdFirstEntry hdFirstRestore hdSecondEntry hdSecondRestore hCallable1 hCallable2

end EvmAsm.Evm64
