/-
  EvmAsm.Evm64.AddMod.Pow256CodeBridge

  CodeReq subsumption bridges from composed pow256 call/restore code into the
  concrete ADDMOD pow256 helper program plus callable body.
-/

import EvmAsm.Evm64.AddMod.Pow256Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The first composed pow256 call/restore code is subsumed by the concrete
    helper program plus callable body. -/
theorem evm_addmod_pow256_minus_one_call_restore_with_callable_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode) :
    ∀ a i, (evm_addmod_pow256_minus_one_call_restore_code base modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  have hLocalProgram :
      ∀ a i, (evm_addmod_pow256_minus_one_local_call_restore_code base modOff) a = some i →
        (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)) a = some i :=
    evm_addmod_pow256_minus_one_local_call_restore_program_sub base modOff
  have hLocal : ∀ a i,
      CodeReq.ofProg base
          (evm_addmod_pow256_prepare_minus_one_mod_args ;;
           evm_addmod_pow256_call_mod modOff) a = some i →
        (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    unfold evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
    apply CodeReq.union_mono_left
    unfold evm_addmod_pow256_minus_one_local_call_restore_code
    exact h
  have hPrep : ∀ a i,
      (evm_addmod_pow256_prepare_minus_one_mod_args_code base) a = some i →
        (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    change CodeReq.ofProg base evm_addmod_pow256_prepare_minus_one_mod_args a = some i at h
    exact CodeReq.ofProg_mono_append_left base
      evm_addmod_pow256_prepare_minus_one_mod_args
      (evm_addmod_pow256_call_mod modOff) a i h
  have hEnter : ∀ a i,
      CodeReq.singleton (base + 52) (.ADDI .x12 .x12 (64 : BitVec 12)) a = some i →
        (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    exact CodeReq.singleton_mono (by
      have hlookup := CodeReq.ofProg_lookup_addr base
        (evm_addmod_pow256_prepare_minus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff) 13 (base + 52)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_minus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_minus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by bv_omega)
      simpa [seq, evm_addmod_pow256_call_mod,
        evm_addmod_pow256_prepare_minus_one_mod_args_length] using hlookup) a i h
  have hJal : ∀ a i,
      CodeReq.singleton (base + 56) (.JAL .x1 modOff) a = some i →
        (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    exact CodeReq.singleton_mono (by
      have hlookup := CodeReq.ofProg_lookup_addr base
        (evm_addmod_pow256_prepare_minus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff) 14 (base + 56)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_minus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_minus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by bv_omega)
      simpa [seq, evm_addmod_pow256_call_mod,
        evm_addmod_pow256_prepare_minus_one_mod_args_length] using hlookup) a i h
  have hRestore : ∀ a i,
      CodeReq.singleton ((base + 56) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)) a = some i →
        (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    exact CodeReq.singleton_mono (by
      have hlookup := CodeReq.ofProg_lookup_addr base
        (evm_addmod_pow256_prepare_minus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff) 15 ((base + 56) + 4)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_minus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_minus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by bv_omega)
      simpa [seq, evm_addmod_pow256_call_mod,
        evm_addmod_pow256_prepare_minus_one_mod_args_length] using hlookup) a i h
  have hdLocal : (evm_addmod_pow256_minus_one_local_call_restore_code base modOff).Disjoint
      callableCode := by
    intro a
    rcases hd a with h_full | h_callable
    · left
      cases h_local : evm_addmod_pow256_minus_one_local_call_restore_code base modOff a with
      | none => rfl
      | some instr =>
          have h_hit := hLocalProgram a instr h_local
          rw [h_full] at h_hit
          contradiction
    · right
      exact h_callable
  have hCallable : ∀ a i, callableCode a = some i →
      (evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
        base modOff callableCode) a = some i := by
    unfold evm_addmod_pow256_minus_one_local_call_restore_with_callable_code
    exact CodeReq.mono_union_right hdLocal (fun _ _ h => h)
  intro a i h
  apply evm_addmod_pow256_minus_one_local_call_restore_with_callable_sub base modOff callableCode hd
  unfold evm_addmod_pow256_minus_one_call_restore_code
    evm_addmod_pow256_minus_one_first_call_code
    evm_addmod_pow256_minus_one_shift_code at h
  exact CodeReq.union_sub
    (CodeReq.union_sub (CodeReq.union_sub hPrep hEnter) hJal)
    (CodeReq.union_sub hCallable hRestore) a i h

/-- The second composed pow256 call/restore code is subsumed by the concrete
    helper program plus callable body. -/
theorem evm_addmod_pow256_plus_one_call_restore_with_callable_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode) :
    ∀ a i, (evm_addmod_pow256_plus_one_call_restore_code (base + 64) modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  have hLocalProgram :
      ∀ a i, (evm_addmod_pow256_plus_one_local_call_restore_code base modOff) a = some i →
        (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)) a = some i :=
    evm_addmod_pow256_plus_one_local_call_restore_program_sub base modOff
  have hSecondBase :
      base + BitVec.ofNat 64 (4 *
        (evm_addmod_pow256_prepare_minus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff).length) = base + 64 := by
    simp only [seq, Program.length_append,
      evm_addmod_pow256_prepare_minus_one_mod_args_length,
      evm_addmod_pow256_call_mod_length]
    bv_omega
  have hLocal : ∀ a i,
      CodeReq.ofProg (base + 64)
          (evm_addmod_pow256_prepare_plus_one_mod_args ;;
           evm_addmod_pow256_call_mod modOff) a = some i →
        (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    unfold evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
    apply CodeReq.union_mono_left
    unfold evm_addmod_pow256_plus_one_local_call_restore_code
    rw [hSecondBase]
    exact h
  have hPrep : ∀ a i,
      (evm_addmod_pow256_prepare_plus_one_mod_args_code (base + 64)) a = some i →
        (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    change CodeReq.ofProg (base + 64) evm_addmod_pow256_prepare_plus_one_mod_args a = some i at h
    exact CodeReq.ofProg_mono_append_left (base + 64)
      evm_addmod_pow256_prepare_plus_one_mod_args
      (evm_addmod_pow256_call_mod modOff) a i h
  have hEnter : ∀ a i,
      CodeReq.singleton ((base + 64) + 96) (.ADDI .x12 .x12 (64 : BitVec 12)) a = some i →
        (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    exact CodeReq.singleton_mono (by
      have hlookup := CodeReq.ofProg_lookup_addr (base + 64)
        (evm_addmod_pow256_prepare_plus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff) 24 ((base + 64) + 96)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_plus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_plus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by bv_omega)
      simpa [seq, evm_addmod_pow256_call_mod,
        evm_addmod_pow256_prepare_plus_one_mod_args_length] using hlookup) a i h
  have hJal : ∀ a i,
      CodeReq.singleton ((base + 64) + 100) (.JAL .x1 modOff) a = some i →
        (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    exact CodeReq.singleton_mono (by
      have hlookup := CodeReq.ofProg_lookup_addr (base + 64)
        (evm_addmod_pow256_prepare_plus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff) 25 ((base + 64) + 100)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_plus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_plus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by bv_omega)
      simpa [seq, evm_addmod_pow256_call_mod,
        evm_addmod_pow256_prepare_plus_one_mod_args_length] using hlookup) a i h
  have hRestore : ∀ a i,
      CodeReq.singleton (((base + 64) + 100) + 4) (.ADDI .x12 .x12 (4000 : BitVec 12)) a = some i →
        (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
          base modOff callableCode) a = some i := by
    intro a i h
    apply hLocal
    exact CodeReq.singleton_mono (by
      have hlookup := CodeReq.ofProg_lookup_addr (base + 64)
        (evm_addmod_pow256_prepare_plus_one_mod_args ;;
         evm_addmod_pow256_call_mod modOff) 26 (((base + 64) + 100) + 4)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_plus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by
          simp only [seq, Program.length_append,
            evm_addmod_pow256_prepare_plus_one_mod_args_length,
            evm_addmod_pow256_call_mod_length]
          omega)
        (by bv_omega)
      simpa [seq, evm_addmod_pow256_call_mod,
        evm_addmod_pow256_prepare_plus_one_mod_args_length] using hlookup) a i h
  have hdLocal : (evm_addmod_pow256_plus_one_local_call_restore_code base modOff).Disjoint
      callableCode := by
    intro a
    rcases hd a with h_full | h_callable
    · left
      cases h_local : evm_addmod_pow256_plus_one_local_call_restore_code base modOff a with
      | none => rfl
      | some instr =>
          have h_hit := hLocalProgram a instr h_local
          rw [h_full] at h_hit
          contradiction
    · right
      exact h_callable
  have hCallable : ∀ a i, callableCode a = some i →
      (evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
        base modOff callableCode) a = some i := by
    unfold evm_addmod_pow256_plus_one_local_call_restore_with_callable_code
    exact CodeReq.mono_union_right hdLocal (fun _ _ h => h)
  intro a i h
  apply evm_addmod_pow256_plus_one_local_call_restore_with_callable_sub base modOff callableCode hd
  unfold evm_addmod_pow256_plus_one_call_restore_code
    evm_addmod_pow256_plus_one_first_call_code
    evm_addmod_pow256_plus_one_shift_code at h
  exact CodeReq.union_sub
    (CodeReq.union_sub (CodeReq.union_sub hPrep hEnter) hJal)
    (CodeReq.union_sub hCallable hRestore) a i h



/-- The named shared pow256 call/restore code region is subsumed by the concrete
    helper program plus callable body. -/
theorem evm_addmod_pow256_mod_n_shared_code_with_callable_sub
    (base : Word) (modOff : BitVec 21) (callableCode : CodeReq)
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode) :
    ∀ a i, (evm_addmod_pow256_mod_n_shared_code base modOff callableCode) a = some i →
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) a = some i := by
  unfold evm_addmod_pow256_mod_n_shared_code
  exact CodeReq.union_sub
    (evm_addmod_pow256_minus_one_call_restore_with_callable_sub base modOff callableCode hd)
    (evm_addmod_pow256_plus_one_call_restore_with_callable_sub base modOff callableCode hd)

/-- Lift any proof over the named shared pow256 code region to the concrete
    helper program plus callable body. -/
theorem evm_addmod_pow256_shared_code_extend_to_concrete
    {nSteps : Nat} {entry exit_ base : Word} {modOff : BitVec 21}
    {callableCode : CodeReq} {P Q : Assertion}
    (hd : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode)
    (h : cpsTripleWithin nSteps entry exit_
      (evm_addmod_pow256_mod_n_shared_code base modOff callableCode) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode) P Q :=
  cpsTripleWithin_extend_code
    (evm_addmod_pow256_mod_n_shared_code_with_callable_sub base modOff callableCode hd) h

/-- Compose both pow256 callable-MOD calls over the concrete helper program plus
    callable body. -/
theorem evm_addmod_pow256_mod_n_with_callable_code_spec_within
    {nSteps1 nSteps2 : Nat} {callableCode : CodeReq} {F : Assertion}
    (hF : F.pcFree)
    (sp base x1Old x1Mid x5Old x5Mid x6Mid x7Mid : Word)
    (n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 r0 r1 r2 r3 : Word)
    (modOff : BitVec 21)
    (hdConcrete : (CodeReq.ofProg base (evm_addmod_pow256_mod_n modOff)).Disjoint callableCode)
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
      (evm_addmod_pow256_mod_n_with_callable_code base modOff callableCode)
      ((evmAddModPow256PrepareMinusOnePre sp
          x5Old n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3) **
       (.x1 ↦ᵣ x1Old))
      ((.x12 ↦ᵣ sp) ** F) := by
  exact evm_addmod_pow256_two_call_restore_shared_code_spec_within hF
    sp base x1Old x1Mid x5Old x5Mid x6Mid x7Mid
    n0 n1 n2 n3 w0 w1 w2 w3 u0 u1 u2 u3 r0 r1 r2 r3 modOff
    (evm_addmod_pow256_minus_one_call_restore_with_callable_sub base modOff callableCode hdConcrete)
    (evm_addmod_pow256_plus_one_call_restore_with_callable_sub base modOff callableCode hdConcrete)
    hdFirstEntry hdFirstRestore hdSecondEntry hdSecondRestore hCallable1 hCallable2


end EvmAsm.Evm64
