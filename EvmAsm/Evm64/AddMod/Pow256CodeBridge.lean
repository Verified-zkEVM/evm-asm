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


end EvmAsm.Evm64
