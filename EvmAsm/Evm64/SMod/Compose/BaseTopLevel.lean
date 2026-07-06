/-
  EvmAsm.Evm64.SMod.Compose.BaseTopLevel

  Top-level SMOD code-region and return-address facts.
-/

import EvmAsm.Evm64.SMod.AddrNorm
import EvmAsm.Evm64.SMod.Compose.ModCallCallable

namespace EvmAsm.Evm64.SMod.Compose

/-- Wrapper sub-region inside `smodCode`. -/
theorem smodCode_wrapper_sub {base : Word} :
    ∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_smod_wrapper) a = some i →
      (smodCode base) a = some i := by
  unfold smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base base evm_smod_legacy evm_smod_wrapper 0
    (EvmAsm.Evm64.SMod.AddrNorm.wrapperStart_addr base)
    (by unfold evm_smod_legacy; simp only [EvmAsm.Rv64.seq, EvmAsm.Rv64.Program]; rfl)
    (by
      rw [evm_smod_legacy_length, evm_smod_wrapper_length]
      norm_num)
    (by
      rw [evm_smod_legacy_length]
      norm_num)

/-- Wrapper sub-region inside `smodCodeV4`. -/
theorem smodCodeV4_wrapper_sub {base : Word} :
    ∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_smod_wrapper) a = some i →
      (smodCodeV4 base) a = some i := by
  unfold smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base base evm_smod evm_smod_wrapper 0
    (EvmAsm.Evm64.SMod.AddrNorm.wrapperStart_addr base)
    (by unfold evm_smod; simp only [EvmAsm.Rv64.seq, EvmAsm.Rv64.Program]; rfl)
    (by
      rw [evm_smod_length, evm_smod_wrapper_length]
      norm_num)
    (by
      rw [evm_smod_length]
      norm_num)

/-- Wrapper sub-region inside the canonical production SMOD code region. -/
theorem smodCodeCanonical_wrapper_sub {base : Word} :
    ∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_smod_wrapper) a = some i →
      (smodCodeCanonical base) a = some i := by
  simpa [smodCodeCanonical] using smodCodeV4_wrapper_sub (base := base)

/-- Bundled top-level SMOD code subsumptions for the wrapper and named appended
    legacy v1 unsigned MOD callable code. -/
theorem smodCode_named_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_smod_wrapper) a = some i →
      (smodCode base) a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.evm_mod_callable_code_v1 (base + wrapperEndOff)) a = some i →
      (smodCode base) a = some i) := by
  exact ⟨smodCode_wrapper_sub, evm_mod_callable_code_v1_sub_smodCode⟩

/-- Bundled top-level SMOD v4 code subsumptions for the wrapper and named
    appended v4 unsigned MOD callable code. -/
theorem smodCodeV4_named_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_smod_wrapper) a = some i →
      (smodCodeV4 base) a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.evm_mod_callable_code_v4 (base + wrapperEndOff)) a = some i →
      (smodCodeV4 base) a = some i) := by
  exact ⟨smodCodeV4_wrapper_sub, evm_mod_callable_code_v4_sub_smodCodeV4⟩

/-- Bundled top-level SMOD code subsumptions for the canonical production
    wrapper and named appended v4 unsigned MOD callable code. -/
theorem smodCodeCanonical_named_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base evm_smod_wrapper) a = some i →
      (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.evm_mod_callable_code_v4 (base + wrapperEndOff)) a = some i →
      (smodCodeCanonical base) a = some i) := by
  simpa [smodCodeCanonical] using smodCodeV4_named_top_level_subs (base := base)

/-- The near `JAL` at the SMOD wrapper's `modCall` block targets the appended
    unsigned MOD callable, which starts at `base + wrapperEndOff`. -/
theorem modCall_target_eq_wrapperEndOff (base : Word) :
    (base + modCallOff) + EvmAsm.Rv64.signExtend21 EvmAsm.Evm64.evm_smodCallOff =
      base + wrapperEndOff := by
  show (base + (192 : Word)) + (92 : Word) = base + (284 : Word)
  bv_omega

/-- Under the standard RV PC-alignment invariant, masking bit 0 on the
    result-sign-fixup entry is the identity. -/
theorem base_add_resultSignFixOff_andn_one
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + resultSignFixOff) &&& ~~~(1 : Word) = base + resultSignFixOff := by
  show (base + (196 : Word)) &&& ~~~(1 : Word) = base + (196 : Word)
  have hb0 : base.getLsbD 0 = false := by
    have h : (base &&& 1).getLsbD 0 = (0 : Word).getLsbD 0 := by rw [hbase]
    rw [BitVec.getLsbD_and] at h
    rw [show BitVec.getLsbD (1 : Word) 0 = true from rfl,
        show BitVec.getLsbD (0 : Word) 0 = false from rfl, Bool.and_true] at h
    exact h
  have hsum0 : (base + 196 : Word).getLsbD 0 = false := by
    rw [BitVec.getLsbD_add (by omega), hb0, BitVec.carry_zero]; rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0; rw [hsum0]; simp
  · have h1 : (1 : Word).getLsbD i = false := by simp [BitVec.getLsbD_one, h0]
    rw [h1]; simp [hi]

/-- The return address written by the SMOD wrapper's near `modCall` is exactly
    the result-sign-fixup entry, and masking bit 0 for the eventual `JALR`
    keeps it there. -/
theorem modCall_return_andn_one_eq_resultSignFixOff
    (base : Word) (hbase : base &&& 1 = 0) :
    (((base + modCallOff) + 4 : Word) &&& ~~~(1 : Word)) =
      base + resultSignFixOff := by
  show (((base + (192 : Word)) + (4 : Word)) &&& ~~~(1 : Word)) =
      base + (196 : Word)
  have hsum : (base + 192 + 4 : Word) = base + 196 := by bv_omega
  rw [hsum]
  have hb0 : base.getLsbD 0 = false := by
    have h : (base &&& 1).getLsbD 0 = (0 : Word).getLsbD 0 := by rw [hbase]
    rw [BitVec.getLsbD_and] at h
    rw [show BitVec.getLsbD (1 : Word) 0 = true from rfl,
        show BitVec.getLsbD (0 : Word) 0 = false from rfl, Bool.and_true] at h
    exact h
  have hsum0 : (base + 196 : Word).getLsbD 0 = false := by
    rw [BitVec.getLsbD_add (by omega), hb0, BitVec.carry_zero]; rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0; rw [hsum0]; simp
  · have h1 : (1 : Word).getLsbD i = false := by simp [BitVec.getLsbD_one, h0]
    rw [h1]; simp [hi]

end EvmAsm.Evm64.SMod.Compose
