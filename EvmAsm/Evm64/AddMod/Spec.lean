/-
  EvmAsm.Evm64.AddMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_addmod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  The general `evm_addmod_stack_spec_within` theorem lands in slice
  evm-asm-sord and is composed from the verified shared bridge with
  the boundary blocks. The addmod-correctness lemma
  `EvmWord.addmod_correct` is added in an earlier slice (see
  parent task evm-asm-z7qm).

  Architecture notes for N=0 case (bead evm-asm-a32mz):
  - When N=0, the mod callable follows the zeroPath: stores zeros at
    x12+32..x12+56 WITHOUT advancing x12.
  - cc_ret preserves x1=(base+128) through the zeroPath.
  - After cc_ret, the epilogue at base+128 advances x12 by 32.
  - Net: x12 goes sp → sp+32 (prologue) → sp+32 (zeroPath) → sp+64 (epilogue).
  - Result (zero) sits at sp+64 = final x12. Correct for ADDMOD pop-3-push-1.
  - Infrastructure available: evm_mod_callable_bzero_v1_preserving_x1_noX9_spec
    (from DivMod/CallableV1Legacy.lean) enables the proof while the
    ADDMOD implementation remains pinned to the legacy callable.
-/

import EvmAsm.Evm64.AddMod.Compose.Base
import EvmAsm.Evm64.AddMod.Compose.ZeroBranch
import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.CallableV1Legacy
import EvmAsm.Evm64.EvmWordArith.AddMod
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.LiftSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.AddMod.Compose

/-! ## ADDMOD N=0 dispatch bridge

The bridge lemma connects the prologue postcondition
`evmAddModPhase1Phase2LimbPost` (for b=N=0) to the mod callable
    precondition `divModStackDispatchPreCallable`. This is the key step enabling
the N=0 end-to-end proof (bead evm-asm-a32mz).

Key simplification: when b=0 (the second ADDMOD operand = N = 0),
all carry computations yield 0, so sum = a (the first operand
unchanged), and the prologue POST has concrete zero carries.
-/

/-- When b=0, the carry chain in `evmAddModPhase1Phase2LimbPost` is trivial.
    All carries are 0, so `sum = a` (all limbs). -/
private theorem evmAddModPhase1Phase2LimbPost_b0_simp
    (base sp a0 a1 a2 a3 : Word) :
    evmAddModPhase1Phase2LimbPost base sp a0 a1 a2 a3 0 0 0 0 =
    (((.x12 ↦ᵣ (sp + 32)) **
      (.x7 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0 : Word)) **
      (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
      ((sp + 32) ↦ₘ a0) ** ((sp + 40) ↦ₘ a1) **
      ((sp + 48) ↦ₘ a2) ** ((sp + 56) ↦ₘ a3)) **
     (.x1 ↦ᵣ ((base + 124) + 4))) := by
  simp [evmAddModPhase1Phase2LimbPost_unfold, BitVec.ult]
  simp [signExtend12, BitVec.signExtend]

/-- Dispatch bridge for ADDMOD N=0: from the prologue POST (b=0 simplified)
    plus register/memory frame, to the mod callable dispatch PRE.

    The prologue POST carries:
    - x12=sp+32, x1=base+128 (= raVal)
    - Carry registers = 0 (since b=0 means no carry anywhere)
    - Sum at sp+32..sp+56 = a (same as original, since a+0=a)
    - Original a at sp..sp+24

    Combined with the frame (x2, x10, x0=0, N=0 at sp+64..sp+88, scratch),
      this gives exactly `divModStackDispatchPreCallable (sp+32) a 0 (base+128) ...`. -/
private theorem evm_addmod_n0_dispatch_bridge
    (sp base : Word) (a : EvmWord)
    (a0 a1 a2 a3 v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (s : PartialState)
    (hpre :
      (evmAddModPhase1Phase2LimbPost base sp a0 a1 a2 a3 0 0 0 0 **
       (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 64) ↦ₘ (0 : Word)) ** ((sp + 72) ↦ₘ (0 : Word)) **
       ((sp + 80) ↦ₘ (0 : Word)) ** ((sp + 88) ↦ₘ (0 : Word)) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0) s) :
      (divModStackDispatchPreCallable (sp + 32) a (0 : EvmWord) ((base + 124) + 4)
         v2 0 0 0 v10 0
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
     (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) s := by
  rw [divModStackDispatchPreCallable_unfold]
  rw [evmAddModPhase1Phase2LimbPost_b0_simp] at hpre
  -- Expand evmWordIs (sp+32) a → atoms at sp+32..sp+56
  simp only [evmWordIs_sp32_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3]
  -- Expand evmWordIs (sp+32+32) 0 → atoms at sp+64..sp+88
  simp only [evmWordIs_sp_limbs_eq (sp + 32 + 32) (0 : EvmWord) 0 0 0 0
    (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
    (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3)]
  -- Normalize addresses and reduce concrete sums
  simp only [BitVec.add_assoc] at hpre ⊢
  simp only [show (32 : Word) + 8 = 40 from by bv_omega,
    show (32 : Word) + 16 = 48 from by bv_omega,
    show (32 : Word) + 24 = 56 from by bv_omega,
    show (32 : Word) + 32 = 64 from by bv_omega,
    show (32 : Word) + 40 = 72 from by bv_omega,
    show (32 : Word) + 48 = 80 from by bv_omega,
    show (32 : Word) + 56 = 88 from by bv_omega,
    show (124 : Word) + 4 = 128 from by bv_omega] at hpre ⊢
  -- All atoms match between hpre and the goal
  xperm_hyp hpre


/-- Dispatch bridge for ADDMOD N=0 with arbitrary second operand.

    The prologue has already replaced the second slot by `a + b`; this bridge
    folds that carry-chain limb postcondition into the MOD callable precondition
    for dividend `a + b` and zero divisor. -/
private theorem evm_addmod_n0_dispatch_bridge_general
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (s : PartialState)
    (hpre :
      (evmAddModPhase1Phase2LimbPost base sp a0 a1 a2 a3 b0 b1 b2 b3 **
       (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 64) ↦ₘ (0 : Word)) ** ((sp + 72) ↦ₘ (0 : Word)) **
       ((sp + 80) ↦ₘ (0 : Word)) ** ((sp + 88) ↦ₘ (0 : Word)) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0) s) :
      let sum0 := a0 + b0
      let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
      let psum1 := a1 + b1
      let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
      let result1 := psum1 + carry0
      let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
      let carry1 := carry1a ||| carry1b
      let psum2 := a2 + b2
      let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
      let result2 := psum2 + carry1
      let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
      let carry2 := carry2a ||| carry2b
      let psum3 := a3 + b3
      let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
      let result3 := psum3 + carry2
      let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
      let carry3 := carry3a ||| carry3b
      (divModStackDispatchPreCallable (sp + 32) (a + b) (0 : EvmWord) ((base + 124) + 4)
         v2 carry3 carry3b carry3 v10 carry3a
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
     evmWordIs sp a) s := by
  dsimp only
  rw [divModStackDispatchPreCallable_unfold]
  rw [evmAddModPhase1Phase2LimbPost_unfold] at hpre
  have ⟨h0, h1, h2, h3⟩ := EvmWord.add_carry_chain_correct a b
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h0 h1 h2 h3
  rw [ha0, hb0] at h0
  rw [ha1, hb1, ha0, hb0] at h1
  rw [ha2, hb2, ha1, hb1, ha0, hb0] at h2
  rw [ha3, hb3, ha2, hb2, ha1, hb1, ha0, hb0] at h3
  simp only [evmWordIs_sp32_limbs_eq sp (a + b) _ _ _ _ h0 h1 h2 h3,
    evmWordIs_sp_limbs_eq (sp + 32 + 32) (0 : EvmWord) 0 0 0 0
      (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
      (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3),
    evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3]
  simp only [BitVec.add_assoc] at hpre ⊢
  simp only [signExtend12, BitVec.signExtend] at hpre ⊢
  simp only [show (32 : Word) + 8 = 40 from by bv_omega,
    show (32 : Word) + 16 = 48 from by bv_omega,
    show (32 : Word) + 24 = 56 from by bv_omega,
    show (32 : Word) + 32 = 64 from by bv_omega,
    show (32 : Word) + 40 = 72 from by bv_omega,
    show (32 : Word) + 48 = 80 from by bv_omega,
    show (32 : Word) + 56 = 88 from by bv_omega,
    show (124 : Word) + 4 = 128 from by bv_omega] at hpre ⊢
  simp at hpre ⊢
  xperm_hyp hpre


/-- Dispatch bridge for ADDMOD with arbitrary modulus.

    The prologue has replaced the second slot by the truncated sum `a + b` and
    left the carry chain in registers. This bridge folds that limb-level post
    into the MOD callable precondition for dividend `a + b` and divisor `N`,
    retaining the original first operand as a frame. -/
private theorem evm_addmod_dispatch_bridge_general
    (sp base : Word) (a b N : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hn0 : N.getLimbN 0 = n0) (hn1 : N.getLimbN 1 = n1)
    (hn2 : N.getLimbN 2 = n2) (hn3 : N.getLimbN 3 = n3)
    (s : PartialState)
    (hpre :
      (evmAddModPhase1Phase2LimbPost base sp a0 a1 a2 a3 b0 b1 b2 b3 **
       (.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) **
       ((sp + 80) ↦ₘ n2) ** ((sp + 88) ↦ₘ n3) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0) s) :
      let sum0 := a0 + b0
      let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
      let psum1 := a1 + b1
      let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
      let result1 := psum1 + carry0
      let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
      let carry1 := carry1a ||| carry1b
      let psum2 := a2 + b2
      let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
      let result2 := psum2 + carry1
      let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
      let carry2 := carry2a ||| carry2b
      let psum3 := a3 + b3
      let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
      let result3 := psum3 + carry2
      let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
      let carry3 := carry3a ||| carry3b
      (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
         v2 carry3 carry3b carry3 v10 carry3a
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       evmWordIs sp a) s := by
  dsimp only
  rw [divModStackDispatchPreCallable_unfold]
  rw [evmAddModPhase1Phase2LimbPost_unfold] at hpre
  have ⟨h0, h1, h2, h3⟩ := EvmWord.add_carry_chain_correct a b
  simp only [EvmWord.getLimb_as_getLimbN_0, EvmWord.getLimb_as_getLimbN_1,
    EvmWord.getLimb_as_getLimbN_2, EvmWord.getLimb_as_getLimbN_3] at h0 h1 h2 h3
  rw [ha0, hb0] at h0
  rw [ha1, hb1, ha0, hb0] at h1
  rw [ha2, hb2, ha1, hb1, ha0, hb0] at h2
  rw [ha3, hb3, ha2, hb2, ha1, hb1, ha0, hb0] at h3
  simp only [evmWordIs_sp32_limbs_eq sp (a + b) _ _ _ _ h0 h1 h2 h3,
    evmWordIs_sp_limbs_eq (sp + 32 + 32) N n0 n1 n2 n3 hn0 hn1 hn2 hn3,
    evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3]
  simp only [BitVec.add_assoc] at hpre ⊢
  simp only [signExtend12, BitVec.signExtend] at hpre ⊢
  simp only [show (32 : Word) + 8 = 40 from by bv_omega,
    show (32 : Word) + 16 = 48 from by bv_omega,
    show (32 : Word) + 24 = 56 from by bv_omega,
    show (32 : Word) + 32 = 64 from by bv_omega,
    show (32 : Word) + 40 = 72 from by bv_omega,
    show (32 : Word) + 48 = 80 from by bv_omega,
    show (32 : Word) + 56 = 88 from by bv_omega,
    show (124 : Word) + 4 = 128 from by bv_omega] at hpre ⊢
  simp at hpre ⊢
  xperm_hyp hpre

/-! ## Alignment helpers -/

private theorem addmod_and_not_one_eq (base : BitVec 64) (hbase : base &&& 1 = 0) :
    base &&& ~~~1 = base := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]
  have hbase0 : base.getLsbD 0 = false := by
    have h := congr_arg (·.getLsbD 0) hbase
    simp only [BitVec.getLsbD_and, show (BitVec.getLsbD (1 : Word) 0) = true from by simp,
               Bool.and_true] at h
    exact h
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [show (BitVec.getLsbD (1 : Word) 0) = true from by simp, Bool.not_true, Bool.and_false,
        hbase0]
  · have h1i : (BitVec.getLsbD (1 : Word) i) = false := by
      simp only [show (1 : Word) = BitVec.ofNat 64 1 from rfl]
      rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and, Nat.testBit_lt_two_pow]
      exact (Nat.pow_lt_pow_right (by norm_num) hi0).trans_le le_rfl
    rw [h1i, Bool.not_false, Bool.and_true]

private theorem addmod_even_and_one_eq_zero (base : BitVec 64) (hbase : base &&& 1 = 0) :
    (base + 128 : BitVec 64) &&& 1 = 0 := by
  have hbase0 : base.getLsbD 0 = false := by
    have h := congr_arg (·.getLsbD 0) hbase
    simp only [BitVec.getLsbD_and, show (BitVec.getLsbD (1 : Word) 0) = true from by simp,
               Bool.and_true] at h
    exact h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [show (BitVec.getLsbD (1 : Word) 0) = true from by simp, Bool.and_true]
    rw [BitVec.getLsbD_add (by omega : 0 < 64)]
    have hc : BitVec.carry 0 base (128 : Word) false = false := by
      simp [BitVec.carry, Nat.mod_one]
    have h128 : (BitVec.getLsbD (128 : Word) 0) = false := by simp
    rw [h128, hc, Bool.false_xor, Bool.xor_false, hbase0]
    simp
  · have h1i : (BitVec.getLsbD (1 : Word) i) = false := by
      simp only [show (1 : Word) = BitVec.ofNat 64 1 from rfl]
      rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and, Nat.testBit_lt_two_pow]
      exact (Nat.pow_lt_pow_right (by norm_num) hi0).trans_le le_rfl
    rw [h1i, Bool.and_false]
    simp [BitVec.getLsbD_zero]


/-! ## ADDMOD through the MOD callable -/

/-- ADDMOD prologue composed with an arbitrary MOD-callable proof.

    This is the common nonzero-modulus spine: the ADDMOD prologue computes the
    truncated `a + b` and carry registers, then hands `(a + b, N)` to the MOD
    callable. The theorem is intentionally parameterized by `hStack`, because
    the legacy MOD callable still exposes branch/domain-specific proofs. -/
theorem evm_addmod_mod_call_return_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hn0 : N.getLimbN 0 = n0) (hn1 : N.getLimbN 1 = n1)
    (hn2 : N.getLimbN 2 = n2) (hn3 : N.getLimbN 3 = n3)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hStack :
      let sum0 := a0 + b0
      let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
      let psum1 := a1 + b1
      let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
      let result1 := psum1 + carry0
      let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
      let carry1 := carry1a ||| carry1b
      let psum2 := a2 + b2
      let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
      let result2 := psum2 + carry1
      let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
      let carry2 := carry2a ||| carry2b
      let psum3 := a3 + b3
      let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
      let result3 := psum3 + carry2
      let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
      let carry3 := carry3a ||| carry3b
      cpsTripleWithin (unifiedDivBound + 1)
        callable_base (base + 128) (evm_mod_callable_code_v1 callable_base)
        (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
          v2 carry3 carry3b carry3 v10 carry3a
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable (sp + 32) (a + b) N **
          (.x1 ↦ᵣ ((base + 124) + 4)))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) N **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((modStackDispatchPostCallable (sp + 32) (a + b) N **
          (.x1 ↦ᵣ ((base + 124) + 4))) ** evmWordIs sp a) := by
  subst hcallable
  have hmono_prog : ∀ ad i,
      (evm_addmod_program_code base modOff) ad = some i →
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) ad = some i :=
    fun ad i h => CodeReq.union_mono_left ad i h
  have hmono_call : ∀ ad i,
      (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)) ad = some i →
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) ad = some i :=
    CodeReq.mono_union_right hdisjoint (fun _ _ h => h)
  let sum0 := a0 + b0
  let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
  let psum1 := a1 + b1
  let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
  let result1 := psum1 + carry0
  let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
  let carry1 := carry1a ||| carry1b
  let psum2 := a2 + b2
  let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
  let result2 := psum2 + carry1
  let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
  let carry2 := carry2a ||| carry2b
  let psum3 := a3 + b3
  let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
  let result3 := psum3 + carry2
  let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
  let carry3 := carry3a ||| carry3b
  have hprologue_to_call : cpsTripleWithin (31 + 1) base ((base + 124) + signExtend21 modOff)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) N **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
         v2 carry3 carry3b carry3 v10 carry3a
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       evmWordIs sp a) := by
    apply cpsTripleWithin_weaken _ _ (cpsTripleWithin_extend_code (hmono := hmono_prog)
      (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp)
        (cpsTripleWithin_frameR
          ((.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 64) ↦ₘ n0) ** ((sp + 72) ↦ₘ n1) **
           ((sp + 80) ↦ₘ n2) ** ((sp + 88) ↦ₘ n3) **
             divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
               shiftMem nMem jMem retMem dMem dloMem scratchUn0)
            (by rw [divScratchValuesCallNoX1_unfold]; pcFree)
          (evm_addmod_prologue_phase1_phase2_reduce_named_spec_within
            sp base modOff a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11 v1))))
    · intro _ hp
      rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b b0 b1 b2 b3 hb0 hb1 hb2 hb3,
          evmWordIs_sp64_limbs_eq sp N n0 n1 n2 n3 hn0 hn1 hn2 hn3] at hp
      xperm_hyp hp
    · intro s hpost
      exact evm_addmod_dispatch_bridge_general sp base a b N
        a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hn0 hn1 hn2 hn3 s hpost
  dsimp only at hStack
  have hcall := cpsTripleWithin_extend_code (hmono := hmono_call)
    (cpsTripleWithin_frameR (evmWordIs sp a) (by pcFree) hStack)
  exact cpsTripleWithin_seq_same_cr hprologue_to_call hcall


/-- Public postcondition for the ADDMOD skeleton under the no-overflow condition.

    The current skeleton feeds the truncated word sum `a + b` into MOD. Under
    `a.toNat + b.toNat < 2^256`, that is semantically the same as ADDMOD's
    full-precision sum. -/
@[irreducible]
def evmAddModNoOverflowCallReturnPost (sp base : Word) (a b N : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 64)) ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs (sp + 32) (a + b) **
  evmWordIs (sp + 64) (EvmWord.addmod a b N) **
  divScratchOwnCallNoX1 (sp + 32) **
  (.x1 ↦ᵣ ((base + 124) + 4)) **
  evmWordIs sp a

theorem evmAddModNoOverflowCallReturnPost_unfold
    (sp base : Word) (a b N : EvmWord) :
    evmAddModNoOverflowCallReturnPost sp base a b N =
      ((.x12 ↦ᵣ (sp + 64)) ** regOwn .x2 **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs (sp + 32) (a + b) **
       evmWordIs (sp + 64) (EvmWord.addmod a b N) **
       divScratchOwnCallNoX1 (sp + 32) **
       (.x1 ↦ᵣ ((base + 124) + 4)) **
       evmWordIs sp a) := by
  delta evmAddModNoOverflowCallReturnPost
  rfl

theorem evmAddModNoOverflowCallReturnPost_pcFree
    (sp base : Word) (a b N : EvmWord) :
    (evmAddModNoOverflowCallReturnPost sp base a b N).pcFree := by
  rw [evmAddModNoOverflowCallReturnPost_unfold]
  pcFree

instance pcFreeInst_evmAddModNoOverflowCallReturnPost
    (sp base : Word) (a b N : EvmWord) :
    Assertion.PCFree (evmAddModNoOverflowCallReturnPost sp base a b N) :=
  ⟨evmAddModNoOverflowCallReturnPost_pcFree sp base a b N⟩

@[irreducible]
def evmAddModNoOverflowCallReturnStackPost (sp base : Word) (a b N : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 64)) ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmStackIs sp [a, a + b, EvmWord.addmod a b N] **
  divScratchOwnCallNoX1 (sp + 32) **
  (.x1 ↦ᵣ ((base + 124) + 4))

theorem evmAddModNoOverflowCallReturnStackPost_unfold
    (sp base : Word) (a b N : EvmWord) :
    evmAddModNoOverflowCallReturnStackPost sp base a b N =
      ((.x12 ↦ᵣ (sp + 64)) ** regOwn .x2 **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmStackIs sp [a, a + b, EvmWord.addmod a b N] **
       divScratchOwnCallNoX1 (sp + 32) **
       (.x1 ↦ᵣ ((base + 124) + 4))) := by
  delta evmAddModNoOverflowCallReturnStackPost
  rfl

theorem evmAddModNoOverflowCallReturnStackPost_pcFree
    (sp base : Word) (a b N : EvmWord) :
    (evmAddModNoOverflowCallReturnStackPost sp base a b N).pcFree := by
  rw [evmAddModNoOverflowCallReturnStackPost_unfold]
  pcFree

instance pcFreeInst_evmAddModNoOverflowCallReturnStackPost
    (sp base : Word) (a b N : EvmWord) :
    Assertion.PCFree (evmAddModNoOverflowCallReturnStackPost sp base a b N) :=
  ⟨evmAddModNoOverflowCallReturnStackPost_pcFree sp base a b N⟩

theorem evmAddModNoOverflowCallReturnPost_to_stackPost
    {sp base : Word} {a b N : EvmWord} {ps : PartialState}
    (h : evmAddModNoOverflowCallReturnPost sp base a b N ps) :
    evmAddModNoOverflowCallReturnStackPost sp base a b N ps := by
  rw [evmAddModNoOverflowCallReturnPost_unfold] at h
  rw [evmAddModNoOverflowCallReturnStackPost_unfold]
  rw [evmStackIs_triple_flat]
  xperm_hyp h

@[irreducible]
def evmAddModPartialStackPre
    (sp : Word) (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
  (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
  evmStackIs sp [a, b, N] **
    divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0

theorem evmAddModPartialStackPre_unfold
    (sp : Word) (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) :
    evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 =
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmStackIs sp [a, b, N] **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  delta evmAddModPartialStackPre
  rfl

theorem evmAddModPartialStackPre_pcFree
    (sp : Word) (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) :
    (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0).pcFree := by
  rw [evmAddModPartialStackPre_unfold]
  pcFree

instance pcFreeInst_evmAddModPartialStackPre
    (sp : Word) (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) :
    Assertion.PCFree
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :=
  ⟨evmAddModPartialStackPre_pcFree sp a b N v1 v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0⟩

/-- ADDMOD callable-return stack theorem for the current skeleton under the
    no-overflow condition. It turns the MOD callable's `EvmWord.mod (a+b) N`
    result into `EvmWord.addmod a b N`. -/
theorem evm_addmod_no_overflow_mod_call_return_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hn0 : N.getLimbN 0 = n0) (hn1 : N.getLimbN 1 = n1)
    (hn2 : N.getLimbN 2 = n2) (hn3 : N.getLimbN 3 = n3)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hStack :
      let sum0 := a0 + b0
      let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
      let psum1 := a1 + b1
      let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
      let result1 := psum1 + carry0
      let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
      let carry1 := carry1a ||| carry1b
      let psum2 := a2 + b2
      let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
      let result2 := psum2 + carry1
      let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
      let carry2 := carry2a ||| carry2b
      let psum3 := a3 + b3
      let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
      let result3 := psum3 + carry2
      let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
      let carry3 := carry3a ||| carry3b
      cpsTripleWithin (unifiedDivBound + 1)
        callable_base (base + 128) (evm_mod_callable_code_v1 callable_base)
        (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
          v2 carry3 carry3b carry3 v10 carry3a
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable (sp + 32) (a + b) N **
          (.x1 ↦ᵣ ((base + 124) + 4)))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) N **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnPost sp base a b N) := by
  have hmain := evm_addmod_mod_call_return_stack_spec_within
    sp base callable_base a b N
    a0 a1 a2 a3 b0 b1 b2 b3 n0 n1 n2 n3 v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hn0 hn1 hn2 hn3 hcallable hdisjoint hStack
  have hsem := EvmWord.mod_truncated_sum_eq_addmod_of_no_overflow a b N hNoOverflow
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun s hpost => by
      rw [modStackDispatchPostCallable_unfold] at hpost
      rw [evmAddModNoOverflowCallReturnPost_unfold]
      rw [hsem] at hpost
      simp only [BitVec.add_assoc] at hpost ⊢
      simp only [show (32 : Word) + 32 = 64 from by bv_omega] at hpost ⊢
      xperm_hyp hpost)
    hmain

/-- Word-level wrapper for `evm_addmod_no_overflow_mod_call_return_stack_spec_within`.

    This removes the twelve limb-equality parameters from the public surface;
    callers still provide the MOD callable proof and the no-overflow hypothesis. -/
theorem evm_addmod_no_overflow_word_mod_call_return_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hStack :
      let a0 := a.getLimbN 0
      let a1 := a.getLimbN 1
      let a2 := a.getLimbN 2
      let a3 := a.getLimbN 3
      let b0 := b.getLimbN 0
      let b1 := b.getLimbN 1
      let b2 := b.getLimbN 2
      let b3 := b.getLimbN 3
      let sum0 := a0 + b0
      let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
      let psum1 := a1 + b1
      let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
      let result1 := psum1 + carry0
      let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
      let carry1 := carry1a ||| carry1b
      let psum2 := a2 + b2
      let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
      let result2 := psum2 + carry1
      let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
      let carry2 := carry2a ||| carry2b
      let psum3 := a3 + b3
      let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
      let result3 := psum3 + carry2
      let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
      let carry3 := carry3a ||| carry3b
      cpsTripleWithin (unifiedDivBound + 1)
        callable_base (base + 128) (evm_mod_callable_code_v1 callable_base)
        (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
          v2 carry3 carry3b carry3 v10 carry3a
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable (sp + 32) (a + b) N **
          (.x1 ↦ᵣ ((base + 124) + 4)))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) N **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnPost sp base a b N) := by
  exact evm_addmod_no_overflow_mod_call_return_stack_spec_within
    sp base callable_base a b N
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (N.getLimbN 0) (N.getLimbN 1) (N.getLimbN 2) (N.getLimbN 3)
    v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hNoOverflow hcallable hdisjoint hStack

/-- No-overflow ADDMOD wrapper that accepts the legacy v1 MOD no-NOP body proof.

The supplied MOD proof stops at `base + nopOff`; this theorem adds the legacy
callable return adapter and then reuses
`evm_addmod_no_overflow_word_mod_call_return_stack_spec_within`. -/
theorem evm_addmod_no_overflow_word_mod_body_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hNoOverflow : a.toNat + b.toNat < 2 ^ 256)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hStack :
      let a0 := a.getLimbN 0
      let a1 := a.getLimbN 1
      let a2 := a.getLimbN 2
      let a3 := a.getLimbN 3
      let b0 := b.getLimbN 0
      let b1 := b.getLimbN 1
      let b2 := b.getLimbN 2
      let b3 := b.getLimbN 3
      let sum0 := a0 + b0
      let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
      let psum1 := a1 + b1
      let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
      let result1 := psum1 + carry0
      let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
      let carry1 := carry1a ||| carry1b
      let psum2 := a2 + b2
      let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
      let result2 := psum2 + carry1
      let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
      let carry2 := carry2a ||| carry2b
      let psum3 := a3 + b3
      let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
      let result3 := psum3 + carry2
      let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
      let carry3 := carry3a ||| carry3b
      cpsTripleWithin unifiedDivBound
        callable_base (callable_base + nopOff) (modCode_noNop callable_base)
        (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
          v2 carry3 carry3b carry3 v10 carry3a
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable (sp + 32) (a + b) N **
          (.x1 ↦ᵣ ((base + 124) + 4)))) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) N **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnPost sp base a b N) := by
  subst hcallable
  have hraVal_align : (((base + 124 : Word) + 4) &&& ~~~1) = base + 128 := by
    rw [show (base + 124 : Word) + 4 = base + 128 from by bv_omega]
    exact addmod_and_not_one_eq _ (addmod_even_and_one_eq_zero base hbase)
  let a0 := a.getLimbN 0
  let a1 := a.getLimbN 1
  let a2 := a.getLimbN 2
  let a3 := a.getLimbN 3
  let b0 := b.getLimbN 0
  let b1 := b.getLimbN 1
  let b2 := b.getLimbN 2
  let b3 := b.getLimbN 3
  let sum0 := a0 + b0
  let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
  let psum1 := a1 + b1
  let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
  let result1 := psum1 + carry0
  let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
  let carry1 := carry1a ||| carry1b
  let psum2 := a2 + b2
  let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
  let result2 := psum2 + carry1
  let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
  let carry2 := carry2a ||| carry2b
  let psum3 := a3 + b3
  let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
  let result3 := psum3 + carry2
  let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
  let carry3 := carry3a ||| carry3b
  have hcallRaw :=
    evm_mod_callable_v1_spec_from_noNop_preserving_x1_noX9
      (sp + 32) ((base + 124) + signExtend21 modOff) ((base + 124) + 4)
      (a + b) N v2 carry3 carry3b carry3 v10 carry3a
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hStack
  rw [hraVal_align] at hcallRaw
  exact evm_addmod_no_overflow_word_mod_call_return_stack_spec_within
    sp base ((base + 124) + signExtend21 modOff) a b N v1 v2 v5 v6 v7 v10 v11
    modOff q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hNoOverflow rfl hdisjoint hcallRaw

/-! ## ADDMOD N=0 end-to-end spec

ADDMOD(a, 0, 0) = 0: when second operand b=0 AND modulus N=0,
the result is 0 (the mod callable zeroPath stores zeros and preserves x1).
Combined code region: `evm_addmod_program_code base modOff ∪ evm_mod_callable_code_v1 callable_base`.
-/

/-- ADDMOD(a, 0, 0) = 0 end-to-end spec (bead evm-asm-a32mz).

    PRE:  x12=sp, a at sp, b=0 at sp+32, N=0 at sp+64; registers; divScratch at (sp+32)+.
    POST: x12=sp+64 (ADDMOD result 0 at sp+64); a preserved at sp; registers weakened.

    Hypothesis `hdisjoint` ensures the addmod program code and mod callable are at
    disjoint addresses (required because they are composed via CodeReq.union). -/
theorem evm_addmod_b0_n0_spec_within
    (sp base callable_base : Word)
    (a : EvmWord) (a0 a1 a2 a3 v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    -- The callable's bzero path advances x12 from sp+32 to sp+64 (via divK_zeroPath),
    -- so the spec exits at base+128 (where cc_ret returns) without the epilogue.
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (0 : EvmWord) **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((.x12 ↦ᵣ (sp + 64)) **
       (.x1 ↦ᵣ ((base + 124) + 4)) **
       regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) a **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchOwnCallNoX1 (sp + 32)) := by
  subst hcallable
  -- Code-region monotonicity helpers
  have hmono_prog : ∀ ad i,
      (evm_addmod_program_code base modOff) ad = some i →
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) ad = some i :=
    fun ad i h => CodeReq.union_mono_left ad i h
  have hmono_call : ∀ ad i,
      (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)) ad = some i →
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) ad = some i :=
    CodeReq.mono_union_right hdisjoint (fun _ _ h => h)
  -- raVal = (base+124)+4 = base+128. With base aligned (base &&& 1 = 0), base+128 is also aligned.
  have hraVal_eq : (base + 124 : Word) + 4 = base + 128 := by bv_omega
  -- ((base+128) &&& ~~~1) = base+128 since base+128 is even (base even + 128 even)
  have hraVal_align : ((base + 124) + 4 : Word) &&& ~~~1 = base + 128 := by
    rw [show (base + 124 : Word) + 4 = base + 128 from by bv_omega]
    exact addmod_and_not_one_eq _ (addmod_even_and_one_eq_zero base hbase)
  -- Step 1: Prologue framed + POST weaken to callable PRE
  have hprologue_to_call : cpsTripleWithin (31 + 1) base ((base + 124) + signExtend21 modOff)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (0 : EvmWord) **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divModStackDispatchPreCallable (sp + 32) a (0 : EvmWord) ((base + 124) + 4)
           v2 0 0 0 v10 0
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3)) := by
    apply cpsTripleWithin_weaken _ _ (cpsTripleWithin_extend_code (hmono := hmono_prog)
      (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp)
        (cpsTripleWithin_frameR
          ((.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 64) ↦ₘ (0 : Word)) ** ((sp + 72) ↦ₘ (0 : Word)) **
           ((sp + 80) ↦ₘ (0 : Word)) ** ((sp + 88) ↦ₘ (0 : Word)) **
             divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
               shiftMem nMem jMem retMem dMem dloMem scratchUn0)
            (by rw [divScratchValuesCallNoX1_unfold]; pcFree)
          (evm_addmod_prologue_phase1_phase2_reduce_named_spec_within
            sp base modOff a0 a1 a2 a3 0 0 0 0 v7 v6 v5 v11 v1))))
    · -- PRE weaken: expand evmWordIs atoms to match framed prologue PRE
      intro _ hp
      rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp (0 : EvmWord) 0 0 0 0
            (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
            (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3),
          evmWordIs_sp64_limbs_eq sp (0 : EvmWord) 0 0 0 0
            (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
            (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3)] at hp
      xperm_hyp hp
    · -- POST weaken: framed prologue POST → callable PRE via dispatch bridge
      intro s hpost
      exact evm_addmod_n0_dispatch_bridge sp base a a0 a1 a2 a3 v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        ha0 ha1 ha2 ha3 s hpost
  -- Step 2: Callable spec (N=0 bzero) framed with original-a atoms
  -- The callable exits at raVal &&& ~~~1 = (base+124+4) &&& ~~~1 = base+128.
  have hcall_raw :=
      evm_mod_callable_bzero_v1_preserving_x1_noX9_spec
        (sp + 32) ((base + 124) + signExtend21 modOff) ((base + 124) + 4)
      a (0 : EvmWord) v2 0 0 0 v10 0
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 rfl
  -- Rewrite exit PC: raVal &&& ~~~1 = base + 128
  rw [hraVal_align] at hcall_raw
  have hcall :=
    cpsTripleWithin_extend_code (hmono := hmono_call)
      (cpsTripleWithin_frameR
        ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
        (by pcFree)
        hcall_raw)
  -- Compose prologue + callable; POST weaken to final form.
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun s hpost => by
      rw [modStackDispatchPostCallable_unfold, EvmWord.mod_zero_right] at hpost
      rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold] at hpost
      rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3]
      rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
      simp only [BitVec.add_assoc] at hpost ⊢
      simp only [show (32 : Word) + 32 = 64 from by bv_omega,
        show (124 : Word) + 4 = 128 from by bv_omega] at hpost ⊢
      xperm_hyp hpost)
    (cpsTripleWithin_seq_same_cr hprologue_to_call hcall)


/-- ADDMOD(a, b, 0) zero-modulus end-to-end spec.

    This generalizes `evm_addmod_b0_n0_spec_within`: the second operand may be
    arbitrary, while the modulus slot is zero. The prologue leaves `a + b` in
    the second stack slot, then the MOD zero-divisor callable stores the zero
    result in the final top slot. -/
theorem evm_addmod_n0_spec_within
    (sp base callable_base : Word)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((.x12 ↦ᵣ (sp + 64)) **
       (.x1 ↦ᵣ ((base + 124) + 4)) **
       regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b) **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchOwnCallNoX1 (sp + 32)) := by
  subst hcallable
  have hmono_prog : ∀ ad i,
      (evm_addmod_program_code base modOff) ad = some i →
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) ad = some i :=
    fun ad i h => CodeReq.union_mono_left ad i h
  have hmono_call : ∀ ad i,
      (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)) ad = some i →
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff))) ad = some i :=
    CodeReq.mono_union_right hdisjoint (fun _ _ h => h)
  have hraVal_align : ((base + 124) + 4 : Word) &&& ~~~1 = base + 128 := by
    rw [show (base + 124 : Word) + 4 = base + 128 from by bv_omega]
    exact addmod_and_not_one_eq _ (addmod_even_and_one_eq_zero base hbase)
  let sum0 := a0 + b0
  let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
  let psum1 := a1 + b1
  let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
  let result1 := psum1 + carry0
  let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
  let carry1 := carry1a ||| carry1b
  let psum2 := a2 + b2
  let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
  let result2 := psum2 + carry1
  let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
  let carry2 := carry2a ||| carry2b
  let psum3 := a3 + b3
  let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
  let result3 := psum3 + carry2
  let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
  let carry3 := carry3a ||| carry3b
  have hprologue_to_call : cpsTripleWithin (31 + 1) base ((base + 124) + signExtend21 modOff)
      ((evm_addmod_program_code base modOff).union
        (evm_mod_callable_code_v1 ((base + 124) + signExtend21 modOff)))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divModStackDispatchPreCallable (sp + 32) (a + b) (0 : EvmWord) ((base + 124) + 4)
         v2 carry3 carry3b carry3 v10 carry3a
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       evmWordIs sp a) := by
    apply cpsTripleWithin_weaken _ _ (cpsTripleWithin_extend_code (hmono := hmono_prog)
      (cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => hp)
        (cpsTripleWithin_frameR
          ((.x2 ↦ᵣ v2) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
           ((sp + 64) ↦ₘ (0 : Word)) ** ((sp + 72) ↦ₘ (0 : Word)) **
           ((sp + 80) ↦ₘ (0 : Word)) ** ((sp + 88) ↦ₘ (0 : Word)) **
             divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
               shiftMem nMem jMem retMem dMem dloMem scratchUn0)
            (by rw [divScratchValuesCallNoX1_unfold]; pcFree)
          (evm_addmod_prologue_phase1_phase2_reduce_named_spec_within
            sp base modOff a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 v5 v11 v1))))
    · intro _ hp
      rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b b0 b1 b2 b3 hb0 hb1 hb2 hb3,
          evmWordIs_sp64_limbs_eq sp (0 : EvmWord) 0 0 0 0
            (EvmWord.getLimbN_zero 0) (EvmWord.getLimbN_zero 1)
            (EvmWord.getLimbN_zero 2) (EvmWord.getLimbN_zero 3)] at hp
      xperm_hyp hp
    · intro s hpost
      exact evm_addmod_n0_dispatch_bridge_general sp base a b a0 a1 a2 a3 b0 b1 b2 b3 v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 s hpost
  have hcall_raw :=
      evm_mod_callable_bzero_v1_preserving_x1_noX9_spec
        (sp + 32) ((base + 124) + signExtend21 modOff) ((base + 124) + 4)
      (a + b) (0 : EvmWord) v2 carry3 carry3b carry3 v10 carry3a
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 rfl
  rw [hraVal_align] at hcall_raw
  have hcall :=
    cpsTripleWithin_extend_code (hmono := hmono_call)
      (cpsTripleWithin_frameR (evmWordIs sp a) (by pcFree) hcall_raw)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun s hpost => by
      rw [modStackDispatchPostCallable_unfold, EvmWord.mod_zero_right] at hpost
      rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold] at hpost
      rw [divScratchOwnCallNoX1_unfold, divScratchOwn_unfold]
      simp only [BitVec.add_assoc] at hpost ⊢
      simp only [show (32 : Word) + 32 = 64 from by bv_omega,
        show (124 : Word) + 4 = 128 from by bv_omega] at hpost ⊢
      xperm_hyp hpost)
    (cpsTripleWithin_seq_same_cr hprologue_to_call hcall)


/-- Word-level ADDMOD(a, b, 0) zero-modulus stack spec.

    This is the consumer-facing wrapper around `evm_addmod_n0_spec_within`:
    callers provide only the three stack words, not the individual limb
    equalities required by the lower-level composition theorem. -/
theorem evm_addmod_n0_stack_spec_within
    (sp base callable_base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((.x12 ↦ᵣ (sp + 64)) **
       (.x1 ↦ᵣ ((base + 124) + 4)) **
       regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b) **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchOwnCallNoX1 (sp + 32)) :=
  evm_addmod_n0_spec_within sp base callable_base a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    rfl rfl rfl rfl rfl rfl rfl rfl hcallable hbase hdisjoint


/-- Semantic zero-modulus ADDMOD stack spec.

    This restates the zero-modulus path with the public EVM result expression
    `EvmWord.addmod a b 0`, so downstream users do not need to know that the
    branch result is definitionally zero. -/
theorem evm_addmod_n0_semantic_stack_spec_within
    (sp base callable_base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) (0 : EvmWord) **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((.x12 ↦ᵣ (sp + 64)) **
       (.x1 ↦ᵣ ((base + 124) + 4)) **
       regOwn .x2 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a + b) **
       evmWordIs (sp + 64) (EvmWord.addmod a b 0) **
         divScratchOwnCallNoX1 (sp + 32)) := by
  simpa using evm_addmod_n0_stack_spec_within
    sp base callable_base a b v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint


/-- Evidence needed to take the current no-overflow ADDMOD path through the
    legacy MOD no-NOP body. This abbreviates the long carry-chain precondition
    used by `evm_addmod_no_overflow_word_mod_body_stack_spec_within`. -/
abbrev evmAddModNoOverflowBodyEvidence
    (sp base callable_base : Word) (a b N : EvmWord) (v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) : Prop :=
  let a0 := a.getLimbN 0
  let a1 := a.getLimbN 1
  let a2 := a.getLimbN 2
  let a3 := a.getLimbN 3
  let b0 := b.getLimbN 0
  let b1 := b.getLimbN 1
  let b2 := b.getLimbN 2
  let b3 := b.getLimbN 3
  let sum0 := a0 + b0
  let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
  let psum1 := a1 + b1
  let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
  let result1 := psum1 + carry0
  let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
  let carry1 := carry1a ||| carry1b
  let psum2 := a2 + b2
  let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
  let result2 := psum2 + carry1
  let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
  let carry2 := carry2a ||| carry2b
  let psum3 := a3 + b3
  let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
  let result3 := psum3 + carry2
  let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
  let carry3 := carry3a ||| carry3b
  cpsTripleWithin unifiedDivBound
    callable_base (callable_base + nopOff) (modCode_noNop callable_base)
    (divModStackDispatchPreCallable (sp + 32) (a + b) N ((base + 124) + 4)
      v2 carry3 carry3b carry3 v10 carry3a
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0)
    (modStackDispatchPostCallable (sp + 32) (a + b) N **
      (.x1 ↦ᵣ ((base + 124) + 4)))

/-- Current complete ADDMOD input domain.

    The full public stack spec must eventually cover every `(a, b, N)`. The
    theorem below currently covers either the exact zero-modulus branch, or the
    nonzero-modulus no-overflow branch when the legacy MOD body proof is
    supplied. -/
abbrev evmAddModPartialDomain
    (sp base callable_base : Word) (a b N : EvmWord) (v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) : Prop :=
  N = 0 ∨
    (a.toNat + b.toNat < 2 ^ 256 ∧
      evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)

/-- Combined partial ADDMOD stack theorem for the two currently complete
    public surfaces: the exact zero-modulus path, and the no-overflow path
    when supplied with the legacy MOD no-NOP body proof. -/
theorem evm_addmod_zero_or_no_overflow_word_mod_body_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hCase :
      N = 0 ∨
      (a.toNat + b.toNat < 2 ^ 256 ∧
        evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       evmWordIs (sp + 64) N **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnPost sp base a b N) := by
  cases hCase with
  | inl hN =>
      subst N
      have hzero := evm_addmod_n0_semantic_stack_spec_within
        sp base callable_base a b v1 v2 v5 v6 v7 v10 v11 modOff
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        hcallable hbase hdisjoint
      exact cpsTripleWithin_weaken
        (fun _ hp => hp)
        (fun _ hp => by
          rw [evmAddModNoOverflowCallReturnPost_unfold]
          xperm_hyp hp)
        hzero
  | inr hNonzero =>
      rcases hNonzero with ⟨hNoOverflow, hStack⟩
      exact evm_addmod_no_overflow_word_mod_body_stack_spec_within
        sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        hNoOverflow hcallable hbase hdisjoint hStack

/-- Stack-shaped-precondition wrapper for the current partial ADDMOD theorem.

    This keeps the existing zero-or-no-overflow domain split and scratch/callable
    assumptions, but folds the three input operands into the ordinary ternary
    EVM stack prefix `evmStackIs sp [a, b, N]`. -/
theorem evm_addmod_zero_or_no_overflow_word_mod_body_stack3_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hCase :
      N = 0 ∨
      (a.toNat + b.toNat < 2 ^ 256 ∧
        evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmStackIs sp [a, b, N] **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnPost sp base a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_triple_flat] at hp
      xperm_hyp hp)
    (fun _ hp => hp)
    (evm_addmod_zero_or_no_overflow_word_mod_body_stack_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hCase)

/-- Stack-shaped pre/post wrapper for the current partial ADDMOD theorem.

    This is still partial over the zero-or-no-overflow domain, but both the
    operand precondition and the call-return post expose ordinary EVM stack
    bundles. Scratch ownership and the legacy MOD callable assumptions remain
    explicit. -/
theorem evm_addmod_zero_or_no_overflow_word_mod_body_stack3_post_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hCase :
      N = 0 ∨
      (a.toNat + b.toNat < 2 ^ 256 ∧
        evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
       (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
       evmStackIs sp [a, b, N] **
         divScratchValuesCallNoX1 (sp + 32) q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnStackPost sp base a b N) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => evmAddModNoOverflowCallReturnPost_to_stackPost hp)
    (evm_addmod_zero_or_no_overflow_word_mod_body_stack3_spec_within
      sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      hcallable hbase hdisjoint hCase)

/-- Named-pre/named-post surface for the current partial ADDMOD theorem.

    This keeps the zero-or-no-overflow domain split explicit, but packages the
    register, operand-stack, and scratch precondition behind
    `evmAddModPartialStackPre`, and returns the folded stack post. -/
theorem evm_addmod_zero_or_no_overflow_named_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hCase :
      N = 0 ∨
      (a.toNat + b.toNat < 2 ^ 256 ∧
        evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0)) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnStackPost sp base a b N) := by
  rw [evmAddModPartialStackPre_unfold]
  exact evm_addmod_zero_or_no_overflow_word_mod_body_stack3_post_spec_within
    sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint hCase

/-- Current partial ADDMOD input domain phrased with the runtime zero-test guard.

    The first disjunct matches the OR-fold value computed by
    `evm_addmod_phase2_n_zero_test`; the second disjunct is the existing
    nonzero-modulus no-overflow body evidence. -/
abbrev evmAddModPartialOrGuardDomain
    (sp base callable_base : Word) (a b N : EvmWord) (v2 v10 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word) : Prop :=
  (N.getLimbN 0 ||| N.getLimbN 1 ||| N.getLimbN 2 ||| N.getLimbN 3 =
    (0 : Word)) ∨
    (a.toNat + b.toNat < 2 ^ 256 ∧
      evmAddModNoOverflowBodyEvidence sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)

/-- Named-domain/named-pre/named-post surface for the current partial ADDMOD
    theorem.

    This keeps the remaining incomplete region behind the single
    `evmAddModPartialDomain` predicate while exposing ordinary stack-shaped
    pre/post assertions. -/
theorem evm_addmod_partial_domain_named_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hDomain :
      evmAddModPartialDomain sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnStackPost sp base a b N) := by
  exact evm_addmod_zero_or_no_overflow_named_stack_spec_within
    sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint hDomain

/-- Runtime-guard-domain variant of
    `evm_addmod_partial_domain_named_stack_spec_within`. This lets callers use
    the OR-fold guard produced by `evm_addmod_phase2_n_zero_test` directly for
    the zero-modulus case. -/
theorem evm_addmod_partial_or_guard_named_stack_spec_within
    (sp base callable_base : Word)
    (a b N : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (modOff : BitVec 21)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hcallable : callable_base = (base + 124) + signExtend21 modOff)
    (hbase : base &&& 1 = 0)
    (hdisjoint : (evm_addmod_program_code base modOff).Disjoint
                   (evm_mod_callable_code_v1 callable_base))
    (hDomain :
      evmAddModPartialOrGuardDomain sp base callable_base a b N v2 v10
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0) :
    cpsTripleWithin ((31 + 1) + (unifiedDivBound + 1))
      base (base + 128)
      ((evm_addmod_program_code base modOff).union (evm_mod_callable_code_v1 callable_base))
      (evmAddModPartialStackPre sp a b N v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0)
      (evmAddModNoOverflowCallReturnStackPost sp base a b N) := by
  apply evm_addmod_partial_domain_named_stack_spec_within
    sp base callable_base a b N v1 v2 v5 v6 v7 v10 v11 modOff
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0
    hcallable hbase hdisjoint
  cases hDomain with
  | inl h_or =>
      exact Or.inl ((addmod_orAll_limbs_eq_zero_iff N).mp h_or)
  | inr h_body =>
      exact Or.inr h_body

-- Placeholder: full general `evm_addmod_stack_spec_within` lands in slice evm-asm-sord.

end EvmAsm.Evm64
