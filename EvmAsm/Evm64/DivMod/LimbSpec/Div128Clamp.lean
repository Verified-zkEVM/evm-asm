/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp

  CPS specs for the two q-clamp sections of the `div128` trial-division
  subroutine:
    * `divK_div128_clamp_q1_merged_spec` — Instrs [13]-[16]. SRLI test
      q1 >= 2^32, BEQ skips correction when q1 < 2^32, else ADDI
      q1-- and ADD rhat += dHi. Both branches merge at base + 16.
    * `divK_div128_clamp_q0_merged_spec` — the same shape on x5/x11 for
      q0/rhat2.

  Twenty-third chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees both
  specs.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se13_12)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 clamp q1: test q1 >= 2^32, conditionally decrement and adjust rhat.
    Instrs [13]-[16]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q1_merged_spec (q1 rhat dHi v5Old : Word) (base : Word) :
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1' := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhat' := if hi = 0 then rhat else rhat + dHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 12) (.ADD .x7 .x7 .x6))))
    cpsTriple base (base + 16) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi q1' rhat' cr
  have I0 := srli_spec_gen .x5 .x10 v5Old q1 32 base (by nofun)
  have hbody : cpsTriple base (base + 4) cr
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ v5Old) ** (.x0 ↦ᵣ 0))
      ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi) **
       (.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    runBlock I0
  have hbeq_raw := beq_spec_gen .x5 .x0 (12 : BitVec 13) hi (0 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [se13_12]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  have hbeq_framed := cpsBranch_frameR
    ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi))
    (by pcFree) hbeq_raw
  have hbeq_ext : cpsBranch (base + 4) cr
      (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi)))
      (base + 16)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi)))
      (base + 8)
        (((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  by_cases hcond : hi = 0
  · have hq : q1' = q1 := if_pos hcond
    have hr : rhat' = rhat := if_pos hcond
    rw [hq, hr]
    have taken := cpsBranch_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') taken
  · have hq : q1' = q1 + signExtend12 4095 := if_neg hcond
    have hr : rhat' = rhat + dHi := if_neg hcond
    rw [hq, hr]
    have ntaken := cpsBranch_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _ _ _).1 h_x0p).2)
    have I1 := addi_spec_gen_same .x10 q1 4095 (base + 8) (by nofun)
    have I2 := add_spec_gen_rd_eq_rs1 .x7 .x6 rhat dHi (base + 12) (by nofun)
    have hcorr : cpsTriple (base + 8) (base + 16) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi))
        ((.x10 ↦ᵣ (q1 + signExtend12 4095)) ** (.x7 ↦ᵣ (rhat + dHi)) ** (.x6 ↦ᵣ dHi)) := by
      runBlock I1 I2
    have hcorr_framed := cpsTriple_frameR
      ((.x5 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) hcorr
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr_framed
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full

/-- div128 clamp q0: test q0 >= 2^32, conditionally decrement and adjust rhat2.
    Instrs [33]-[36]. Both BEQ paths merge at base+16. -/
theorem divK_div128_clamp_q0_merged_spec (q0 rhat2 dHi v1Old : Word) (base : Word) :
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0' := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2' := if hi = 0 then rhat2 else rhat2 + dHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 8) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 12) (.ADD .x11 .x11 .x6))))
    cpsTriple base (base + 16) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
       (.x1 ↦ᵣ v1Old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ dHi) **
       (.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
  intro hi q0' rhat2' cr
  have hbody : cpsTriple base (base + 4) cr
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
       (.x1 ↦ᵣ v1Old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi) **
       (.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ 0)) := by
    have I0 := srli_spec_gen .x1 .x5 v1Old q0 32 base (by nofun)
    runBlock I0
  have hbeq_raw := beq_spec_gen .x1 .x0 (12 : BitVec 13) hi (0 : Word) (base + 4)
  have ha_t : (base + 4) + signExtend13 (12 : BitVec 13) = base + 16 := by rw [se13_12]; bv_addr
  have ha_f : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [ha_t, ha_f] at hbeq_raw
  have hbeq_framed := cpsBranch_frameR
    ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi))
    (by pcFree) hbeq_raw
  have hbeq_ext : cpsBranch (base + 4) cr
      (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word))) **
       ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi)))
      (base + 16)
        (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi = 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi)))
      (base + 8)
        (((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜hi ≠ 0⌝) **
         ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi))) :=
    fun R hR s hcr hPR hpc =>
      hbeq_framed R hR s ((CodeReq.singleton_satisfiedBy _ _ s).mpr (hcr _ _ (by
        show cr (base + 4) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 4 = base) := by bv_omega
        simp only [beq_iff_eq, h0, ↓reduceIte]))) hPR hpc
  have composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_ext
  by_cases hcond : hi = 0
  · have hq : q0' = q0 := if_pos hcond
    have hr : rhat2' = rhat2 := if_pos hcond
    rw [hq, hr]
    have taken := cpsBranch_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _ _ _).1 h_x0p).2 hcond)
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') taken
  · have hq : q0' = q0 + signExtend12 4095 := if_neg hcond
    have hr : rhat2' = rhat2 + dHi := if_neg hcond
    rw [hq, hr]
    have ntaken := cpsBranch_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact hcond ((sepConj_pure_right _ _ _).1 h_x0p).2)
    have I1 := addi_spec_gen_same .x5 q0 4095 (base + 8) (by nofun)
    have I2 := add_spec_gen_rd_eq_rs1 .x11 .x6 rhat2 dHi (base + 12) (by nofun)
    have hcorr : cpsTriple (base + 8) (base + 16) cr
        ((.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) ** (.x6 ↦ᵣ dHi))
        ((.x5 ↦ᵣ (q0 + signExtend12 4095)) ** (.x11 ↦ᵣ (rhat2 + dHi)) ** (.x6 ↦ᵣ dHi)) := by
      runBlock I1 I2
    have hcorr_framed := cpsTriple_frameR
      ((.x1 ↦ᵣ hi) ** (.x0 ↦ᵣ (0 : Word)))
      (by pcFree) hcorr
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right _ _ h').1 hp').1)) h hp
        xperm_hyp hp') ntaken hcorr_framed
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full

end EvmAsm.Evm64
