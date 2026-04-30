/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1

  CPS spec for instrs [17]-[24] of the `div128` subroutine — the first
  product-check section:
    * `divK_div128_prodcheck1_merged_spec_within` — 8 instructions: LD + MUL +
      SLLI + OR (body) + BLTU + JAL (branch) + ADDI + ADD (correction).
      If `rhat*2^32 + un1 < q1*dLo`, BLTU takes the correction path
      (`q1--`, `rhat += dHi`); otherwise JAL skips both adjustments.
      Both branches merge at `base + 32`.

  Twenty-fourth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se21_12)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 product check 1: compute q1*dLo vs rhat*2^32+un1, conditionally correct.
    Instrs [17]-[24]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck1_merged_spec_within
    (sp q1 rhat dHi un1 v1Old v5Old dlo : Word) (base : Word) :
    let qDlo := q1 * dlo
    let rhatUn1 := (rhat <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1 + signExtend12 4095 else q1
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhat + dHi else rhat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 20) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))))))))
    cpsTripleWithin 8 base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
  intro qDlo rhatUn1 q1' rhat' cr
  have hbody : cpsTripleWithin 4 base (base + 16) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
    have I0 := ld_spec_gen_within .x1 .x12 sp v1Old dlo 3952 base (by nofun)
    have I1 := mul_spec_gen_within .x5 .x10 .x1 v5Old q1 dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen_within .x1 .x7 dlo rhat 32 (base + 8) (by nofun)
    have I3 := or_spec_gen_rd_eq_rs1_within .x1 .x11 (rhat <<< (32 : BitVec 6).toNat) un1 (base + 12) (by nofun)
    runBlock I0 I1 I2 I3
  have hbltu_raw := bltu_spec_gen_within .x1 .x5 (8 : BitVec 13) rhatUn1 qDlo (base + 16)
  have ha_t : (base + 16) + signExtend13 (8 : BitVec 13) = base + 24 := by rv64_addr
  have ha_f : (base + 16 : Word) + 4 = base + 20 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  have hbltu_framed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
     (.x6 ↦ᵣ dHi) ** (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) hbltu_raw
  have hbltu_ext : cpsBranchWithin 1 (base + 16) cr
      (((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo)) **
       ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
        (.x6 ↦ᵣ dHi) ** (sp + signExtend12 3952 ↦ₘ dlo)))
      (base + 24)
        (((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo) ** ⌜BitVec.ult rhatUn1 qDlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
          (.x6 ↦ᵣ dHi) ** (sp + signExtend12 3952 ↦ₘ dlo)))
      (base + 20)
        (((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo) ** ⌜¬BitVec.ult rhatUn1 qDlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
          (.x6 ↦ᵣ dHi) ** (sp + signExtend12 3952 ↦ₘ dlo))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s (CodeReq.singleton_satisfiedBy.mpr (hcr _ _ (by
        show cr (base + 16) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 16 = base) := by bv_omega
        have h1 : ¬(base + 16 = base + 4) := by bv_omega
        have h2 : ¬(base + 16 = base + 8) := by bv_omega
        have h3 : ¬(base + 16 = base + 12) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, ↓reduceIte]))) hPR hpc
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  by_cases hcond : BitVec.ult rhatUn1 qDlo
  · have hq : q1' = q1 + signExtend12 4095 := if_pos hcond
    have hr : rhat' = rhat + dHi := if_pos hcond
    rw [hq, hr]
    have taken_br := cpsBranchWithin_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_x0p).2 hcond)
    have I4 := addi_spec_gen_same_within .x10 q1 4095 (base + 24) (by nofun)
    have I5 := add_spec_gen_rd_eq_rs1_within .x7 .x6 rhat dHi (base + 28) (by nofun)
    have hcorr : cpsTripleWithin 2 (base + 24) (base + 32) cr
        ((.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x6 ↦ᵣ dHi))
        ((.x10 ↦ᵣ (q1 + signExtend12 4095)) ** (.x7 ↦ᵣ (rhat + dHi)) ** (.x6 ↦ᵣ dHi)) := by
      runBlock I4 I5
    have hcorr_framed := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un1) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) hcorr
    have full := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp')
      taken_br hcorr_framed
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
  · have hq : q1' = q1 := if_neg hcond
    have hr : rhat' = rhat := if_neg hcond
    rw [hq, hr]
    have ntaken_br := cpsBranchWithin_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 h_x0p).2 hcond)
    have I_jal := jal_x0_spec_gen_within 12 (base + 20)
    rw [se21_12] at I_jal
    have ha_jal : (base + 20 : Word) + 12 = base + 32 := by bv_addr
    rw [ha_jal] at I_jal
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 20) (.JAL .x0 12) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have I_jal_cr := cpsTripleWithin_extend_code hcr_jal I_jal
    have hjal_framed := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo) ** (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) **
       (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (by pcFree) I_jal_cr
    simp only [sepConj_emp_left'] at hjal_framed
    have ntaken_clean : cpsTripleWithin 5 base (base + 20) cr
        ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
         (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) **
         (sp + signExtend12 3952 ↦ₘ dlo))
        ((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo) **
         (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
         (.x6 ↦ᵣ dHi) ** (sp + signExtend12 3952 ↦ₘ dlo)) :=
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          have hp' : (((.x1 ↦ᵣ rhatUn1) ** (.x5 ↦ᵣ qDlo)) **
            ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1) ** (.x7 ↦ᵣ rhat) ** (.x11 ↦ᵣ un1) **
             (.x6 ↦ᵣ dHi) ** (sp + signExtend12 3952 ↦ₘ dlo))) h :=
            sepConj_mono_left (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp')
        ntaken_br
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => hp)
        ntaken_clean hjal_framed)

end EvmAsm.Evm64
