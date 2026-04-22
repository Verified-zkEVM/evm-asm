/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

  CPS spec for instrs [37]-[44] of the `div128` subroutine — the second
  product-check section:
    * `divK_div128_prodcheck2_merged_spec` — 8 instructions: LD + MUL +
      SLLI + LD + OR (body) + BLTU + JAL (branch) + ADDI (correction).
      If `rhat2*2^32 + un0 < q0*dLo`, BLTU takes the correction path
      (ADDI `q0--`); otherwise JAL skips the correction. Both branches
      merge at `base + 32`. Note there's only one correction instruction
      here (no rhat2 update, unlike product check 1).

  Twenty-fifth chunk of the `LimbSpec.lean` split tracked by issue #312.
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
open EvmAsm.Rv64.AddrNorm (se21_8)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase 2b refined quotient digit in `div128Quot`.

    Factored standalone so the Knuth TAOCP §4.3.1 Step D3 guard
    (`rhat2c < 2^32`) can be added in a follow-up iteration without
    rewriting the entire `div128Quot` body. **Currently matches legacy
    (buggy) semantics**; the bug is documented at
    `/home/zksecurity/.claude/plans/dynamic-strolling-riddle.md`.

    Lives in `Div128ProdCheck2.lean` (the lowest-level file that
    naturally talks about Phase 2b's mul-check). Visible from
    `LimbSpec.Div128Step2`, `Compose/Base` (transitively via `LimbSpec`),
    and `LoopDefs.Iter` (where `div128Quot` calls it). -/
def div128Quot_phase2b_q0' (q0c rhat2c dLo div_un0 : Word) : Word :=
  let q0Dlo := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
  if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c

/-- Phase 2b guard: 2-instruction cpsBranch that skips the Phase 2b mul-check
    when `rhat2c ≥ 2^32`. Per Knuth TAOCP §4.3.1 Step D3 ("repeat this test
    if r̂ < b") — when `rhat2c ≥ 2^32`, the 64-bit `<< 32` in `rhat2Un0`
    truncates, so the downstream `BLTU` mul-check would false-positively
    fire; this guard dispatches past the mul-check entirely in that case.

    Assembly:
    ```
    [0] SRLI .x1 .x11 32       -- x1 = rhat2c >> 32
    [4] BNE  .x1 .x0 guard_off -- if nonzero, branch past mul-check
    ```

    Branches:
    - **Taken** (rhat2c_hi ≠ 0, guard fires): branches to `(base+4) +
      signExtend13 guard_off`. Mul-check skipped.
    - **Fall-through** (rhat2c_hi = 0): continues to `base + 8`, Phase 2b
      mul-check runs normally.

    Used by `divK_div128_step2_guarded_spec` (future) to compose
    clamp_q0 + guard + prodcheck2 into a 17-instruction step2 block. -/
theorem divK_div128_phase2b_guard_spec
    (sp rhat2c v1Old : Word) (base : Word) (guard_off : BitVec 13) :
    let rhat2c_hi := rhat2c >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x11 32))
        (CodeReq.singleton (base + 4) (.BNE .x1 .x0 guard_off))
    cpsBranch base cr
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ v1Old) ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 guard_off)
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2c_hi) **
         (.x0 ↦ᵣ 0) ** ⌜rhat2c_hi ≠ 0⌝)
      (base + 8)
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2c_hi) **
         (.x0 ↦ᵣ 0) ** ⌜rhat2c_hi = 0⌝) := by
  intro rhat2c_hi cr
  -- Step 1: SRLI .x1 .x11 32  (cpsTriple base → base+4)
  have hsrli_raw := srli_spec_gen .x1 .x11 v1Old rhat2c 32 base (by nofun)
  -- Extend to the full cr (which includes the BNE).
  have hcr_srli : ∀ a i,
      CodeReq.singleton base (.SRLI .x1 .x11 32) a = some i → cr a = some i := by
    intro a i h
    simp only [cr, CodeReq.union, CodeReq.singleton] at h ⊢
    split at h
    · rename_i hab; simp_all
    · simp at h
  have hsrli := cpsTriple_extend_code hcr_srli hsrli_raw
  have hsrli_framed := cpsTriple_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0))
    (by pcFree) hsrli
  -- Step 2: BNE .x1 .x0 guard_off  (cpsBranch base+4 → ...)
  have hbne_raw := bne_spec_gen .x1 .x0 guard_off rhat2c_hi (0 : Word) (base + 4)
  have hcr_bne : ∀ a i,
      CodeReq.singleton (base + 4) (.BNE .x1 .x0 guard_off) a = some i → cr a = some i := by
    intro a i h
    simp only [cr, CodeReq.union, CodeReq.singleton] at h ⊢
    split at h
    · rename_i hab; rw [beq_iff_eq] at hab; subst hab
      have : (base + 4 : Word) ≠ base := by bv_omega
      simp_all
    · simp at h
  have hbne := cpsBranch_extend_code hcr_bne hbne_raw
  have hbne_framed := cpsBranch_frameR
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c))
    (by pcFree) hbne
  -- Compose SRLI (cpsTriple) + BNE (cpsBranch).
  have composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsrli_framed hbne_framed
  -- Weaken to the stated pre/post shapes (atom permutation, `base + 4 + 4 = base + 8`).
  have h_addr_eq : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [h_addr_eq] at composed
  exact cpsBranch_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

/-- div128 product check 2: compute q0*dLo vs rhat2*2^32+un0, conditionally correct q0.
    Instrs [37]-[44]. Both BLTU paths merge at base+32. -/
theorem divK_div128_prodcheck2_merged_spec
    (sp q0 rhat2 v1Old v7Old dlo un0 : Word) (base : Word) :
    let q0Dlo := q0 * dlo
    let rhat2Un0 := (rhat2 <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := div128Quot_phase2b_q0' q0 rhat2 dlo un0
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 16) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 20) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 24) (.JAL .x0 8))
       (CodeReq.singleton (base + 28) (.ADDI .x5 .x5 4095))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7Old) ** (.x1 ↦ᵣ v1Old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0Dlo) ** (.x1 ↦ᵣ rhat2Un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0Dlo rhat2Un0 q0' cr
  have hbody : cpsTriple base (base + 20) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
       (.x7 ↦ᵣ v7Old) ** (.x1 ↦ᵣ v1Old) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
       (.x7 ↦ᵣ q0Dlo) ** (.x1 ↦ᵣ rhat2Un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
    have I0 := ld_spec_gen .x1 .x12 sp v1Old dlo 3952 base (by nofun)
    have I1 := mul_spec_gen .x7 .x5 .x1 v7Old q0 dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen .x1 .x11 dlo rhat2 32 (base + 8) (by nofun)
    have I3 := ld_spec_gen .x11 .x12 sp rhat2 un0 3944 (base + 12) (by nofun)
    have I4 := or_spec_gen_rd_eq_rs1 .x1 .x11 (rhat2 <<< (32 : BitVec 6).toNat) un0 (base + 16) (by nofun)
    runBlock I0 I1 I2 I3 I4
  have hbltu_raw := bltu_spec_gen .x1 .x7 (8 : BitVec 13) rhat2Un0 q0Dlo (base + 20)
  have ha_t : (base + 20) + signExtend13 (8 : BitVec 13) = base + 28 := by rv64_addr
  have ha_f : (base + 20 : Word) + 4 = base + 24 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  have hbltu_framed := cpsBranch_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) hbltu_raw
  have hbltu_ext : cpsBranch (base + 20) cr
      (((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo)) **
       ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)))
      (base + 28)
        (((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo) ** ⌜BitVec.ult rhat2Un0 q0Dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)))
      (base + 24)
        (((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo) ** ⌜¬BitVec.ult rhat2Un0 q0Dlo⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s (CodeReq.singleton_satisfiedBy.mpr (hcr _ _ (by
        show cr (base + 20) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 20 = base) := by bv_omega
        have h1 : ¬(base + 20 = base + 4) := by bv_omega
        have h2 : ¬(base + 20 = base + 8) := by bv_omega
        have h3 : ¬(base + 20 = base + 12) := by bv_omega
        have h4 : ¬(base + 20 = base + 16) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, h4, ↓reduceIte]))) hPR hpc
  have composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  by_cases hcond : BitVec.ult rhat2Un0 q0Dlo
  · have hq : q0' = q0 + signExtend12 4095 := if_pos hcond
    rw [hq]
    have taken_br := cpsBranch_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_x0p).2 hcond)
    have I5 := addi_spec_gen_same .x5 q0 4095 (base + 28) (by nofun)
    have hcorr : cpsTriple (base + 28) (base + 32) cr
        (.x5 ↦ᵣ q0)
        (.x5 ↦ᵣ (q0 + signExtend12 4095)) := by
      runBlock I5
    have hcorr_framed := cpsTriple_frameR
      ((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo) ** (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) hcorr
    have full := cpsTriple_seq_perm_same_cr
      (fun h hp => by
        have hp' := sepConj_mono_left (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
        xperm_hyp hp')
      taken_br hcorr_framed
    exact cpsTriple_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp) full
  · have hq : q0' = q0 := if_neg hcond
    rw [hq]
    have ntaken_br := cpsBranch_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_x0p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 h_x0p).2 hcond)
    have I_jal := jal_x0_spec_gen 8 (base + 24)
    rw [se21_8] at I_jal
    have ha_jal : (base + 24 : Word) + 8 = base + 32 := by bv_addr
    rw [ha_jal] at I_jal
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 24) (.JAL .x0 8) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have I_jal_cr := cpsTriple_extend_code hcr_jal I_jal
    have hjal_framed := cpsTriple_frameR
      ((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo) ** (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) **
       (.x11 ↦ᵣ un0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) I_jal_cr
    simp only [sepConj_emp_left'] at hjal_framed
    have ntaken_clean : cpsTriple base (base + 24) cr
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ rhat2) **
         (.x7 ↦ᵣ v7Old) ** (.x1 ↦ᵣ v1Old) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
        ((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo) **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) :=
      cpsTriple_weaken
        (fun h hp => hp)
        (fun h hp => by
          have hp' : (((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo)) **
            ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0) ** (.x11 ↦ᵣ un0) **
             (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))) h :=
            sepConj_mono_left (sepConj_mono_right
              (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp')
        ntaken_br
    exact cpsTriple_weaken
      (fun _ hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_seq_perm_same_cr
        (fun _ hp => hp)
        ntaken_clean hjal_framed)

end EvmAsm.Evm64
