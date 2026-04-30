/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2

  Full-step composition for instrs [30]-[46] of the `div128` subroutine —
  combining step-2-init (DIVU+MUL+SUB), clamp-q0 (SRLI+BEQ+ADDI+ADD),
  Phase 2b guard (SRLI+BNE — Knuth TAOCP §4.3.1 Step D3), and prodcheck2
  (LD+MUL+SLLI+LD+OR + BLTU+JAL + ADDI) into a single refined `q0`
  computation for the low 64 bits.

  Thirtieth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

-- Each of the three `Div128*` sub-file imports below transitively brings
-- `DivMod.Program`, `Rv64.SyscallSpecs`, `Rv64.ControlFlow`,
-- `Rv64.Tactics.XSimp`, `Rv64.Tactics.RunBlock`.
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 step 2 upto-guard: init + clamp_q0 composition for instrs [30]-[36].
    Output at base+28 with x5=q0c, x11=rhat2c, x1=hi ready for the Phase 2b
    guard to consume.

    Note: proof pattern matches the pre-guard (main-branch) step2_spec's first
    two sub-specs; this sub-lemma exists so the full `divK_div128_step2_spec_within`
    can compose it with the new `phase2b_guard_spec` + `prodcheck2_merged_spec`
    without re-stating the init/clamp code subsumption every time. -/
theorem divK_div128_step2_upto_guard_spec_within
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6)))))))
    cpsTripleWithin 7 base (base + 28) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
       (.x1 ↦ᵣ hi) ** (.x11 ↦ᵣ rhat2c) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
       (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))))))) := rfl
  have h1_raw := divK_div128_step2_init_spec_within un21 dHi v1Old v5Old v11Old base
  have h1 : cpsTripleWithin 3 base (base + 12) cr _ _ :=
    cpsTripleWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail
        (CodeReq.union_mono_left _ _)))
  have h1f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  have h2_raw := divK_div128_clamp_q0_merged_spec_within q0 rhat2 dHi (q0 * dHi) (base + 12)
  have ha4 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have ha8 : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have ha12 : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have ha16 : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [ha4, ha8, ha12, ha16] at h2_raw
  have h2 : cpsTripleWithin 4 (base + 12) (base + 28) cr _ _ :=
    cpsTripleWithin_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · simp at h)
  have h2f := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ un21) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1f h2f
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h12

/-- div128 step 2 thru-guard: init + clamp_q0 + phase2b_guard composition
    for instrs [30]-[38]. Produces a cpsBranchWithin at base+28 that either takes
    the taken path to base+68 (skipping mul-check when rhat2cHi ≠ 0) or
    falls through to base+36 (rhat2cHi = 0) where mul-check will run. -/
theorem divK_div128_step2_thru_guard_spec_within
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
       (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36)))))))))
    cpsBranchWithin 9 base cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (base + 68)
        ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
         (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi ≠ 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (base + 36)
        ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
         (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c rhat2cHi cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
       (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))))))))) := rfl
  -- h1 = step2_upto_guard_spec (cpsTripleWithin base..base+28, 7-singleton cr).
  -- Its cr is a STRUCTURAL PREFIX of thru_guard's cr: same 7 singletons,
  -- ending in `singleton (base+24) ADD` vs thru_guard's `union (sing 24 ADD)
  -- (union (sing 28 SRLI) (sing 32 BNE))`. So 6 union_mono_tails + 1
  -- union_mono_left (peeling sing 24 ADD from the head).
  have h1_raw := divK_div128_step2_upto_guard_spec_within sp un21 dHi v1Old v5Old v11Old
    dlo un0 base
  have h1 : cpsTripleWithin 7 base (base + 28) cr _ _ :=
    cpsTripleWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]
      exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_tail
        (CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_tail
        (CodeReq.union_mono_left _ _)))))))
  -- h2 = phase2b_guard_spec at base+28 (2-singleton cr).
  have h2_raw := divK_div128_phase2b_guard_spec_within sp rhat2c hi (base + 28) (36 : BitVec 13)
  have ha_bne : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  have ha_t : (base + 32 : Word) + signExtend13 (36 : BitVec 13) = base + 68 := by rv64_addr
  have ha_f : (base + 28 : Word) + 8 = base + 36 := by bv_addr
  simp only [ha_bne, ha_t, ha_f] at h2_raw
  -- phase2b_guard's 2-singleton cr is the innermost pair of thru_guard's 9-cr.
  -- Use split+simp pattern (only 2 levels deep, bounded heartbeats).
  have h2 : cpsBranchWithin 2 (base + 28) cr _ _ _ _ _ :=
    cpsBranchWithin_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · simp at h)
  have h2f := cpsBranchWithin_frameR
    ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h2
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1 h2f
  exact cpsBranchWithin_weaken
    (fun h hp => hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

/-- div128 step 2 branch-merged: composes thru_guard + prodcheck2_merged into
    a cpsBranchWithin where BOTH legs end at base+68 (guard-fires skips directly;
    guard-doesn't-fire runs the mul-check). -/
theorem divK_div128_step2_branch_merged_spec_within
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
    let q0Dlo := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let q0'Unguarded := if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 40) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 56) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 60) (.JAL .x0 8))
       (CodeReq.singleton (base + 64) (.ADDI .x5 .x5 4095)))))))))))))))))
    cpsBranchWithin 17 base cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (base + 68)  -- guard-fires path
        ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
         (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi ≠ 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (base + 68)  -- guard-doesn't-fire + prodcheck2 (carries ⌜rhat2cHi = 0⌝)
        ((.x7 ↦ᵣ q0Dlo) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0'Unguarded) **
         (.x1 ↦ᵣ rhat2Un0) ** (.x11 ↦ᵣ un0) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c q0Dlo rhat2Un0 rhat2cHi q0'Unguarded cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 40) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 56) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 60) (.JAL .x0 8))
       (CodeReq.singleton (base + 64) (.ADDI .x5 .x5 4095))))))))))))))))) := rfl
  -- h1 = thru_guard_spec (cpsBranchWithin base..base+68|base+36, 9-singleton cr).
  -- Its cr is a STRUCTURAL PREFIX of branch_merged's 17-cr: same 8 outer unions,
  -- innermost differs (thru_guard = sing 32 BNE, branch_merged = union (sing 32 BNE) REST).
  -- So 8 union_mono_tails + 1 union_mono_left.
  have h1_raw := divK_div128_step2_thru_guard_spec_within sp un21 dHi v1Old v5Old v11Old
    dlo un0 base
  have h1 : cpsBranchWithin 9 base cr _ _ _ _ _ :=
    cpsBranchWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]
      exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_tail
        (CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_tail
        (CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left _ _)))))))))
  -- h2 = prodcheck2_merged_spec at base+36 (8-singleton cr, positions 9-16
  -- of the 17-cr). Use split+simp pattern (8 levels deep but each level is
  -- cheap — heads don't match the prodcheck2 cr's head).
  have h2_raw := divK_div128_prodcheck2_merged_spec_within sp q0c rhat2c rhat2cHi un21
    dlo un0 (base + 36)
  have hb4 : (base + 36 : Word) + 4 = base + 40 := by bv_addr
  have hb8 : (base + 36 : Word) + 8 = base + 44 := by bv_addr
  have hb12 : (base + 36 : Word) + 12 = base + 48 := by bv_addr
  have hb16 : (base + 36 : Word) + 16 = base + 52 := by bv_addr
  have hb20 : (base + 36 : Word) + 20 = base + 56 := by bv_addr
  have hb24 : (base + 36 : Word) + 24 = base + 60 := by bv_addr
  have hb28 : (base + 36 : Word) + 28 = base + 64 := by bv_addr
  have hb32 : (base + 36 : Word) + 32 = base + 68 := by bv_addr
  simp only [hb4, hb8, hb12, hb16, hb20, hb24, hb28, hb32] at h2_raw
  -- prodcheck2's 8-cr ⊆ 17-cr: use split+simp pattern (8 levels, matching
  -- the old pre-guard step2 proof's pattern for the prodcheck block).
  have h2 : cpsTripleWithin 8 (base + 36) (base + 68) cr _ _ :=
    cpsTripleWithin_extend_code (h := h2_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
        · split at h
          · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
          · split at h
            · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
            · split at h
              · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
              · split at h
                · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                · split at h
                  · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                  · split at h
                    · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left, CodeReq.beq_base_offset]
                    · simp at h)
  -- Frame h2 with (x6, x0) and ⌜rhat2cHi = 0⌝ so the pure fact is carried
  -- through the composition and ends up in branch_merged's fall-through post.
  have h2f := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝)
    (by pcFree) h2
  -- hperm: permute thru_guard's Q_f (incl. pure fact) to h2f's pre order.
  have composed := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    (h1 := h1)
    (hperm := fun h hp => by xperm_hyp hp)
    (h2 := h2f)
    (ht1 := fun h hp => hp)
  -- Reshape h2f's left-associated post to our natural right-associated post.
  exact cpsBranchWithin_weaken
    (fun h hp => hp)
    (fun h hp => hp)  -- Q_t unchanged
    (fun h hp => by xperm_hyp hp)  -- Q_f_final reshaped
    composed

/-- Bundled postcondition for `divK_div128_step2_spec_within`. Hides the
    13-let chain (Step 2 trial-division intermediates + Phase 2b
    exit selectors) so the theorem signature stays a clean
    `cpsTripleWithin A B cr P (divKDiv128Step2Post …)` instead of a
    let-chain immediately preceding the triple. Marked
    `@[irreducible]` so callers see only the bundled assertion;
    `unfold` to expose the lets when bridging downstream. Part of #1139. -/
@[irreducible]
def divKDiv128Step2Post (sp un21 dHi dlo un0 : Word) : Assertion :=
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dlo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let x11Exit := if rhat2cHi = 0 then un0 else rhat2c
  (.x7 ↦ᵣ x7Exit) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
  (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- Bundled CodeReq for `divK_div128_step2_spec_within` (instrs [30]-[46], 17
    singletons). Bundling avoids the let in the theorem signature. -/
@[irreducible]
def divKDiv128Step2Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
  (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x1 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 40) (.MUL .x7 .x5 .x1))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SLLI .x1 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x11 .x12 3944))
  (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x1 .x1 .x11))
  (CodeReq.union (CodeReq.singleton (base + 56) (.BLTU .x1 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 60) (.JAL .x0 8))
   (CodeReq.singleton (base + 64) (.ADDI .x5 .x5 4095)))))))))))))))))

/-- div128 step 2: trial division q0, clamp, Phase 2b guard, product check.
    Instrs [30]-[46] (17 instructions). Includes the Knuth TAOCP §4.3.1
    Step D3 guard (SRLI + BNE at instrs [37]-[38]) that skips the
    product check when `rhat2c >= 2^32`.

    Input: un21 in x7, dHi in x6, dlo/un0 in memory.
    Output: refined q0 in x5 (= `div128Quot_phase2b_q0' q0c rhat2c dlo un0`).

    Postcondition is bundled as `divKDiv128Step2Post`; the per-register
    breakdown is in that def's body. Bundling addresses the "many lets
    before cpsTripleWithin" elaboration anti-pattern (#1139). -/
theorem divK_div128_step2_spec_within
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    cpsTripleWithin 17 base (base + 68) (divKDiv128Step2Code base)
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (divKDiv128Step2Post sp un21 dHi dlo un0) := by
  unfold divKDiv128Step2Code divKDiv128Step2Post
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let q0Dlo := q0c * dlo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let x7Exit := if rhat2cHi = 0 then q0Dlo else un21
  let x1Exit := if rhat2cHi = 0 then rhat2Un0 else rhat2cHi
  let x11Exit := if rhat2cHi = 0 then un0 else rhat2c
  let cr :=
    CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
    (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
    (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
    (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
    (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
    (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
    (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
    (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
    (CodeReq.union (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))
    (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x1 .x12 3952))
    (CodeReq.union (CodeReq.singleton (base + 40) (.MUL .x7 .x5 .x1))
    (CodeReq.union (CodeReq.singleton (base + 44) (.SLLI .x1 .x11 32))
    (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x11 .x12 3944))
    (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x1 .x1 .x11))
    (CodeReq.union (CodeReq.singleton (base + 56) (.BLTU .x1 .x7 8))
    (CodeReq.union (CodeReq.singleton (base + 60) (.JAL .x0 8))
     (CodeReq.singleton (base + 64) (.ADDI .x5 .x5 4095)))))))))))))))))
  -- Apply branch_merged to get a cpsBranchWithin with both legs at base+68.
  have hbr := divK_div128_step2_branch_merged_spec_within sp un21 dHi v1Old v5Old v11Old
    dlo un0 base
  -- Target post as a local assertion.
  let tgtPost : Assertion :=
    (.x7 ↦ᵣ x7Exit) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
    (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)
  -- Helper: cpsTripleWithin_refl at base+68 is a zero-step identity triple; we
  -- extend it from empty cr to our cr (vacuous) and use it for both branches.
  have refl_of {P : Assertion} (h : ∀ hp, P hp → tgtPost hp) :
      cpsTripleWithin 0 (base + 68) (base + 68) cr P tgtPost :=
    cpsTripleWithin_extend_code (fun _ _ h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_refl h)
  -- Bridge for taken path (rhat2cHi ≠ 0): strip pure fact, rewrite x7/x1/x11
  -- exits to un21/rhat2cHi/rhat2c, rewrite q0' to q0c via helper unfolding.
  have h_t : cpsTripleWithin 0 (base + 68) (base + 68) cr _ tgtPost := refl_of (P :=
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi ≠ 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) (by
    intro hp hP
    have h_hi_ne : rhat2cHi ≠ 0 := by
      -- Extract ⌜rhat2cHi ≠ 0⌝ from position 7 in the sepConj chain.
      obtain ⟨_, _, _, _, _, hrest⟩ := hP
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, ⟨_, hpure⟩, _⟩ := hrest
      exact hpure
    have hq0' : q0' = q0c := by
      show div128Quot_phase2b_q0' q0c rhat2c dlo un0 = q0c
      unfold div128Quot_phase2b_q0'
      exact if_neg h_hi_ne
    have hx7 : x7Exit = un21 := if_neg h_hi_ne
    have hx1 : x1Exit = rhat2cHi := if_neg h_hi_ne
    have hx11 : x11Exit = rhat2c := if_neg h_hi_ne
    show tgtPost hp
    show ((.x7 ↦ᵣ x7Exit) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
         (sp + signExtend12 3952 ↦ₘ dlo) **
         (sp + signExtend12 3944 ↦ₘ un0)) hp
    rw [hq0', hx7, hx1, hx11]
    -- Strip the pure fact and permute.
    have hP' : ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
                (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
                (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
                (sp + signExtend12 3952 ↦ₘ dlo) **
                (sp + signExtend12 3944 ↦ₘ un0)) hp :=
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_left h').1 hp').2))))))) hp hP
    xperm_hyp hP')
  -- Bridge for fall-through path: the post carries ⌜rhat2cHi = 0⌝ so we
  -- can extract it and rewrite the exit selectors to their then-branch values.
  have h_f : cpsTripleWithin 0 (base + 68) (base + 68) cr _ tgtPost := refl_of (P :=
    (.x7 ↦ᵣ q0Dlo) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ
      (if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c)) **
    (.x1 ↦ᵣ rhat2Un0) ** (.x11 ↦ᵣ un0) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) (by
    intro hp hP
    have h_hi_eq : rhat2cHi = 0 := by
      -- Extract ⌜rhat2cHi = 0⌝ from position 7 in the sepConj chain.
      obtain ⟨_, _, _, _, _, hrest⟩ := hP
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, ⟨_, hpure⟩, _⟩ := hrest
      exact hpure
    have hq0' : q0' = (if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c) := by
      show div128Quot_phase2b_q0' q0c rhat2c dlo un0 = _
      unfold div128Quot_phase2b_q0'
      rw [if_pos h_hi_eq]
    have hx7 : x7Exit = q0Dlo := if_pos h_hi_eq
    have hx1 : x1Exit = rhat2Un0 := if_pos h_hi_eq
    have hx11 : x11Exit = un0 := if_pos h_hi_eq
    show ((.x7 ↦ᵣ x7Exit) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
         (sp + signExtend12 3952 ↦ₘ dlo) **
         (sp + signExtend12 3944 ↦ₘ un0)) hp
    rw [hq0', hx7, hx1, hx11]
    -- Strip the pure fact and permute remaining atoms.
    have hP' : ((.x7 ↦ᵣ q0Dlo) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ
                (if BitVec.ult rhat2Un0 q0Dlo then q0c + signExtend12 4095 else q0c)) **
                (.x1 ↦ᵣ rhat2Un0) ** (.x11 ↦ᵣ un0) **
                (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
                (sp + signExtend12 3952 ↦ₘ dlo) **
                (sp + signExtend12 3944 ↦ₘ un0)) hp :=
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (fun h' hp' => ((sepConj_pure_left h').1 hp').2))))))) hp hP
    xperm_hyp hP')
  exact cpsBranchWithin_merge_same_cr hbr h_t h_f

end EvmAsm.Evm64
