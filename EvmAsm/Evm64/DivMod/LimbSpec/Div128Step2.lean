/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2

  Full-step composition for instrs [30]-[44] of the `div128` subroutine —
  combining step-2-init (DIVU+MUL+SUB), clamp-q0 (SRLI+BEQ+ADDI+ADD),
  and prodcheck2 (LD+MUL+SLLI+LD+OR + BLTU+JAL + ADDI) into a single
  refined `q0` computation for the low 64 bits.

  Thirtieth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 step 2: trial division q0, clamp, product check. Instrs [30]-[44].
    Input: un21 in x7, d_hi in x6, dlo/un0 in memory.
    Output: refined q0 in x5. -/
theorem divK_div128_step2_spec
    (sp un21 d_hi v1_old v5_old v11_old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 d_hi
    let rhat2 := un21 - q0 * d_hi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + d_hi
    let q0_dlo := q0c * dlo
    let rhat2_un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2_un0 q0_dlo then q0c + signExtend12 4095 else q0c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 52) (.JAL .x0 8))
       (CodeReq.singleton (base + 56) (.ADDI .x5 .x5 4095)))))))))))))))
    cpsTriple base (base + 60) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ d_hi) ** (.x5 ↦ᵣ v5_old) **
       (.x1 ↦ᵣ v1_old) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ q0_dlo) ** (.x6 ↦ᵣ d_hi) ** (.x5 ↦ᵣ q0') **
       (.x1 ↦ᵣ rhat2_un0) ** (.x11 ↦ᵣ un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c q0_dlo rhat2_un0 q0' cr
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 44) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 48) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 52) (.JAL .x0 8))
       (CodeReq.singleton (base + 56) (.ADDI .x5 .x5 4095))))))))))))))) := rfl
  have h1_raw := divK_div128_step2_init_spec un21 d_hi v1_old v5_old v11_old base
  have h1 : cpsTriple base (base + 12) cr _ _ :=
    cpsTriple_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left _ _)))
  have h1f := cpsTriple_frame_left _ _ _ _ _
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  have h2_raw := divK_div128_clamp_q0_merged_spec q0 rhat2 d_hi (q0 * d_hi) (base + 12)
  have : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  simp only [*] at h2_raw
  have h2 : cpsTriple (base + 12) (base + 28) cr _ _ :=
    cpsTriple_extend_code (h := h2_raw) (hmono := by
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
  have h2f := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ un21) ** (.x12 ↦ᵣ sp) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h2
  have h12 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h1f h2f
  have h3_raw := divK_div128_prodcheck2_merged_spec sp q0c rhat2c hi
    un21 dlo un0 (base + 28)
  have : (base + 28 : Word) + 4 = base + 32 := by bv_addr
  have : (base + 28 : Word) + 8 = base + 36 := by bv_addr
  have : (base + 28 : Word) + 12 = base + 40 := by bv_addr
  have : (base + 28 : Word) + 16 = base + 44 := by bv_addr
  have : (base + 28 : Word) + 20 = base + 48 := by bv_addr
  have : (base + 28 : Word) + 24 = base + 52 := by bv_addr
  have : (base + 28 : Word) + 28 = base + 56 := by bv_addr
  have : (base + 28 : Word) + 32 = base + 60 := by bv_addr
  simp only [*] at h3_raw
  have h3 : cpsTriple (base + 28) (base + 60) cr _ _ :=
    cpsTriple_extend_code (h := h3_raw) (hmono := by
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
  have h3f := cpsTriple_frame_left _ _ _ _ _
    ((.x6 ↦ᵣ d_hi) ** (.x0 ↦ᵣ 0))
    (by pcFree) h3
  have h123 := cpsTriple_seq_with_perm_same_cr _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) h12 h3f
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h123

end EvmAsm.Evm64
