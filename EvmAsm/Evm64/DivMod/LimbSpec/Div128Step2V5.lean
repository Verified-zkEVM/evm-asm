/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2V5

  Step-2 composition for the v5 `divK_div128_v5` subroutine.

  This file builds the v5 Phase-2 block specs bottom-up. The first piece
  is the straight-line prefix `init + cap_q0` (instrs [46]-[56]):

    * step-2 init (DIVU + MUL + SUB) — instrs [46..48]: q0 = un21 / dHi,
      rhat2 = un21 - q0*dHi.
    * Phase-2a cap block — instrs [49..56]
      (`divK_div128_cap_q0_v5_merged_spec_within`): caps q0c at 0xFFFFFFFF
      and recomputes rhat2c when q0 ≥ 2^32.

  Output `q0c`/`rhat2c` match the Phase-2a portion of `div128Quot_v5`.
  This is the foundation of the full `step2_v5` spec (which additionally
  threads the Phase-2b guard + the two D3 corrections). Register-renamed
  mirror of `divK_div128_step1_initcap_v5_spec_within` (Div128Step1V5.lean):
  the trial quotient lives in `x5` (was `x10`), the remainder in `x11`
  (was `x7`), the cap scratch in `x9` (was `x5`), and the diff scratch in
  `x7` (was `x9`).

  Bead `evm-asm-wbc4i.6.7` (V5.6.8), part of `div128_v5_spec` (bead `.6`).
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128CapV5
public import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

@[expose] public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Code requirement for the div128 v5 step-2 prefix (init + Phase-2a cap,
    instrs [46]-[56]). -/
def divKDiv128Step2InitCapV5Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x9 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x9))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x9 .x5 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x9 .x0 28))
  (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x9 .x0 4095))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x9 .x9 32))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x7 .x5 .x9))
  (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x11 .x11 .x7))
   (CodeReq.singleton (base + 40) (.ADDI .x5 .x9 0)))))))))))

/-- div128 v5 step-2 prefix: trial division `q0` then the Phase-2a cap.
    Instrs [46]-[56]. Input: un21 in x7, dHi in x6. Output: capped `q0c`
    in x5, recomputed `rhat2c` in x11. -/
theorem divK_div128_step2_initcap_v5_spec_within
    (un21 dHi v5Old v9Old v11Old : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0cCap
    let rhat2c := if hi = 0 then rhat2 else rhat2 + (q0 - q0cCap) * dHi
    let x9o := if hi = 0 then hi else q0cCap
    let x7o := if hi = 0 then un21 else (q0 - q0cCap) * dHi
    cpsTripleWithin 11 base (base + 44) (divKDiv128Step2InitCapV5Code base)
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ 0))
      ((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x9 ↦ᵣ x9o) ** (.x7 ↦ᵣ x7o) ** (.x0 ↦ᵣ 0)) := by
  intro q0 rhat2 hi q0cCap q0c rhat2c x9o x7o
  let cr := divKDiv128Step2InitCapV5Code base
  show cpsTripleWithin 11 base (base + 44) cr _ _
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x9 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x9))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x9 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x9 .x0 28))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x9 .x0 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.SRLI .x9 .x9 32))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SUB .x7 .x5 .x9))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADD .x11 .x11 .x7))
       (CodeReq.singleton (base + 40) (.ADDI .x5 .x9 0))))))))))) := rfl
  -- Block 1: step-2 init [46..48] (DIVU + MUL + SUB).
  have h1_raw : cpsTripleWithin 3 base (base + 12)
      (CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x9 .x5 .x6))
       (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x9))))
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old))
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0) **
       (.x9 ↦ᵣ q0 * dHi) ** (.x11 ↦ᵣ rhat2)) := by
    have I0 := divu_spec_gen_within .x5 .x7 .x6 v5Old un21 dHi base (by nofun)
    have I1 := mul_spec_gen_within .x9 .x5 .x6 v9Old q0 dHi (base + 4) (by nofun)
    have I2 := sub_spec_gen_within .x11 .x7 .x9 un21 (q0 * dHi) v11Old (base + 8) (by nofun)
    runBlock I0 I1 I2
  have h1 : cpsTripleWithin 3 base (base + 12) cr _ _ :=
    cpsTripleWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]
      exact CodeReq.union_mono_tail (CodeReq.union_mono_tail (CodeReq.union_mono_left)))
  have h1f := cpsTripleWithin_frameR
    (.x0 ↦ᵣ (0 : Word))
    (by pcFree) h1
  -- Block 2: Phase-2a cap [49..56].
  have h2_raw := divK_div128_cap_q0_v5_merged_spec_within q0 rhat2 dHi (q0 * dHi) un21 (base + 12)
  unfold divKDiv128CapQ0V5Code at h2_raw
  have hb4 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  have hb8 : (base + 12 : Word) + 8 = base + 20 := by bv_addr
  have hb12 : (base + 12 : Word) + 12 = base + 24 := by bv_addr
  have hb16 : (base + 12 : Word) + 16 = base + 28 := by bv_addr
  have hb20 : (base + 12 : Word) + 20 = base + 32 := by bv_addr
  have hb24 : (base + 12 : Word) + 24 = base + 36 := by bv_addr
  have hb28 : (base + 12 : Word) + 28 = base + 40 := by bv_addr
  have hb32 : (base + 12 : Word) + 32 = base + 44 := by bv_addr
  simp only [hb32] at h2_raw
  have h2 : cpsTripleWithin 8 (base + 12) (base + 44) cr _ _ :=
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
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1f h2
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    h12

/-- Code requirement for the div128 v5 step-2 prefix + Phase-2b leading
    guard (instrs [46]-[58]): the init+cap code disjoint-unioned with the
    guard `SRLI;BNE` ([57]-[58]). -/
def divKDiv128Step2InitCapGuardV5Code (base : Word) : CodeReq :=
  (divKDiv128Step2InitCapV5Code base).union
  (CodeReq.union (CodeReq.singleton (base + 44) (.SRLI .x9 .x11 32))
   (CodeReq.singleton (base + 48) (.BNE .x9 .x0 92)))

/-- v5 div128 step-2 prefix + Phase-2b leading guard (instrs [46]-[58]).
    Runs init+cap (→ q0c/rhat2c) then the Phase-2b guard `SRLI;BNE`: when
    `rhat2c ≥ 2^32` the guard is taken and jumps past both D3 corrections to
    `base+140` ([81], the combine boundary); otherwise it falls through to
    `base+52` ([59], the Phase-2b body). `cpsBranchWithin` over the disjoint
    union of the prefix and guard code requirements. Register-renamed mirror
    of `divK_div128_step1_initcapguard_v5_spec_within`. -/
theorem divK_div128_step2_initcapguard_v5_spec_within
    (sp un21 dHi v5Old v9Old v11Old : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0cCap
    let rhat2c := if hi = 0 then rhat2 else rhat2 + (q0 - q0cCap) * dHi
    let x7o := if hi = 0 then un21 else (q0 - q0cCap) * dHi
    cpsBranchWithin 13 base (divKDiv128Step2InitCapGuardV5Code base)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x9 ↦ᵣ v9Old) ** (.x11 ↦ᵣ v11Old) ** (.x0 ↦ᵣ 0))
      (base + 140)
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x9 ↦ᵣ rhat2c >>> (32 : BitVec 6).toNat) **
         (.x0 ↦ᵣ 0) ** ⌜rhat2c >>> (32 : BitVec 6).toNat ≠ 0⌝ **
         (.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7o))
      (base + 52)
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x9 ↦ᵣ rhat2c >>> (32 : BitVec 6).toNat) **
         (.x0 ↦ᵣ 0) ** ⌜rhat2c >>> (32 : BitVec 6).toNat = 0⌝ **
         (.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7o)) := by
  intro q0 rhat2 hi q0cCap q0c rhat2c x7o
  unfold divKDiv128Step2InitCapGuardV5Code
  -- Prefix [46..56]: init + cap → q0c/rhat2c, framed with x12 = sp.
  have hpre := divK_div128_step2_initcap_v5_spec_within un21 dHi v5Old v9Old v11Old base
  have hpref := cpsTripleWithin_frameR (.x12 ↦ᵣ sp) (by pcFree) hpre
  -- Guard [57..58] at base+44.
  have hg := divK_div128_phase2b_guard_spec_within sp rhat2c
    (if hi = 0 then hi else q0cCap) (base + 44) (92 : BitVec 13)
  have hba : (base + 44 : Word) + 4 = base + 48 := by bv_addr
  have hfe : (base + 44 : Word) + 8 = base + 52 := by bv_addr
  simp only [hba, hfe] at hg
  have hte : (base + 48 : Word) + signExtend13 (92 : BitVec 13) = base + 140 := by rv64_addr
  rw [hte] at hg
  have hgf := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7o))
    (by pcFree) hg
  have composed := cpsTripleWithin_seq_cpsBranchWithin_with_perm
    (by unfold divKDiv128Step2InitCapV5Code; crDisjoint)
    (fun h hp => by xperm_hyp hp) hpref hgf
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Evm64
