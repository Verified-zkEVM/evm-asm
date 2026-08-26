/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase2bV5

  v5 div128 Phase-2b 2nd-D3 block (instrs [71]-[80] of `divK_div128_v5`):
  the guarded second Knuth-D3 correction on `q0`.

    * Phase-2b 2nd-D3 guard — [71..72]: `SRLI x9 x11 32 ; BNE x9 x0 36`.
      When `rhat2' ≥ 2^32` the guard fires and skips the mul-check.
    * prodcheck2 mul-check — [73..80]:
      `LD x9 x12 3952 ; MUL x7 x5 x9 ; SLLI x9 x11 32 ; LD x11 x12 3944 ;
       OR x9 x9 x11 ; BLTU x9 x7 8 ; JAL x0 8 ; ADDI x5 x5 4095`.

  This is the Phase-2b analogue of `divK_div128_prodcheck1b_merged_spec_within`
  (`Div128ProdCheck1b.lean`) — the building block the v4 step2 spec lacked
  (v4 inlined Phase-2b via `phase_D`/`phase_E` over the full step2 code).
  Both Phase-2b D3 corrections are identical between v4 and v5; only the
  Phase-2a cap differs. Composed via the disjoint guard + body sequencing
  lemma `cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr`, so no
  flat-CR subsumption is needed beyond the standard code extensions.

  Bead `evm-asm-wbc4i.6.9` (V5.6.10); a building block of the full
  `step2_v5` spec (bead `.6`).
-/

module

public import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

@[expose] public section

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se21_16)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled CodeReq for `divK_div128_prodcheck2b_v5_merged_spec_within`
    (10 singletons, instrs [71..80]). `@[irreducible]` to keep the
    let-chain out of the theorem signature. -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedCode (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x9 .x0 36))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x9 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x7 .x5 .x9))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x9 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x11 .x12 3944))
  (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x9 .x9 .x11))
  (CodeReq.union (CodeReq.singleton (base + 28) (.BLTU .x9 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 8))
   (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))))))))))

/-- Bundled precondition. -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedPre (sp q0' rhat2' v7Old v9Old dlo un0 : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x7 ↦ᵣ v7Old) **
  (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- Bundled taken-leg postcondition (rhat2'Hi ≠ 0: guard fires, body skipped). -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedTakenPost
    (sp q0' rhat2' v7Old dlo un0 : Word) : Assertion :=
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x7 ↦ᵣ v7Old) **
  (.x9 ↦ᵣ rhat2'Hi) ** (.x0 ↦ᵣ 0) ** ⌜rhat2'Hi ≠ 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- Bundled fall-through-leg postcondition (rhat2'Hi = 0: body runs the
    2nd D3 mul-check). -/
@[irreducible]
def divKDiv128Prodcheck2bV5MergedFTPost (sp q0' rhat2' dlo un0 : Word) :
    Assertion :=
  let q0Dlo := q0' * dlo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0'' := if BitVec.ult rhat2'Un0 q0Dlo then q0' + signExtend12 4095 else q0'
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0'') ** (.x11 ↦ᵣ un0) ** (.x7 ↦ᵣ q0Dlo) **
  (.x9 ↦ᵣ rhat2'Un0) ** (.x0 ↦ᵣ 0) ** ⌜rhat2'Hi = 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)

/-- div128 v5 Phase-2b 2nd-D3 block (instrs [71]-[80]): the guard
    `SRLI;BNE` then the prodcheck2 mul-check. Both guard branches and both
    BLTU paths merge at `base + 40`. The taken leg (rhat2'Hi ≠ 0) skips the
    body, leaving `.x5 = q0'`, `.x9 = rhat2'Hi`. The fall-through leg
    (rhat2'Hi = 0) executes the mul-check, producing `.x5 = q0''`,
    `.x11 = un0`, `.x7 = q0'*dlo`, `.x9 = rhat2'*2^32|un0`.

    Phase-2b analogue of `divK_div128_prodcheck1b_merged_spec_within`. -/
theorem divK_div128_prodcheck2b_v5_merged_spec_within
    (sp q0' rhat2' v7Old v9Old dlo un0 : Word) (base : Word) :
    cpsBranchWithin 10 base (divKDiv128Prodcheck2bV5MergedCode base)
      (divKDiv128Prodcheck2bV5MergedPre sp q0' rhat2' v7Old v9Old dlo un0)
      (base + 40)
        (divKDiv128Prodcheck2bV5MergedTakenPost sp q0' rhat2' v7Old dlo un0)
      (base + 40)
        (divKDiv128Prodcheck2bV5MergedFTPost sp q0' rhat2' dlo un0) := by
  unfold divKDiv128Prodcheck2bV5MergedCode divKDiv128Prodcheck2bV5MergedPre
    divKDiv128Prodcheck2bV5MergedTakenPost divKDiv128Prodcheck2bV5MergedFTPost
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let cr :=
    CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x11 32))
    (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x9 .x0 36))
    (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x9 .x12 3952))
    (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x7 .x5 .x9))
    (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x9 .x11 32))
    (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x11 .x12 3944))
    (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x9 .x9 .x11))
    (CodeReq.union (CodeReq.singleton (base + 28) (.BLTU .x9 .x7 8))
    (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 8))
     (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))))))))))
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.SRLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x9 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x9 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x7 .x5 .x9))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 24) (.OR .x9 .x9 .x11))
      (CodeReq.union (CodeReq.singleton (base + 28) (.BLTU .x9 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 8))
       (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095)))))))))) := rfl
  -- Guard [71..72] at base: cpsBranchWithin, taken→base+40, ft→base+8.
  have h1_raw := divK_div128_phase2b_guard_spec_within sp rhat2' v9Old base (36 : BitVec 13)
  have ha_t : (base + 4 : Word) + signExtend13 (36 : BitVec 13) = base + 40 := by rv64_addr
  rw [ha_t] at h1_raw
  have h1 : cpsBranchWithin 2 base cr _ _ _ _ _ :=
    cpsBranchWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left]
        · simp at h)
  have h1f := cpsBranchWithin_frameR
    ((.x5 ↦ᵣ q0') ** (.x7 ↦ᵣ v7Old) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
    (by pcFree) h1
  -- Body [73..80] at base+8: prodcheck2 mul-check (x9 input = rhat2'Hi, dead).
  have h2_raw := divK_div128_prodcheck2_merged_spec_within sp q0' rhat2' rhat2'Hi v7Old dlo un0
    (base + 8)
  have hb4 : (base + 8 : Word) + 4 = base + 12 := by bv_addr
  have hb8 : (base + 8 : Word) + 8 = base + 16 := by bv_addr
  have hb12 : (base + 8 : Word) + 12 = base + 20 := by bv_addr
  have hb16 : (base + 8 : Word) + 16 = base + 24 := by bv_addr
  have hb20 : (base + 8 : Word) + 20 = base + 28 := by bv_addr
  have hb24 : (base + 8 : Word) + 24 = base + 32 := by bv_addr
  have hb28 : (base + 8 : Word) + 28 = base + 36 := by bv_addr
  have hb32 : (base + 8 : Word) + 32 = base + 40 := by bv_addr
  simp only [hb4, hb8, hb12, hb16, hb20, hb24, hb28, hb32] at h2_raw
  have h2 : cpsTripleWithin 8 (base + 8) (base + 40) cr _ _ :=
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
  have h2f := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ 0) ** ⌜rhat2'Hi = 0⌝)
    (by pcFree) h2
  -- Compose: guard fall-through ⨾ body.
  have composed := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    (h1 := h1f)
    (hperm := fun h hp => by xperm_hyp hp)
    (h2 := h2f)
    (ht1 := fun h hp => hp)
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

/-- div128 v5 Phase-2b 1st-D3 correction WITH spill (instrs [59]-[70]).
    Setup `LD/MUL/SLLI/SD/LD/OR` [59..64] computes `q0c*dlo` (x7) and
    `rhat2c*2^32|un0` (x9), spilling `rhat2c` to `mem[sp+3936]` and reloading
    `un0` into x11. The `BLTU x9 x7 12` [65] then conditionally corrects:
    when `rhat2Un0 < q0Dlo1` (taken, [68..70]) it decrements `q0c` and adds
    `dHi` to the restored `rhat2c`; otherwise (fall-through, [66..67]) it
    just restores `rhat2c` and skips. Both paths converge at `base+48` ([71]).

    Reached only when the Phase-2b outer guard ([57..58]) falls through, so the
    block itself is unguarded (the `rhat2c < 2^32` regime is the caller's
    invariant). Self-contained re-derivation of the v4 step2 `hC + phase_D`
    blocks (whose CR is tied to the full v4 step2 code). -/
theorem divK_div128_prodcheck2_spill_merged_spec_within
    (sp q0c rhat2c dHi v7Old v9Old dlo un0 vScratchOld : Word) (base : Word) :
    let q0Dlo1 := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
    let rhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x9 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x9))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x11 3936))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x9 .x9 .x11))
      (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x9 .x7 12))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x11 .x12 3936))
      (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 16))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3936))
       (CodeReq.singleton (base + 44) (.ADD .x11 .x11 .x6))))))))))))
    cpsTripleWithin 10 base (base + 48) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ v7Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2') ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ q0Dlo1) ** (.x9 ↦ᵣ rhat2Un0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro q0Dlo1 rhat2Un0 q0' rhat2' cr
  -- Setup [59..64]: LD/MUL/SLLI/SD/LD/OR → x7=q0Dlo1, x9=rhat2Un0, x11=un0,
  -- mem3936=rhat2c.
  have hbody : cpsTripleWithin 6 base (base + 24) cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ v7Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ q0Dlo1) ** (.x9 ↦ᵣ rhat2Un0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
    have I0 := ld_spec_gen_within .x9 .x12 sp v9Old dlo 3952 base (by nofun)
    have I1 := mul_spec_gen_within .x7 .x5 .x9 v7Old q0c dlo (base + 4) (by nofun)
    have I2 := slli_spec_gen_within .x9 .x11 dlo rhat2c 32 (base + 8) (by nofun)
    have I3 := sd_spec_gen_within .x12 .x11 sp rhat2c vScratchOld 3936 (base + 12)
    have I4 := ld_spec_gen_within .x11 .x12 sp rhat2c un0 3944 (base + 16) (by nofun)
    have I5 := or_spec_gen_rd_eq_rs1_within .x9 .x11
      (rhat2c <<< (32 : BitVec 6).toNat) un0 (base + 20) (by nofun)
    runBlock I0 I1 I2 I3 I4 I5
  -- BLTU [65] at base+24: taken (ult)→base+36, ft→base+28.
  have hbltu_raw := bltu_spec_gen_within .x9 .x7 (12 : BitVec 13) rhat2Un0 q0Dlo1 (base + 24)
  have ha_t : (base + 24) + signExtend13 (12 : BitVec 13) = base + 36 := by rv64_addr
  have ha_f : (base + 24 : Word) + 4 = base + 28 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  have hbltu_framed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ rhat2c))
    (by pcFree) hbltu_raw
  have hbltu_ext : cpsBranchWithin 1 (base + 24) cr
      (((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1)) **
       ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
        (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
        (sp + signExtend12 3936 ↦ₘ rhat2c)))
      (base + 36)
        (((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜BitVec.ult rhat2Un0 q0Dlo1⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ rhat2c)))
      (base + 28)
        (((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜¬BitVec.ult rhat2Un0 q0Dlo1⌝) **
         ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ rhat2c))) :=
    fun R hR s hcr hPR hpc =>
      hbltu_framed R hR s (CodeReq.singleton_satisfiedBy.mpr (hcr _ _ (by
        show cr (base + 24) = _
        simp only [cr, CodeReq.union, CodeReq.singleton]
        have h0 : ¬(base + 24 = base) := by bv_omega
        have h1 : ¬(base + 24 = base + 4) := by bv_omega
        have h2 : ¬(base + 24 = base + 8) := by bv_omega
        have h3 : ¬(base + 24 = base + 12) := by bv_omega
        have h4 : ¬(base + 24 = base + 16) := by bv_omega
        have h5 : ¬(base + 24 = base + 20) := by bv_omega
        simp only [beq_iff_eq, h0, h1, h2, h3, h4, h5, ↓reduceIte]))) hPR hpc
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbltu_ext
  by_cases hcond : BitVec.ult rhat2Un0 q0Dlo1
  · -- Taken [68..70]: ADDI(q0c--); LD(restore rhat2c); ADD(rhat2c+=dHi).
    have hq : q0' = q0c + signExtend12 4095 := if_pos hcond
    have hr : rhat2' = rhat2c + dHi := if_pos hcond
    rw [hq, hr]
    have taken_br := cpsBranchWithin_takenPath composed (fun hp hQf => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_p⟩, _⟩ := hQf
      exact ((sepConj_pure_right _).1 h_p).2 hcond)
    have J0 := addi_spec_gen_same_within .x5 q0c 4095 (base + 36) (by nofun)
    have J1 := ld_spec_gen_within .x11 .x12 sp un0 rhat2c 3936 (base + 40) (by nofun)
    have J2 := add_spec_gen_rd_eq_rs1_within .x11 .x6 rhat2c dHi (base + 44) (by nofun)
    have hpath : cpsTripleWithin 3 (base + 36) (base + 48) cr
        ((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ dHi) **
         (sp + signExtend12 3936 ↦ₘ rhat2c))
        ((.x5 ↦ᵣ (q0c + signExtend12 4095)) ** (.x11 ↦ᵣ (rhat2c + dHi)) **
         (.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ dHi) **
         (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
      runBlock J0 J1 J2
    have hpath_f := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) hpath
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          have hp' := sepConj_mono_left (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp')
        taken_br hpath_f)
  · -- Fall-through [66..67]: LD(restore rhat2c); JAL 16 → base+48.
    have hq : q0' = q0c := if_neg hcond
    have hr : rhat2' = rhat2c := if_neg hcond
    rw [hq, hr]
    have ntaken_br := cpsBranchWithin_ntakenPath composed (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_p⟩, _⟩ := hQt
      exact absurd ((sepConj_pure_right _).1 h_p).2 hcond)
    have ntaken_clean : cpsTripleWithin 7 base (base + 28) cr
        ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
         (.x7 ↦ᵣ v7Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ vScratchOld))
        ((.x9 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) **
         (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ un0) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c)) :=
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          have hp' := sepConj_mono_left (sepConj_mono_right
            (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
          xperm_hyp hp')
        ntaken_br
    have K0 := ld_spec_gen_within .x11 .x12 sp un0 rhat2c 3936 (base + 28) (by nofun)
    have hld : cpsTripleWithin 1 (base + 28) (base + 32) cr
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ un0) ** (sp + signExtend12 3936 ↦ₘ rhat2c))
        ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
      runBlock K0
    have hld_f := cpsTripleWithin_frameR
      ((.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ q0Dlo1) ** (.x9 ↦ᵣ rhat2Un0) **
       (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      (by pcFree) hld
    have K1 := jal_x0_spec_gen_within 16 (base + 32)
    rw [se21_16] at K1
    have ha_jal : (base + 32 : Word) + 16 = base + 48 := by bv_addr
    rw [ha_jal] at K1
    have hcr_jal : ∀ a i, CodeReq.singleton (base + 32) (.JAL .x0 16) a = some i →
        cr a = some i := by
      intro a i h
      simp only [CodeReq.singleton] at h
      split at h
      · next heq => rw [beq_iff_eq] at heq; subst heq; simp_all [cr, CodeReq.union, CodeReq.singleton]
      · simp at h
    have K1_cr := cpsTripleWithin_extend_code hcr_jal K1
    have hjal_f := cpsTripleWithin_frameR
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ q0Dlo1) ** (.x9 ↦ᵣ rhat2Un0) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      (by pcFree) K1_cr
    simp only [sepConj_emp_left'] at hjal_f
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by xperm_hyp hp)
        (cpsTripleWithin_seq_perm_same_cr
          (fun h hp => by xperm_hyp hp)
          ntaken_clean hld_f)
        hjal_f)

/-- Disjointness of the spill block's CodeReq [59..70] and the 2nd-D3 block's
    CodeReq [71..80] (at base+48). Top-level (fresh heartbeat budget): the
    120 singleton pairs would overflow `crDisjoint`'s inline simp. -/
theorem divKDiv128Phase2bBody_spill_prodcheck2b_disjoint (base : Word) :
    CodeReq.Disjoint
      (CodeReq.union (CodeReq.singleton base (.LD .x9 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x9))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x11 3936))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x9 .x9 .x11))
      (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x9 .x7 12))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x11 .x12 3936))
      (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 16))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3936))
       (CodeReq.singleton (base + 44) (.ADD .x11 .x11 .x6)))))))))))))
      (divKDiv128Prodcheck2bV5MergedCode (base + 48)) := by
  unfold divKDiv128Prodcheck2bV5MergedCode
  repeat' apply CodeReq.Disjoint.union_left
  all_goals (repeat' apply CodeReq.Disjoint.union_right)
  all_goals exact CodeReq.Disjoint.singleton (by bv_omega)

/-- div128 v5 Phase-2b body (instrs [59]-[80]): the 1st-D3 spill correction
    then the guarded 2nd-D3 correction. Composes `spill ;; prodcheck2b` via the
    disjoint-union sequencing lemma. `cpsBranchWithin 20`, both legs at
    `base + 88` ([81], the combine boundary): the 2nd-D3 guard taken leg
    (`rhat2'Hi ≠ 0`) keeps `q0'`; the fall-through leg runs the 2nd mul-check.

    Reached when the Phase-2b outer guard ([57..58]) falls through. Phase-2b
    analogue of `divK_div128_phase1b_body_v5_spec_within`. -/
theorem divK_div128_phase2b_body_v5_spec_within
    (sp q0c rhat2c dHi v7Old v9Old dlo un0 vScratchOld : Word) (base : Word) :
    let q0Dlo1 := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
    let rhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    let cr :=
      (CodeReq.union (CodeReq.singleton base (.LD .x9 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x7 .x5 .x9))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x9 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SD .x12 .x11 3936))
      (CodeReq.union (CodeReq.singleton (base + 16) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x9 .x9 .x11))
      (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x9 .x7 12))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x11 .x12 3936))
      (CodeReq.union (CodeReq.singleton (base + 32) (.JAL .x0 16))
      (CodeReq.union (CodeReq.singleton (base + 36) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 40) (.LD .x11 .x12 3936))
       (CodeReq.singleton (base + 44) (.ADD .x11 .x11 .x6))))))))))))).union
      (divKDiv128Prodcheck2bV5MergedCode (base + 48))
    cpsBranchWithin 20 base cr
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x7 ↦ᵣ v7Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      (base + 88)
        ((divKDiv128Prodcheck2bV5MergedTakenPost sp q0' rhat2' q0Dlo1 dlo un0) **
         ((.x6 ↦ᵣ dHi) ** (sp + signExtend12 3936 ↦ₘ rhat2c)))
      (base + 88)
        ((divKDiv128Prodcheck2bV5MergedFTPost sp q0' rhat2' dlo un0) **
         ((.x6 ↦ᵣ dHi) ** (sp + signExtend12 3936 ↦ₘ rhat2c))) := by
  intro q0Dlo1 rhat2Un0 q0' rhat2' cr
  -- Block 1: spill 1st-D3 [59..70] (cpsTriple base → base+48).
  have h1 := divK_div128_prodcheck2_spill_merged_spec_within
    sp q0c rhat2c dHi v7Old v9Old dlo un0 vScratchOld base
  -- Block 2: 2nd-D3 prodcheck2b [71..80] at base+48, framed with x6/mem3936.
  have h2_raw := divK_div128_prodcheck2b_v5_merged_spec_within
    sp q0' rhat2' q0Dlo1 rhat2Un0 dlo un0 (base + 48)
  have he : (base + 48 : Word) + 40 = base + 88 := by bv_addr
  rw [he] at h2_raw
  unfold divKDiv128Prodcheck2bV5MergedPre at h2_raw
  have h2f := cpsBranchWithin_frameR
    ((.x6 ↦ᵣ dHi) ** (sp + signExtend12 3936 ↦ₘ rhat2c))
    (by pcFree) h2_raw
  have composed := cpsTripleWithin_seq_cpsBranchWithin_with_perm
    (divKDiv128Phase2bBody_spill_prodcheck2b_disjoint base)
    (fun h hp => by xperm_hyp hp) h1 h2f
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => hp)
    (fun h hp => hp)
    composed

end EvmAsm.Evm64
