/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1b

  Block spec for the **2nd D3 correction iteration** added by
  `divK_div128_v2` (in `EvmAsm/Evm64/DivMod/Program.lean`). This is
  the Phase 1b 2nd correction block — instructions [25..34] of the
  fixed `divK_div128_v2` subroutine (10 instructions: SRLI guard +
  BNE skip + 8-instruction D3 step mirroring `Div128ProdCheck1`).

  The block spec proves that under the precondition `q1c, rhatc` (post
  Phase 1a clamp + 1st D3 correction), the 10 instructions correctly
  compute Knuth's classical 2nd D3 correction:
  - if `rhatc < 2^32` (guard condition) AND
    `q1c * dLo > rhatc * 2^32 + un1` (product test),
    then q1' := q1c - 1, rhat' := rhatc + dHi.
  - otherwise q1' := q1c, rhat' := rhatc.

  The merged spec is shaped as a `cpsBranchWithin` (mirroring
  `divK_div128_step2_branch_merged_spec_within`) where both legs converge at
  `base + 40` but carry different register postconditions for `.x5`
  and `.x1` (the body's mul-check temporaries).

  Issue #1337's algorithm fix migration. Tracked in PR #1389.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se21_12)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Sub-stub A — guard portion**: `[25..26]` SRLI + BNE (cpsBranchWithin).
    Mirrors `divK_div128_phase2b_guard_spec_within` but with `.x7` as the rhat
    register (Phase 2b uses `.x11`).

    Branches:
    - **Taken** (rhatHi ≠ 0): branches to `(base + 4) + signExtend13 guard_off`.
    - **Fall-through** (rhatHi = 0): continues to `base + 8`. -/
theorem divK_div128_prodcheck1b_guard_spec_within
    (sp rhat v1Old : Word) (base : Word) (guard_off : BitVec 13) :
    let rhatHi := rhat >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x7 32))
        (CodeReq.singleton (base + 4) (.BNE .x1 .x0 guard_off))
    cpsBranchWithin 2 base cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat) ** (.x1 ↦ᵣ v1Old) ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 guard_off)
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat) ** (.x1 ↦ᵣ rhatHi) **
         (.x0 ↦ᵣ 0) ** ⌜rhatHi ≠ 0⌝)
      (base + 8)
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat) ** (.x1 ↦ᵣ rhatHi) **
         (.x0 ↦ᵣ 0) ** ⌜rhatHi = 0⌝) := by
  intro rhatHi cr
  -- Step 1: SRLI .x1 .x7 32  (cpsTripleWithin base → base+4)
  have hsrli_raw := srli_spec_gen_within .x1 .x7 v1Old rhat 32 base (by nofun)
  have hcr_srli : ∀ a i,
      CodeReq.singleton base (.SRLI .x1 .x7 32) a = some i → cr a = some i := by
    intro a i h
    simp only [cr, CodeReq.union, CodeReq.singleton] at h ⊢
    split at h
    · rename_i hab; simp_all
    · simp at h
  have hsrli := cpsTripleWithin_extend_code hcr_srli hsrli_raw
  have hsrli_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0))
    (by pcFree) hsrli
  -- Step 2: BNE .x1 .x0 guard_off  (cpsBranchWithin base+4 → ...)
  have hbne_raw := bne_spec_gen_within .x1 .x0 guard_off rhatHi (0 : Word) (base + 4)
  have hcr_bne : ∀ a i,
      CodeReq.singleton (base + 4) (.BNE .x1 .x0 guard_off) a = some i → cr a = some i := by
    intro a i h
    simp only [cr, CodeReq.union, CodeReq.singleton] at h ⊢
    split at h
    · rename_i hab; rw [beq_iff_eq] at hab; subst hab
      have : (base + 4 : Word) ≠ base := by bv_omega
      simp_all
    · simp at h
  have hbne := cpsBranchWithin_extend_code hcr_bne hbne_raw
  have hbne_framed := cpsBranchWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat))
    (by pcFree) hbne
  have composed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsrli_framed hbne_framed
  have h_addr_eq : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [h_addr_eq] at composed
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

/-- Bundled CodeReq for `divK_div128_prodcheck1b_body_spec_within` (8 singletons,
    instrs [27..34]). `@[irreducible]` to keep let-bindings out of the
    theorem signature. -/
@[irreducible]
def divKDiv128Prodcheck1bBodyCode (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))
  (CodeReq.union (CodeReq.singleton (base + 16) (.BLTU .x1 .x5 8))
  (CodeReq.union (CodeReq.singleton (base + 20) (.JAL .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 24) (.ADDI .x10 .x10 4095))
   (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))))))))

/-- Bundled precondition for `divK_div128_prodcheck1b_body_spec_within`. -/
@[irreducible]
def divKDiv128Prodcheck1bBodyPre (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
  (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Bundled postcondition for `divK_div128_prodcheck1b_body_spec_within`. -/
@[irreducible]
def divKDiv128Prodcheck1bBodyPost (sp q1c rhatc dHi un1 dlo : Word) : Assertion :=
  let qDlo := q1c * dlo
  let rhatUn1' := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1' qDlo then q1c + signExtend12 4095 else q1c
  let rhat' := if BitVec.ult rhatUn1' qDlo then rhatc + dHi else rhatc
  (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
  (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1') ** (.x6 ↦ᵣ dHi) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- **Sub-stub B — body portion**: `[27..34]` LD/MUL/SLLI/OR/BLTU/JAL/ADDI/ADD.
    Identical structure to `divK_div128_prodcheck1_merged_spec_within` (the 1st
    D3 block); just at a different offset within `divK_div128_v2`.

    Reachable only when the guard at [25..26] falls through (rhatc < 2^32). -/
theorem divK_div128_prodcheck1b_body_spec_within
    (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) (base : Word) :
    cpsTripleWithin 8 base (base + 32) (divKDiv128Prodcheck1bBodyCode base)
      (divKDiv128Prodcheck1bBodyPre sp q1c rhatc dHi un1 v1Old v5Old dlo)
      (divKDiv128Prodcheck1bBodyPost sp q1c rhatc dHi un1 dlo) := by
  unfold divKDiv128Prodcheck1bBodyCode divKDiv128Prodcheck1bBodyPre
    divKDiv128Prodcheck1bBodyPost
  exact divK_div128_prodcheck1_merged_spec_within
    sp q1c rhatc dHi un1 v1Old v5Old dlo base

/-- Bundled CodeReq for `divK_div128_prodcheck1b_merged_spec_within` (10 singletons,
    instrs [25..34]). `@[irreducible]` to keep let-bindings out of the
    theorem signature. -/
@[irreducible]
def divKDiv128Prodcheck1bMergedCode (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x1 .x0 36))
  (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x1 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x5 .x10 .x1))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x1 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x1 .x1 .x11))
  (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x1 .x5 8))
  (CodeReq.union (CodeReq.singleton (base + 28) (.JAL .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x10 .x10 4095))
   (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x6))))))))))

/-- Bundled precondition for `divK_div128_prodcheck1b_merged_spec_within`. -/
@[irreducible]
def divKDiv128Prodcheck1bMergedPre (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
  (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Bundled taken-leg postcondition for `divK_div128_prodcheck1b_merged_spec_within`
    (rhatHi ≠ 0: guard fires, body is skipped). -/
@[irreducible]
def divKDiv128Prodcheck1bMergedTakenPost
    (sp q1c rhatc dHi un1 v5Old dlo : Word) : Assertion :=
  let rhatHi := rhatc >>> (32 : BitVec 6).toNat
  (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
  (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ rhatHi) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
  ⌜rhatHi ≠ 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Bundled fall-through-leg postcondition for `divK_div128_prodcheck1b_merged_spec_within`
    (rhatHi = 0: guard falls through, body runs the 2nd D3 mul-check). -/
@[irreducible]
def divKDiv128Prodcheck1bMergedFTPost (sp q1c rhatc dHi un1 dlo : Word) :
    Assertion :=
  let qDlo := q1c * dlo
  let rhatUn1' := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let rhatHi := rhatc >>> (32 : BitVec 6).toNat
  let q1'FT := if BitVec.ult rhatUn1' qDlo then q1c + signExtend12 4095 else q1c
  let rhat'FT := if BitVec.ult rhatUn1' qDlo then rhatc + dHi else rhatc
  (.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1'FT) ** (.x7 ↦ᵣ rhat'FT) ** (.x11 ↦ᵣ un1) **
  (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1') ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
  ⌜rhatHi = 0⌝ **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- div128 product check 1b (Knuth classical 2nd D3 correction).
    Instrs [25]-[34] of `divK_div128_v2`. Both guard branches and both
    BLTU paths merge at `base + 40`.

    **Shape**: `cpsBranchWithin` — mirrors `divK_div128_step2_branch_merged_spec_within`'s
    pattern of "two paths converging at the same merge address but with
    different register postconditions". The taken leg (rhatHi ≠ 0) skips
    the body, leaving `.x5 = v5Old` and `.x1 = rhatHi` (the SRLI result).
    The fall-through leg (rhatHi = 0) executes the body, producing
    `.x5 = qDlo` and `.x1 = rhatUn1'`. Both legs end at `base + 40`.

    Composes:
    - Sub-stub A (`divK_div128_prodcheck1b_guard_spec_within`): [25..26] guard.
    - Sub-stub B (`divK_div128_prodcheck1b_body_spec_within`): [27..34] body.

    **Output for `.x10` (q1) / `.x7` (rhat)** matches the Lean abstraction
    `div128Quot_v2`'s 2nd D3 step:
    ```
    let q1' := if rhatc < 2^32 ∧ rhatUn1' < q1c * dLo
               then q1c - 1 else q1c
    let rhat' := if rhatc < 2^32 ∧ rhatUn1' < q1c * dLo
                 then rhatc + dHi else rhatc
    ```
    (taken leg gives the `else q1c` / `else rhatc` directly via `rhatHi ≠ 0`.)

    Issue #1337 algorithm fix migration. -/
theorem divK_div128_prodcheck1b_merged_spec_within
    (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) (base : Word) :
    cpsBranchWithin 10 base (divKDiv128Prodcheck1bMergedCode base)
      (divKDiv128Prodcheck1bMergedPre sp q1c rhatc dHi un1 v1Old v5Old dlo)
      (base + 40)
        (divKDiv128Prodcheck1bMergedTakenPost sp q1c rhatc dHi un1 v5Old dlo)
      (base + 40)
        (divKDiv128Prodcheck1bMergedFTPost sp q1c rhatc dHi un1 dlo) := by
  unfold divKDiv128Prodcheck1bMergedCode divKDiv128Prodcheck1bMergedPre
    divKDiv128Prodcheck1bMergedTakenPost divKDiv128Prodcheck1bMergedFTPost
  -- Reintroduce the locals the proof body uses (formerly let-bound in the
  -- statement). With bundled defs in the signature, these locals are private
  -- to the proof.
  let qDlo := q1c * dlo
  let rhatUn1' := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let rhatHi := rhatc >>> (32 : BitVec 6).toNat
  let cr :=
    CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x7 32))
    (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x1 .x0 36))
    (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x1 .x12 3952))
    (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x5 .x10 .x1))
    (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x1 .x7 32))
    (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x1 .x1 .x11))
    (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x1 .x5 8))
    (CodeReq.union (CodeReq.singleton (base + 28) (.JAL .x0 12))
    (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x10 .x10 4095))
     (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x6))))))))))
  have hcr_eq : cr =
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 28) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x6)))))))))) := rfl
  -- h1 = guard_spec sp rhatc v1Old base 36 (cpsBranchWithin base..base+40|base+8)
  have h1_raw := divK_div128_prodcheck1b_guard_spec_within sp rhatc v1Old base (36 : BitVec 13)
  have ha_t : (base + 4 : Word) + signExtend13 (36 : BitVec 13) = base + 40 := by rv64_addr
  rw [ha_t] at h1_raw
  -- Extend guard's 2-singleton cr to merged's 10-singleton cr
  have h1 : cpsBranchWithin 2 base cr _ _ _ _ _ :=
    cpsBranchWithin_extend_code (h := h1_raw) (hmono := by
      rw [hcr_eq]; intro a i
      simp only [CodeReq.union_singleton_apply, CodeReq.singleton]; intro h
      split at h
      · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all
      · split at h
        · next hab => rw [beq_iff_eq] at hab; subst hab; simp_all [CodeReq.beq_offset_self_left]
        · simp at h)
  -- Frame guard with the unchanged-through-guard atoms
  have h1f := cpsBranchWithin_frameR
    ((.x10 ↦ᵣ q1c) ** (.x11 ↦ᵣ un1) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ dHi) **
     (sp + signExtend12 3952 ↦ₘ dlo))
    (by pcFree) h1
  -- h2 = body_spec at base+8 — body's v1Old becomes the SRLI result rhatHi
  have h2_raw := divK_div128_prodcheck1b_body_spec_within sp q1c rhatc dHi un1 rhatHi v5Old dlo
    (base + 8)
  -- Unfold the body's bundled forms so the rest of the proof works with the
  -- explicit cr / pre / post structure.
  unfold divKDiv128Prodcheck1bBodyCode divKDiv128Prodcheck1bBodyPre
    divKDiv128Prodcheck1bBodyPost at h2_raw
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
  -- Frame body with (.x0 ↦ᵣ 0) ** ⌜rhatHi = 0⌝ — both pass through unchanged
  have h2f := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ 0) ** ⌜rhatHi = 0⌝)
    (by pcFree) h2
  -- Compose: guard fall-through ⨾ body, with permutation matching guard's Q_f → body's pre
  have composed := cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    (h1 := h1f)
    (hperm := fun h hp => by xperm_hyp hp)
    (h2 := h2f)
    (ht1 := fun h hp => hp)
  -- Weaken final post to merged_spec's right-associated shape
  exact cpsBranchWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Evm64
