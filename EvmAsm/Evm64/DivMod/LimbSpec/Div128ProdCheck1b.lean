/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1b

  **STUB FILE** for issue #1337 algorithm fix migration.

  Provides the block spec for the **2nd D3 correction iteration** added
  by `divK_div128_v2` (in `EvmAsm/Evm64/DivMod/Program.lean`). This is
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

  **Status (2026-04-27)**: theorem signature only; proof is a sorry
  pending the multi-iteration migration. Mirrors the structure of
  `Div128ProdCheck1.divK_div128_prodcheck1_merged_spec` (the 1st D3
  block) and `Div128ProdCheck2.div128Quot_phase2b_q0'`
  (Phase 2b's guarded D3, structurally identical).

  Issue #1337's algorithm fix migration. Tracked in PR #1389.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se21_12)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Sub-stub A — guard portion**: `[25..26]` SRLI + BNE (cpsBranch).
    Mirrors `divK_div128_phase2b_guard_spec` but with `.x7` as the rhat
    register (Phase 2b uses `.x11`).

    Branches:
    - **Taken** (rhatHi ≠ 0): branches to `(base + 4) + signExtend13 guard_off`.
    - **Fall-through** (rhatHi = 0): continues to `base + 8`. -/
theorem divK_div128_prodcheck1b_guard_spec
    (sp rhat v1Old : Word) (base : Word) (guard_off : BitVec 13) :
    let rhatHi := rhat >>> (32 : BitVec 6).toNat
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x7 32))
        (CodeReq.singleton (base + 4) (.BNE .x1 .x0 guard_off))
    cpsBranch base cr
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat) ** (.x1 ↦ᵣ v1Old) ** (.x0 ↦ᵣ 0))
      ((base + 4) + signExtend13 guard_off)
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat) ** (.x1 ↦ᵣ rhatHi) **
         (.x0 ↦ᵣ 0) ** ⌜rhatHi ≠ 0⌝)
      (base + 8)
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat) ** (.x1 ↦ᵣ rhatHi) **
         (.x0 ↦ᵣ 0) ** ⌜rhatHi = 0⌝) := by
  intro rhatHi cr
  -- Step 1: SRLI .x1 .x7 32  (cpsTriple base → base+4)
  have hsrli_raw := srli_spec_gen .x1 .x7 v1Old rhat 32 base (by nofun)
  have hcr_srli : ∀ a i,
      CodeReq.singleton base (.SRLI .x1 .x7 32) a = some i → cr a = some i := by
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
  have hbne_raw := bne_spec_gen .x1 .x0 guard_off rhatHi (0 : Word) (base + 4)
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
    ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhat))
    (by pcFree) hbne
  have composed := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hsrli_framed hbne_framed
  have h_addr_eq : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [h_addr_eq] at composed
  exact cpsBranch_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    composed

/-- **Sub-stub B — body portion**: `[27..34]` LD/MUL/SLLI/OR/BLTU/JAL/ADDI/ADD.
    Identical structure to `divK_div128_prodcheck1_merged_spec` (the 1st
    D3 block); just at a different offset within `divK_div128_v2`.

    Reachable only when the guard at [25..26] falls through (rhatc < 2^32). -/
theorem divK_div128_prodcheck1b_body_spec
    (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) (base : Word) :
    let qDlo := q1c * dlo
    let rhatUn1' := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1' qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1' qDlo then rhatc + dHi else rhatc
    let cr :=
      CodeReq.union (CodeReq.singleton base (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 12) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 20) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 28) (.ADD .x7 .x7 .x6))))))))
    cpsTriple base (base + 32) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1') ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
  -- Direct delegation: this body is structurally identical to the 1st D3 block's
  -- merged spec — same 8 instructions at the same relative offsets.
  exact divK_div128_prodcheck1_merged_spec sp q1c rhatc dHi un1 v1Old v5Old dlo base

/-- div128 product check 1b (Knuth classical 2nd D3 correction).
    Instrs [25]-[34] of `divK_div128_v2`. Both guard branches and both
    BLTU paths merge at `base + 40`.

    **Shape**: `cpsBranch` — mirrors `divK_div128_step2_branch_merged_spec`'s
    pattern of "two paths converging at the same merge address but with
    different register postconditions". The taken leg (rhatHi ≠ 0) skips
    the body, leaving `.x5 = v5Old` and `.x1 = rhatHi` (the SRLI result).
    The fall-through leg (rhatHi = 0) executes the body, producing
    `.x5 = qDlo` and `.x1 = rhatUn1'`. Both legs end at `base + 40`.

    Composes:
    - Sub-stub A (`divK_div128_prodcheck1b_guard_spec`): [25..26] guard.
    - Sub-stub B (`divK_div128_prodcheck1b_body_spec`): [27..34] body.

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
theorem divK_div128_prodcheck1b_merged_spec
    (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) (base : Word) :
    let qDlo := q1c * dlo
    let rhatUn1' := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let rhatHi := rhatc >>> (32 : BitVec 6).toNat
    -- Fall-through leg only — the guard-taken leg keeps q1c / rhatc.
    let q1'FT := if BitVec.ult rhatUn1' qDlo then q1c + signExtend12 4095 else q1c
    let rhat'FT := if BitVec.ult rhatUn1' qDlo then rhatc + dHi else rhatc
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
    cpsBranch base cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      (base + 40)  -- guard-fires path (rhatHi ≠ 0): body is skipped
        ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
         (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ rhatHi) ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
         ⌜rhatHi ≠ 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo))
      (base + 40)  -- guard-doesn't-fire + body (rhatHi = 0): runs the mul-check
        ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1'FT) ** (.x7 ↦ᵣ rhat'FT) ** (.x11 ↦ᵣ un1) **
         (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1') ** (.x6 ↦ᵣ dHi) ** (.x0 ↦ᵣ 0) **
         ⌜rhatHi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo)) := by
  sorry  -- Composition of guard cpsBranch + body cpsTriple via cpsBranch_seq pattern.

end EvmAsm.Evm64
