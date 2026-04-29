/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2v4

  Full-step composition for instructions [40]-[70] of the
  `divK_div128_v4` subroutine — the v4 fix that adds a 2nd Phase 2b
  D3 correction iteration (Knuth TAOCP §4.3.1 classical D3 step,
  full 2-iteration version, Phase 2b half).

  Combines:
  - step-2-init (DIVU+MUL+SUB) — instrs [40..42] (same as v2 step2)
  - clamp-q0 (SRLI+BEQ+ADDI+ADD) — instrs [43..46] (same as v2)
  - Phase 2b guard (SRLI+BNE) — instrs [47..48] (same as v2)
  - Phase 2b 1st D3 with save/restore — instrs [49..60] (NEW shape)
  - Phase 2b 2nd D3 — instrs [61..70] (NEW)

  into a single refined `q0` computation matching the Lean abstraction
  `div128Quot_v4`'s Phase 2 output (q0 = q0'' after BOTH Phase 2b D3
  iterations).

  The v4 Phase 2b structure differs from v2 Phase 2b in two ways:
  1. The 1st D3 saves rhat2c to scratch slot 3936 before clobbering x11
     with un0, then restores it in BOTH BLTU paths so rhat2c is
     available for the 2nd D3 guard.
  2. The 2nd D3 (instrs [61..70]) mirrors Phase 1b's 2nd D3 structure
     but for q0/rhat2 instead of q1/rhat.

  PR-A2 of the v2 → v4 migration plan. Issue #1337 / Issue #61.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The 31 instructions of the step-2-v4 block (instrs [40..70] of
    `divK_div128_v4`), as a plain `List Instr` so `step2v4_sub` can use
    `CodeReq.ofProg_lookup` — the same mechanism as `d128_v4_sub`. -/
def divKDiv128Step2V4Instrs : List Instr :=
  [.DIVU .x5 .x7 .x6,   .MUL .x1 .x5 .x6,   .SUB .x11 .x7 .x1,   -- [0..2]
   .SRLI .x1 .x5 32,     .BEQ .x1 .x0 12,     .ADDI .x5 .x5 4095,   -- [3..5]
   .ADD .x11 .x11 .x6,   .SRLI .x1 .x11 32,   .BNE .x1 .x0 92,      -- [6..8]
   .LD .x1 .x12 3952,    .MUL .x7 .x5 .x1,    .SLLI .x1 .x11 32,    -- [9..11]
   .SD .x12 .x11 3936,   .LD .x11 .x12 3944,  .OR .x1 .x1 .x11,     -- [12..14]
   .BLTU .x1 .x7 12,     .LD .x11 .x12 3936,  .JAL .x0 16,           -- [15..17]
   .ADDI .x5 .x5 4095,   .LD .x11 .x12 3936,  .ADD .x11 .x11 .x6,   -- [18..20]
   .SRLI .x1 .x11 32,    .BNE .x1 .x0 36,     .LD .x1 .x12 3952,    -- [21..23]
   .MUL .x7 .x5 .x1,    .SLLI .x1 .x11 32,   .LD .x11 .x12 3944,   -- [24..26]
   .OR .x1 .x1 .x11,    .BLTU .x1 .x7 8,     .JAL .x0 8,            -- [27..29]
   .ADDI .x5 .x5 4095]                                                  -- [30]

/-- Bundled CodeReq for `divK_div128_step2_v4_spec`. Expressed as
    `CodeReq.ofProg` (not union-of-singletons) so `step2v4_sub` can
    use `ofProg_lookup` — same pattern as `d128_v4_sub` for the full
    `divK_div128_v4` program. `@[irreducible]` to keep let-bindings
    out of theorem signatures. -/
@[irreducible]
def divKDiv128Step2V4Code (base : Word) : CodeReq :=
  CodeReq.ofProg base divKDiv128Step2V4Instrs

private theorem divKDiv128Step2V4Instrs_len : divKDiv128Step2V4Instrs.length = 31 := by decide

/-- Per-instruction subsumption: singleton at byte-offset `4*k` of
    `divKDiv128Step2V4Code base` is included in the CodeReq.
    Exactly analogous to `d128_v4_sub` for the full `divK_div128_v4`
    program — avoids repeating the union-of-singletons form. -/
private theorem step2v4_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < 31)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : divKDiv128Step2V4Instrs.get ⟨k, by
        have := divKDiv128Step2V4Instrs_len; omega⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divKDiv128Step2V4Code base) a = some i := by
  subst h_addr; subst h_instr; unfold divKDiv128Step2V4Code
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup base divKDiv128Step2V4Instrs k (by
        have := divKDiv128Step2V4Instrs_len; omega) (by decide)) a i h

/-- The single BLTU dispatch at the start of Phase D, extended into the
    step2-v4 code requirement. The semantic path bodies are proved separately. -/
private theorem divK_div128_step2_v4_phase_D_bltu_spec
    (rhat2Un0 q0Dlo1 : Word) (base : Word) :
    cpsBranch (base + 60) (divKDiv128Step2V4Code base)
      ((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1))
      (base + 72)
        ((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜BitVec.ult rhat2Un0 q0Dlo1⌝)
      (base + 64)
        ((.x1 ↦ᵣ rhat2Un0) ** (.x7 ↦ᵣ q0Dlo1) ** ⌜¬BitVec.ult rhat2Un0 q0Dlo1⌝) := by
  have hbltu_raw := bltu_spec_gen .x1 .x7 (12 : BitVec 13) rhat2Un0 q0Dlo1 (base + 60)
  have ha_t : (base + 60) + signExtend13 (12 : BitVec 13) = base + 72 := by rv64_addr
  have ha_f : (base + 60 : Word) + 4 = base + 64 := by bv_addr
  rw [ha_t, ha_f] at hbltu_raw
  exact cpsBranch_extend_code (h := hbltu_raw) (hmono := by
    exact step2v4_sub 15 (base+60) (.BLTU .x1 .x7 12)
      (by omega) (by bv_omega) (by decide))

/-- The SRLI+BNE dispatch at the start of Phase E, extended into the step2-v4
    code requirement and framed with the registers/memory live across it. -/
private theorem divK_div128_step2_v4_phase_E_guard_spec
    (sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c : Word) (base : Word) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
    cpsBranch (base + 84) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x1 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      (base + 124)
        ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x11 ↦ᵣ rhat2') ** (.x1 ↦ᵣ rhat2'Hi) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi ≠ 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c))
      (base + 92)
        ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
         (.x11 ↦ᵣ rhat2') ** (.x1 ↦ᵣ rhat2'Hi) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ ** ⌜rhat2'Hi = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
         (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro rhat2cHi rhat2'Hi
  have hraw := divK_div128_phase2b_guard_spec sp rhat2' rhat2Un0 (base + 84) (36 : BitVec 13)
  simp only [show (base + 84 : Word) + 4 = base + 88 from by bv_addr,
             show (base + 84 : Word) + 8 = base + 92 from by bv_addr,
             show (base + 88 : Word) + signExtend13 (36 : BitVec 13) = base + 124 from by
               rv64_addr] at hraw
  have hguard : cpsBranch (base + 84) (divKDiv128Step2V4Code base) _ _ _ _ _ :=
    cpsBranch_extend_code (h := hraw) (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 21 (base+84) (.SRLI .x1 .x11 32) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 22 (base+88) (.BNE .x1 .x0 36) (by omega) (by bv_omega) (by decide)))
  have hframed := cpsBranch_frameR
    ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
     ⌜rhat2cHi = 0⌝ **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ rhat2c))
    (by pcFree) hguard
  exact cpsBranch_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hframed

/-- Bundled postcondition for `divK_div128_step2_v4_spec`. Hides the
    let-chain for Step 2 v4 trial-division intermediates + Phase 2b
    1st+2nd D3 outcomes.

    The key output is `q0''` (post-2nd-D3 correction), which is what
    `div128Quot_v4` computes. Other registers (x1, x6, x7, x11) hold
    transient end-of-block values that depend on the BLTU path taken;
    the postcondition encodes them via if-then-else on the relevant
    BLTU/BNE conditions. -/
@[irreducible]
def divKDiv128Step2V4Post (sp un21 dHi dlo un0 vScratchOld : Word) : Assertion :=
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dlo            -- product for 1st D3 check
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  -- Phase 2b 1st D3 result (if outer guard doesn't fire).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  -- Post-1st-D3 rhat2: equals rhat2c + dHi if 1st BLTU fired, else rhat2c.
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dlo            -- product for 2nd D3 check
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  -- Phase 2b 2nd D3 result.
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  -- Exit register state at [71]:
  -- x7: un21 (outer BNE) | q0c*dlo (2nd BNE) | q0'*dlo (2nd D3 ran).
  let x7Exit := if rhat2cHi ≠ 0 then un21
                else if rhat2'Hi ≠ 0 then q0Dlo1
                else q0Dlo2
  -- x1: rhat2cHi (outer BNE) | rhat2'Hi (2nd BNE) | rhat2'*2^32|un0 (2nd D3 ran).
  let x1Exit := if rhat2cHi ≠ 0 then rhat2cHi
                else if rhat2'Hi ≠ 0 then rhat2'Hi
                else rhat2'Un0
  -- x11: rhat2c (outer BNE) | rhat2' (2nd BNE) | un0 (2nd D3 ran).
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c
                 else if rhat2'Hi ≠ 0 then rhat2'
                 else un0
  -- mem3936: vScratchOld if outer BNE fired (SD at [52] not reached),
  --          else rhat2c (saved at [52]).
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
  (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ mem3936Exit)

/-- Phase D sub-lemma: BLTU+paths [15..20] of step2_v4, merged post.
    Input = midC (= output of Phase C at base+60).
    Output = midD (post-BLTU merged state at base+84).
    by_cases on ult for taken/not-taken paths; by_cases on rhat2cHi for vacuity.
    Proof outline:
    - if rhat2cHi ≠ 0: pre (⌜rhat2cHi=0⌝) is False → vacuous.
    - if rhat2cHi = 0, ult = true (taken path [18..20]):
        strip ⌜ult⌝ from pre, run ADDI+LD+ADD via runBlock.
    - if rhat2cHi = 0, ult = false (not-taken path [16..17]):
        strip ⌜¬ult⌝ from pre, run LD+JAL via runBlock. -/
theorem divK_div128_step2_v4_phase_D_merged_spec
    (sp dHi q0c rhat2c dlo un0 : Word) (base : Word) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let q0Dlo1   := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let q0'      := div128Quot_phase2b_q0' q0c rhat2c dlo un0
    let rhat2'   := if rhat2cHi = 0 then
                      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
                    else rhat2c
    cpsTriple (base + 60) (base + 84) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
       (.x11 ↦ᵣ un0) ** (.x1 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x1 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro rhat2cHi q0Dlo1 rhat2Un0 q0' rhat2'
  have hbltu := divK_div128_step2_v4_phase_D_bltu_spec rhat2Un0 q0Dlo1 base
  -- Remaining proof split:
  -- * taken path: [18..20] ADDI; LD; ADD with `add_spec_gen_rd_eq_rs1`
  -- * fallthrough path: [16..17] LD; JAL
  -- Both paths then rewrite `div128Quot_phase2b_q0'` under the carried
  -- `rhat2cHi = 0` fact and strip the BLTU pure fact.
  sorry

/-- Phase E sub-lemma: 2nd D3 guard+prodcheck [21..30] of step2_v4, merged post.
    Input = midD (at base+84). Output = finalPost_rhat2cHi0 (at base+124).
    by_cases on rhat2'Hi for guard taken/not-taken.
    Proof outline:
    - if rhat2cHi ≠ 0: midD pre (⌜rhat2cHi=0⌝) is False → vacuous.
    - if rhat2cHi = 0 and rhat2'Hi ≠ 0 (guard fires): identity, q0''=q0'.
    - if rhat2cHi = 0 and rhat2'Hi = 0:
        prodcheck2_merged_spec at base+92, extended via step2v4_sub 23..30. -/
theorem divK_div128_step2_v4_phase_E_merged_spec
    (sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c : Word) (base : Word) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
    let q0Dlo2   := q0' * dlo
    let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
    let q0''     := div128Quot_phase2b_q0' q0' rhat2' dlo un0
    let x7Exit   := if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2
    let x1Exit   := if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0
    let x11Exit  := if rhat2'Hi ≠ 0 then rhat2' else un0
    cpsTriple (base + 84) (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x11 ↦ᵣ rhat2') ** (.x1 ↦ᵣ rhat2Un0) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c))
      ((.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
       (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ rhat2c)) := by
  intro rhat2cHi rhat2'Hi q0Dlo2 rhat2'Un0 q0'' x7Exit x1Exit x11Exit
  have hguard := divK_div128_step2_v4_phase_E_guard_spec
    sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c base
  -- Remaining proof split:
  -- * guard-taken path: zero-step bridge at base+124, using `rhat2'Hi ≠ 0`
  -- * guard-fallthrough path: reuse `divK_div128_prodcheck2_merged_spec`
  --   over [23..30], then bridge its unguarded quotient to `q0''` using
  --   `rhat2'Hi = 0`.
  sorry

/-- **STUB**: full v4 Phase 2 spec — instructions [40..70] of `divK_div128_v4`.

    Proof structure (5 blocks in `divK_div128_step2_v4_spec`):
    - Block 1 [0..28]  (hA): init+clamp  → `cpsTriple base (base+28)`.
    - Block 2 [28..36] (hB): outer SRLI+BNE guard → `cpsBranch (base+28)`.
    - Compose hA+hB → `cpsBranch base (base+124) | (base+36)`.
    - Taken (rhat2cHi≠0): `h_taken` identity at base+124.
    - Not-taken (rhat2cHi=0): `h_notTaken` = Block3(hC) + Block4(hD) + Block5(hE).
      Block 3 [36..60] (hC): pre-BLTU setup via runBlock.
      Block 4 [60..84] (hD): BLTU+paths via `phase_D_merged_spec`.
      Block 5 [84..124](hE): 2nd D3 guard+prodcheck via `phase_E_merged_spec`. -/
theorem divK_div128_step2_v4_spec
    (sp un21 dHi v1Old v5Old v11Old dlo un0 vScratchOld : Word) (base : Word) :
    cpsTriple base (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) **
       (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      (divKDiv128Step2V4Post sp un21 dHi dlo un0 vScratchOld) := by
  unfold divKDiv128Step2V4Post
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dlo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dlo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  let x7Exit := if rhat2cHi ≠ 0 then un21
                else if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2
  let x1Exit := if rhat2cHi ≠ 0 then rhat2cHi
                else if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c
                 else if rhat2'Hi ≠ 0 then rhat2' else un0
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  -- Phase A: init+clamp [0..28] — cpsTriple base (base+28).
  -- Reuse divK_div128_step2_upto_guard_spec, extend via step2v4_sub 0..6.
  have hA_raw := divK_div128_step2_upto_guard_spec sp un21 dHi v1Old v5Old v11Old dlo un0 base
  have hA : cpsTriple base (base + 28) (divKDiv128Step2V4Code base) _ _ :=
    cpsTriple_extend_code (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 0 base (.DIVU .x5 .x7 .x6) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 1 (base+4) (.MUL .x1 .x5 .x6) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 2 (base+8) (.SUB .x11 .x7 .x1) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 3 (base+12) (.SRLI .x1 .x5 32) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 4 (base+16) (.BEQ .x1 .x0 12) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 5 (base+20) (.ADDI .x5 .x5 4095) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 6 (base+24) (.ADD .x11 .x11 .x6) (by omega) (by bv_omega) (by decide))))))))
    hA_raw
  have hAf := cpsTriple_frameR
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
    (by pcFree) hA
  -- Phase B: outer SRLI+BNE guard [28..36] — cpsBranch via step2v4_sub 7+8.
  have hB_raw := divK_div128_phase2b_guard_spec sp rhat2c hi (base + 28) (92 : BitVec 13)
  simp only [show (base + 28 : Word) + 4 = base + 32 from by bv_addr,
             show (base + 28 : Word) + 8 = base + 36 from by bv_addr,
             show (base + 32 : Word) + signExtend13 (92 : BitVec 13) = base + 124 from by
               rv64_addr] at hB_raw
  have hB : cpsBranch (base + 28) (divKDiv128Step2V4Code base) _ _ _ _ _ :=
    cpsBranch_extend_code (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 7 (base+28) (.SRLI .x1 .x11 32) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 8 (base+32) (.BNE .x1 .x0 92) (by omega) (by bv_omega) (by decide))) hB_raw
  have hBf := cpsBranch_frameR
    ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ vScratchOld))
    (by pcFree) hB
  have composed_AB := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  -- finalPost (merged post at base+124 for both legs).
  let finalPost : Assertion :=
    (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
    (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ mem3936Exit)
  -- Taken leg (rhat2cHi ≠ 0): BNE fires, already at base+124.
  -- q0'' = q0c (both D3 guards fire), x7=un21, x1=rhat2cHi, x11=rhat2c, mem3936=vScratchOld.
  -- The taken postcondition of composed_AB:
  let takenPost : Assertion :=
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2cHi) **
     (.x0 ↦ᵣ 0) ** ⌜rhat2cHi ≠ 0⌝) **
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
  have h_taken : cpsTriple (base + 124) (base + 124) (divKDiv128Step2V4Code base)
      takenPost finalPost :=
    cpsTriple_extend_code (hmono := fun _ _ h => by simp [CodeReq.empty] at h)
    (cpsTriple_refl (by
      intro hp htp
      -- Extract ⌜rhat2cHi ≠ 0⌝ from takenPost (inside a have so htp survives).
      -- takenPost = (.x12 ** .x11 ** .x1 ** .x0 ** ⌜rhat2cHi ≠ 0⌝) ** rest.
      have h_ne : rhat2cHi ≠ 0 := by
        obtain ⟨_, _, _, _, hleft, _⟩ := htp
        obtain ⟨_, _, _, _, _, h1⟩ := hleft  -- peel .x12
        obtain ⟨_, _, _, _, _, h2⟩ := h1     -- peel .x11
        obtain ⟨_, _, _, _, _, h3⟩ := h2     -- peel .x1
        obtain ⟨_, _, _, _, _, h4⟩ := h3     -- peel .x0
        obtain ⟨_, hpure⟩ := h4             -- ⌜rhat2cHi ≠ 0⌝
        exact hpure
      -- When rhat2cHi ≠ 0: both D3 guards skip → q0'' = q0c.
      have hq0' : q0' = q0c := by
        show div128Quot_phase2b_q0' q0c rhat2c dlo un0 = q0c
        simp only [div128Quot_phase2b_q0']; exact if_neg h_ne
      have hrhat2' : rhat2' = rhat2c := by
        show (if rhat2cHi = 0 then _ else rhat2c) = rhat2c
        exact if_neg h_ne
      have hq0'' : q0'' = q0c := by
        show div128Quot_phase2b_q0' q0' rhat2' dlo un0 = q0c
        rw [hq0', hrhat2']
        simp only [div128Quot_phase2b_q0']; exact if_neg h_ne
      have hx7 : x7Exit = un21   := by show (if rhat2cHi ≠ 0 then un21 else _) = un21; exact if_pos h_ne
      have hx1 : x1Exit = rhat2cHi := by show (if rhat2cHi ≠ 0 then rhat2cHi else _) = rhat2cHi; exact if_pos h_ne
      have hx11 : x11Exit = rhat2c  := by show (if rhat2cHi ≠ 0 then rhat2c else _) = rhat2c; exact if_pos h_ne
      have hmem : mem3936Exit = vScratchOld := by show (if rhat2cHi ≠ 0 then vScratchOld else _) = vScratchOld; exact if_pos h_ne
      -- Strip ⌜rhat2cHi ≠ 0⌝ from htp for xperm_hyp.
      -- takenPost = (.x12 ** .x11 ** .x1 ** .x0 ** ⌜...⌝) ** rest.
      -- Strip: 3x sepConj_mono_right to reach .x0 ** ⌜...⌝, then strip.
      have htp' : (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2cHi) ** (.x0 ↦ᵣ 0)) **
          (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ vScratchOld)) hp :=
        sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)))) hp htp
      -- Rewrite finalPost to explicit form, then xperm_hyp htp'.
      show finalPost hp
      rw [show finalPost = ((.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ un21) **
          (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
          (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
          (sp + signExtend12 3952 ↦ₘ dlo) **
          (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ vScratchOld)) from by
        simp only [finalPost, hq0'', hx7, hx1, hx11, hmem]]
      xperm_hyp htp'))
  -- The not-taken postcondition of composed_AB:
  let notTakenPost : Assertion :=
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2cHi) **
     (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝) **
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
  -- Not-taken leg (rhat2cHi = 0): run [36..120] → base+124.
  have h_notTaken : cpsTriple (base + 36) (base + 124) (divKDiv128Step2V4Code base)
      notTakenPost finalPost := by
    -- Phase C: pre-BLTU setup [9..14] = LD+MUL+SLLI+SD+LD+OR.
    let midC : Assertion :=
      (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
      (.x11 ↦ᵣ un0) ** (.x1 ↦ᵣ rhat2Un0) **
      (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
      (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
      (sp + signExtend12 3936 ↦ₘ rhat2c)
    have hC : cpsTriple (base+36) (base+60) (divKDiv128Step2V4Code base)
        notTakenPost midC := by
      apply cpsTriple_extend_code (hmono := by
        exact CodeReq.union_sub (step2v4_sub 9 (base+36) (.LD .x1 .x12 3952) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 10 (base+40) (.MUL .x7 .x5 .x1) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 11 (base+44) (.SLLI .x1 .x11 32) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 12 (base+48) (.SD .x12 .x11 3936) (by omega) (by bv_omega) (by decide))
         (CodeReq.union_sub (step2v4_sub 13 (base+52) (.LD .x11 .x12 3944) (by omega) (by bv_omega) (by decide))
          (step2v4_sub 14 (base+56) (.OR .x1 .x1 .x11) (by omega) (by bv_omega) (by decide)))))))
      have I0 := ld_spec_gen .x1 .x12 sp rhat2cHi dlo 3952 (base+36) (by nofun)
      have I1 := mul_spec_gen .x7 .x5 .x1 un21 q0c dlo (base+40) (by nofun)
      have I2 := slli_spec_gen .x1 .x11 dlo rhat2c 32 (base+44) (by nofun)
      have I3 := sd_spec_gen .x12 .x11 sp rhat2c vScratchOld 3936 (base+48)
      have I4 := ld_spec_gen .x11 .x12 sp rhat2c un0 3944 (base+52) (by nofun)
      have I5 := or_spec_gen_rd_eq_rs1 .x1 .x11
            (rhat2c <<< (32 : BitVec 6).toNat) un0 (base+56) (by nofun)
      simp only [show (base+36:Word)+4 = base+40 from by bv_omega,
                 show (base+40:Word)+4 = base+44 from by bv_omega,
                 show (base+44:Word)+4 = base+48 from by bv_omega,
                 show (base+48:Word)+4 = base+52 from by bv_omega,
                 show (base+52:Word)+4 = base+56 from by bv_omega,
                 show (base+56:Word)+4 = base+60 from by bv_omega] at *
      runBlock I0 I1 I2 I3 I4 I5
    -- Phase D: BLTU+paths [15..20] via `divK_div128_step2_v4_phase_D_merged_spec`.
    let midD : Assertion :=
      (.x7 ↦ᵣ q0Dlo1) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
      (.x11 ↦ᵣ rhat2') ** (.x1 ↦ᵣ rhat2Un0) **
      (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝ **
      (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
      (sp + signExtend12 3936 ↦ₘ rhat2c)
    have hD_raw := divK_div128_step2_v4_phase_D_merged_spec sp dHi q0c rhat2c dlo un0 base
    have hD : cpsTriple (base+36) (base+84) (divKDiv128Step2V4Code base) notTakenPost midD :=
      cpsTriple_seq_perm_same_cr (fun h hp => by exact hp) hC hD_raw
    -- Phase E: 2nd D3 guard+prodcheck [21..30] via `divK_div128_step2_v4_phase_E_merged_spec`.
    -- Bridge hE_raw post → finalPost: by_cases on rhat2cHi (midD has ⌜rhat2cHi=0⌝
    -- so ≠0 is vacuous); then reduce outer if-then-else by h_z + xperm.
    have hE : cpsTriple (base+84) (base+124) (divKDiv128Step2V4Code base)
        midD finalPost := by
      have _hE_raw := divK_div128_step2_v4_phase_E_merged_spec
                       sp dHi q0' rhat2' rhat2Un0 q0Dlo1 dlo un0 rhat2c base
      sorry
    exact cpsTriple_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hq => by xperm_hyp hq)
      (cpsTriple_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hD hE)
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsBranch_merge_same_cr composed_AB h_taken h_notTaken)

end EvmAsm.Evm64
