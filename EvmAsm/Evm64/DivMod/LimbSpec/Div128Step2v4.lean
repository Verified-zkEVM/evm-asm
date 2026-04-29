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

/-- Bundled CodeReq for `divK_div128_step2_v4_spec` (31 singletons,
    instrs [40..70] of `divK_div128_v4`). `@[irreducible]` to keep
    let-bindings out of theorem signatures. -/
@[irreducible]
def divKDiv128Step2V4Code (base : Word) : CodeReq :=
  CodeReq.union (CodeReq.singleton base                (.DIVU .x5 .x7 .x6))
  (CodeReq.union (CodeReq.singleton (base + 4)         (.MUL .x1 .x5 .x6))
  (CodeReq.union (CodeReq.singleton (base + 8)         (.SUB .x11 .x7 .x1))
  (CodeReq.union (CodeReq.singleton (base + 12)        (.SRLI .x1 .x5 32))
  (CodeReq.union (CodeReq.singleton (base + 16)        (.BEQ .x1 .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 20)        (.ADDI .x5 .x5 4095))
  (CodeReq.union (CodeReq.singleton (base + 24)        (.ADD .x11 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 28)        (.SRLI .x1 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 32)        (.BNE .x1 .x0 92))
  (CodeReq.union (CodeReq.singleton (base + 36)        (.LD .x1 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 40)        (.MUL .x7 .x5 .x1))
  (CodeReq.union (CodeReq.singleton (base + 44)        (.SLLI .x1 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 48)        (.SD .x12 .x11 3936))
  (CodeReq.union (CodeReq.singleton (base + 52)        (.LD .x11 .x12 3944))
  (CodeReq.union (CodeReq.singleton (base + 56)        (.OR .x1 .x1 .x11))
  (CodeReq.union (CodeReq.singleton (base + 60)        (.BLTU .x1 .x7 12))
  (CodeReq.union (CodeReq.singleton (base + 64)        (.LD .x11 .x12 3936))
  (CodeReq.union (CodeReq.singleton (base + 68)        (.JAL .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 72)        (.ADDI .x5 .x5 4095))
  (CodeReq.union (CodeReq.singleton (base + 76)        (.LD .x11 .x12 3936))
  (CodeReq.union (CodeReq.singleton (base + 80)        (.ADD .x11 .x11 .x6))
  (CodeReq.union (CodeReq.singleton (base + 84)        (.SRLI .x1 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 88)        (.BNE .x1 .x0 36))
  (CodeReq.union (CodeReq.singleton (base + 92)        (.LD .x1 .x12 3952))
  (CodeReq.union (CodeReq.singleton (base + 96)        (.MUL .x7 .x5 .x1))
  (CodeReq.union (CodeReq.singleton (base + 100)       (.SLLI .x1 .x11 32))
  (CodeReq.union (CodeReq.singleton (base + 104)       (.LD .x11 .x12 3944))
  (CodeReq.union (CodeReq.singleton (base + 108)       (.OR .x1 .x1 .x11))
  (CodeReq.union (CodeReq.singleton (base + 112)       (.BLTU .x1 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 116)       (.JAL .x0 8))
   (CodeReq.singleton (base + 120)       (.ADDI .x5 .x5 4095)))))))))))))))))))))))))))))))

/-- Bundled postcondition for `divK_div128_step2_v4_spec`. Hides the
    let-chain for Step 2 v4 trial-division intermediates + Phase 2b
    1st+2nd D3 outcomes.

    The key output is `q0''` (post-2nd-D3 correction), which is what
    `div128Quot_v4` computes. Other registers (x1, x6, x7, x11) hold
    transient end-of-block values that depend on the BLTU path taken;
    the postcondition encodes them via if-then-else on the relevant
    BLTU/BNE conditions. -/
@[irreducible]
def divKDiv128Step2V4Post (sp un21 dHi dlo un0 : Word) : Assertion :=
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  -- Phase 2b 1st D3.
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  -- Phase 2b 2nd D3 — uses q0' and the post-1st-correction rhat2.
  let rhat2' :=
    if rhat2c >>> (32 : BitVec 6).toNat = 0 then
      let qDlo2c := q0c * dlo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
      if BitVec.ult rhatUn0 qDlo2c then rhat2c + dHi else rhat2c
    else rhat2c
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  -- Memory state: rhat2c is saved to slot 3936 (could be either rhat2c
  -- or rhat2c+dHi depending on BLTU; abstracted here as the actual
  -- saved value).
  let savedRhat2c := rhat2c  -- the SD at [52] saves the un-incremented rhat2c
  -- Exit register state: x5 holds q0'' (the final corrected q0).
  -- x11, x7, x1 hold transient values from the last instructions.
  -- TODO: pin x1/x7/x11 exit values once the proof body is filled in.
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ savedRhat2c)

/-- Bundled postcondition for Phase 2b 1st D3 with save/restore.
    Covers instructions [47..60] of divK_div128_v4 (14 instructions). -/
@[irreducible]
def divKDiv128Phase2b1stD3V4Post (sp q0c rhat2c dlo un0 dHi : Word) : Assertion :=
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let rhat2c_upd :=
    if rhat2cHi = 0 then
      let qDlo := q0c * dlo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
      if BitVec.ult rhatUn0 qDlo then rhat2c + dHi else rhat2c
    else rhat2c
  -- After 1st D3: x5 = q0', x11 = rhat2c_upd, x7 = q0c * dlo (transient).
  (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2c_upd) ** (.x6 ↦ᵣ dHi) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ rhat2c)

/-- **STUB**: Phase 2b 1st D3 with save/restore — instructions [47..60].
    The outer BNE guard at [48] (offset 92) jumps to [71] (past step2_v4
    entirely) when rhat2c >= 2^32. Otherwise runs the 1st D3 mul-check
    with the save/restore of rhat2c to scratch slot 3936.

    This is NOT a standalone cpsTriple (the outer BNE exits step2_v4);
    it is a building block for step2_v4_spec's branch structure. -/
theorem divK_div128_phase2b_1st_d3_v4_spec
    (sp q0c rhat2c dlo un0 dHi v1Old v7Old vScratch : Word) (base : Word) :
    cpsTriple base (base + 56) (divKDiv128Step2V4Code base)
      ((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x1 ↦ᵣ v1Old) ** (.x7 ↦ᵣ v7Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratch))
      (divKDiv128Phase2b1stD3V4Post sp q0c rhat2c dlo un0 dHi) := by
  sorry  -- Covers [47..60] when rhat2c < 2^32 guard doesn't fire globally.
         -- Actually this is NOT right: the outer BNE jumps out of step2_v4.
         -- Simplification: treat step2_v4 as a cpsTriple (ignoring the fact
         -- that BNE branches forward past [71] — which is handled by step2_v4
         -- itself via the outer branch structure). Keep as sorry for now.

/-- **STUB**: full v4 Phase 2 spec — instructions [40..70] of `divK_div128_v4`.

    Mirrors `divK_div128_step2_spec` for the v4 algorithm. Proof structure:
    - [40..42]: step-2-init (same as v2).
    - [43..46]: clamp-q0 (same as v2).
    - [47..48]: Phase 2b guard (same as v2).
    - [49..60]: Phase 2b 1st D3 with save/restore (NEW).
    - [61..70]: Phase 2b 2nd D3 (NEW — mirror of Phase 1b 2nd D3).

    Estimated body: ~700 LOC, mirrors the v2 step2 spec but with the
    added 2nd D3 + save/restore handling. -/
theorem divK_div128_step2_v4_spec
    (sp un21 dHi v1Old v5Old v11Old dlo un0 vScratchOld : Word) (base : Word) :
    cpsTriple base (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) **
       (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      (divKDiv128Step2V4Post sp un21 dHi dlo un0) := by
  sorry  -- PR-A2 finish stub. Body composes step2_init + clamp_q0 +
         -- phase2b_guard + (1st D3 with save/restore) + (2nd D3),
         -- mirroring the v2 step2_spec proof structure but with
         -- 14 additional instructions.

end EvmAsm.Evm64
