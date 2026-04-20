/-
  EvmAsm.Evm64.DivMod.Compose.Base

  Shared infrastructure for DivMod composition: divCode/modCode definitions,
  program length lemmas, and the skipBlock tactic macro.
-/

import EvmAsm.Evm64.DivMod.LimbSpec
import EvmAsm.Evm64.DivMod.AddrNorm
import EvmAsm.Evm64.DivMod.Compose.Offsets
import EvmAsm.Rv64.AddrNorm

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Program length lemmas (via decide)
-- Non-private so they are accessible from sub-files via skipBlock macro.
-- ============================================================================

theorem divK_phaseA_len : (divK_phaseA 1020).length = 8 := by decide
theorem divK_phaseB_len : divK_phaseB.length = 21 := by decide
theorem divK_clz_len : divK_clz.length = 24 := by decide
theorem divK_phaseC2_len : (divK_phaseC2 172).length = 4 := by decide
theorem divK_normB_len : divK_normB.length = 21 := by decide
theorem divK_normA_len : (divK_normA 40).length = 21 := by decide
theorem divK_copyAU_len : divK_copyAU.length = 9 := by decide
theorem divK_loopSetup_len : (divK_loopSetup 464).length = 4 := by decide
theorem divK_loopBody_len : (divK_loopBody 560 7736).length = 115 := by decide
theorem divK_denorm_len : divK_denorm.length = 25 := by decide
theorem divK_divEpilogue_len : (divK_div_epilogue 24).length = 10 := by decide
theorem divK_zeroPath_len : divK_zeroPath.length = 5 := by decide
theorem divK_nop_len : (ADDI .x0 .x0 0 : Program).length = 1 := by decide
theorem divK_div128_len : divK_div128.length = 49 := by decide
theorem divK_modEpilogue_len : (divK_mod_epilogue 24).length = 10 := by decide

/-- Skip one ofProg block in a right-nested union via range disjointness.
    Closes the disjointness goal using block length lemmas + bv_omega. -/
macro "skipBlock" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range _ _ _ _ (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len,
          divK_modEpilogue_len] at hk1 hk2
        bv_omega)))

-- ============================================================================
-- Full program CodeReq definitions
-- ============================================================================

/-- The full evm_div code split into 14 per-phase CodeReq.ofProg blocks.
    This is the canonical CodeReq for all composed specs.
    Block offsets are named constants defined in `Compose.Offsets` — see
    that file for the canonical layout and drift checks. -/
abbrev divCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24), -- block 10
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 11
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 12
    CodeReq.ofProg (base + div128Off)     divK_div128             -- block 13
  ]

/-- The full evm_mod code split into 14 per-phase CodeReq.ofProg blocks.
    Identical to divCode except block 10 uses divK_mod_epilogue. -/
abbrev modCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24), -- block 10 differs from divCode
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

-- ============================================================================
-- Shared code: blocks common to divCode and modCode (all except epilogue)
-- ============================================================================

/-- Shared code blocks between divCode and modCode (everything except block 10, the epilogue).
    Used as the code requirement for loop body and div128 specs, which are identical
    for DIV and MOD. -/
abbrev sharedDivModCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),     -- block 0
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,            -- block 1
    CodeReq.ofProg (base + clzOff)        divK_clz,               -- block 2
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),     -- block 3
    CodeReq.ofProg (base + normBOff)      divK_normB,             -- block 4
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),        -- block 5
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,            -- block 6
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),   -- block 7
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),-- block 8
    CodeReq.ofProg (base + denormOff)     divK_denorm,            -- block 9
    -- NO epilogue block (this is where divCode and modCode differ)
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,          -- block 10 (was 11)
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),       -- block 11 (was 12)
    CodeReq.ofProg (base + div128Off)     divK_div128             -- block 12 (was 13)
  ]

-- Per-block subsumption: each shared block ⊆ divCode.
-- Blocks 0-9 are at the same union positions; blocks 10-12 (shared) = blocks 11-13 (divCode).
private theorem shared_b0_div (b : Word) : ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left _ _
private theorem shared_b1_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b2_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b3_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b4_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b5_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b6_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b7_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b8_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b9_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b10_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b11_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + nopOff) (ADDI .x0 .x0 0 : Program)) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b12_div (b : Word) : ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (divCode b) a = some i := by
  unfold divCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _

/-- sharedDivModCode ⊆ divCode: every shared block is also in divCode. -/
theorem sharedDivModCode_sub_divCode (base : Word) :
    ∀ a i, (sharedDivModCode base) a = some i → (divCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono (shared_b0_div base)
    (CodeReq.union_split_mono (shared_b1_div base)
    (CodeReq.union_split_mono (shared_b2_div base)
    (CodeReq.union_split_mono (shared_b3_div base)
    (CodeReq.union_split_mono (shared_b4_div base)
    (CodeReq.union_split_mono (shared_b5_div base)
    (CodeReq.union_split_mono (shared_b6_div base)
    (CodeReq.union_split_mono (shared_b7_div base)
    (CodeReq.union_split_mono (shared_b8_div base)
    (CodeReq.union_split_mono (shared_b9_div base)
    (CodeReq.union_split_mono (shared_b10_div base)
    (CodeReq.union_split_mono (shared_b11_div base)
    (CodeReq.union_split_mono (shared_b12_div base)
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

-- Per-block subsumption for modCode. Same pattern as shared_b*_div — the
-- shared blocks occupy the same union positions in modCode as in divCode.
private theorem shared_b0_mod (b : Word) : ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left _ _
private theorem shared_b1_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b2_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b3_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b4_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b5_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b6_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b7_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b8_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b9_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b10_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b11_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + nopOff) (ADDI .x0 .x0 0 : Program)) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _
private theorem shared_b12_mod (b : Word) : ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (modCode b) a = some i := by
  unfold modCode; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left _ _

/-- sharedDivModCode ⊆ modCode: every shared block is also in modCode.
    Mirror of `sharedDivModCode_sub_divCode`. -/
theorem sharedDivModCode_sub_modCode (base : Word) :
    ∀ a i, (sharedDivModCode base) a = some i → (modCode base) a = some i := by
  unfold sharedDivModCode; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono (shared_b0_mod base)
    (CodeReq.union_split_mono (shared_b1_mod base)
    (CodeReq.union_split_mono (shared_b2_mod base)
    (CodeReq.union_split_mono (shared_b3_mod base)
    (CodeReq.union_split_mono (shared_b4_mod base)
    (CodeReq.union_split_mono (shared_b5_mod base)
    (CodeReq.union_split_mono (shared_b6_mod base)
    (CodeReq.union_split_mono (shared_b7_mod base)
    (CodeReq.union_split_mono (shared_b8_mod base)
    (CodeReq.union_split_mono (shared_b9_mod base)
    (CodeReq.union_split_mono (shared_b10_mod base)
    (CodeReq.union_split_mono (shared_b11_mod base)
    (CodeReq.union_split_mono (shared_b12_mod base)
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

-- ============================================================================
-- Postcondition bundle for loopSetup (shift ≠ 0) path
-- Encapsulates 11 let bindings (shift normalization of b[] and a[]) plus
-- the full 30-atom assertion chain into a single opaque Assertion.
-- Used by all 8 _to_loopSetup_spec theorems (n=1..4, DIV and MOD).
-- ============================================================================

-- ============================================================================
-- Scratch region bundle: 15 memory cells used by the 256-bit DIV/MOD program
-- ============================================================================

/-- The 15 scratch memory cells that the DIV/MOD program reads and writes
    during execution. All live at negative offsets from the stack pointer
    (`sp + signExtend12 …` with 12-bit values ≥ 2048 wrapping to negative).

    Layout:
    - `q0..q3` at `sp + signExtend12 4088/4080/4072/4064` — accumulated quotient digits
    - `u0..u4` at `sp + signExtend12 4056/4048/4040/4032/4024` — normalized dividend
    - `u5..u7` at `sp + signExtend12 4016/4008/4000` — overflow/scratch
    - `shiftMem` at `sp + signExtend12 3992`, `nMem` at `sp + signExtend12 3984`
    - `jMem` at `sp + signExtend12 3976`

    This is the precondition shape — specific starting values for every cell.
    The full-path specs universally-quantify over these values since the program
    overwrites them; the predicate packages them so stack specs aren't littered
    with fifteen `↦ₘ` lines at every call site. -/
@[irreducible]
def divScratchValues (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word) : Assertion :=
  ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
  ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
  ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
  ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
  ((sp + signExtend12 3992) ↦ₘ shiftMem) **
  ((sp + signExtend12 3984) ↦ₘ nMem) **
  ((sp + signExtend12 3976) ↦ₘ jMem)

/-- Unfold `divScratchValues` into its 15 underlying memory atoms. The bundle
    is `@[irreducible]`, so `unfold` won't see through it — this named rewrite
    is the supported way in at call sites (parallel to `divScratchOwn_unfold`). -/
theorem divScratchValues_unfold (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word) :
    divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem =
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
     ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem) **
     ((sp + signExtend12 3984) ↦ₘ nMem) **
     ((sp + signExtend12 3976) ↦ₘ jMem)) := by
  delta divScratchValues; rfl

/-- Mid-tree variant of `divScratchValues_unfold`: threads a `Q` through the
    equality so `rw ←` can fold the 15 atoms into a `divScratchValues` bundle
    **even when they sit in the middle of a longer sepConj chain**. Counterpart
    to `evmWordIs_sp{_,32}_limbs_eq_right`. Used by the DIV/MOD stack-spec
    composition where scratch atoms are scattered across the unfolded
    `fullDivN4MaxSkipPost` post. -/
theorem divScratchValues_unfold_right (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word) (Q : Assertion) :
    (((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
     ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
     ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem) **
     ((sp + signExtend12 3984) ↦ₘ nMem) **
     ((sp + signExtend12 3976) ↦ₘ jMem) ** Q) =
    (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem ** Q) := by
  rw [divScratchValues_unfold]
  iterate 14 rw [sepConj_assoc']

/-- Value-agnostic counterpart to `divScratchValues`: the same 15 cells but
    with ownership only (no commitment to specific values). Suitable for the
    postcondition of a stack-level DIV/MOD spec that doesn't want to expose
    the algorithm's internal scratch state to callers. -/
@[irreducible]
def divScratchOwn (sp : Word) : Assertion :=
  memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
  memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
  memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
  memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
  memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
  memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
  memOwn (sp + signExtend12 3992) **
  memOwn (sp + signExtend12 3984) **
  memOwn (sp + signExtend12 3976)

/-- Named unfold for `divScratchOwn`. Restores access to the underlying
    definition once the `@[irreducible]` attribute has made `delta` the only
    way in at call sites. Parallel to `divScratchValues_unfold`. -/
theorem divScratchOwn_unfold (sp : Word) :
    divScratchOwn sp =
    (memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
     memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
     memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
     memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
     memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
     memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
     memOwn (sp + signExtend12 3992) **
     memOwn (sp + signExtend12 3984) **
     memOwn (sp + signExtend12 3976)) := by
  delta divScratchOwn; rfl

/-- Mid-tree variant of `divScratchOwn_unfold`: threads a `Q` through the
    equality so `rw ←` can fold the 15 ownership atoms into a `divScratchOwn`
    bundle **even when they sit in the middle of a longer sepConj chain**.
    Parallel to `divScratchValues_unfold_right`. -/
theorem divScratchOwn_unfold_right (sp : Word) (Q : Assertion) :
    ((memOwn (sp + signExtend12 4088) ** memOwn (sp + signExtend12 4080) **
      memOwn (sp + signExtend12 4072) ** memOwn (sp + signExtend12 4064) **
      memOwn (sp + signExtend12 4056) ** memOwn (sp + signExtend12 4048) **
      memOwn (sp + signExtend12 4040) ** memOwn (sp + signExtend12 4032) **
      memOwn (sp + signExtend12 4024) ** memOwn (sp + signExtend12 4016) **
      memOwn (sp + signExtend12 4008) ** memOwn (sp + signExtend12 4000) **
      memOwn (sp + signExtend12 3992) **
      memOwn (sp + signExtend12 3984) **
      memOwn (sp + signExtend12 3976)) ** Q) =
    (divScratchOwn sp ** Q) := by
  rw [divScratchOwn_unfold]

theorem pcFree_divScratchValues (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem : Word) :
    (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem).pcFree := by
  unfold divScratchValues; pcFree

instance (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    Assertion.PCFree (divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem) :=
  ⟨pcFree_divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem⟩

/-- `divScratchOwn` is pc-free: all its 15 atoms are `memOwn`. Proof goes
    through the `_unfold` rewrite since the bundle is `@[irreducible]`. -/
theorem pcFree_divScratchOwn (sp : Word) : (divScratchOwn sp).pcFree := by
  rw [divScratchOwn_unfold]; pcFree

instance pcFreeInst_divScratchOwn (sp : Word) :
    Assertion.PCFree (divScratchOwn sp) :=
  ⟨pcFree_divScratchOwn sp⟩

/-- Weakening: any concrete scratch state implies ownership of the same 15
    cells. This lets a stack spec hide the scratch values on exit. -/
theorem divScratchValues_implies_divScratchOwn
    (sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem : Word) :
    ∀ h, divScratchValues sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem h → divScratchOwn sp h := by
  unfold divScratchValues divScratchOwn
  -- Weaken each of the 15 memIs cells to memOwn, left to right.
  iterate 14 apply sepConj_mono (memIs_implies_memOwn _ _)
  exact memIs_implies_memOwn _ _

/-- Postcondition for the shift≠0 path from entry to loop setup.
    Encapsulates the shift/antiShift computation, normalized b'[0..3],
    and normalized u[0..4] as internal let bindings.
    Marked @[irreducible] so xperm treats this as 1 opaque atom. -/
@[irreducible]
def loopSetupPost (sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ nVal) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
  (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - nVal) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
  ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
  ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ u4) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
  ((sp + signExtend12 3992) ↦ₘ shift)

/-- Unfold the opaque loopSetupPost back to its expanded form. -/
theorem loopSetupPost_unfold (sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
    let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
    let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
    let u0 := a0 <<< (shift.toNat % 64)
    (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ nVal) ** (.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
    (.x0 ↦ᵣ (0 : Word)) **
    (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
    (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - nVal) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
    ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
    ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
    ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
    ((sp + signExtend12 4024) ↦ₘ u4) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta loopSetupPost; rfl

/-- `loopSetupPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_loopSetupPost (sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  rw [loopSetupPost_unfold]; pcFree

instance pcFreeInst_loopSetupPost
    (sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_loopSetupPost sp nVal shift a0 a1 a2 a3 b0 b1 b2 b3⟩

-- ============================================================================
-- Postcondition bundles for denorm + epilogue paths
-- ============================================================================

/-- Postcondition for DIV denorm + epilogue (shift ≠ 0).
    Encapsulates antiShift and denormalized u'[0..3]. -/
@[irreducible]
def denormDivPost (sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
  (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
  ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
  ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
  ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
  ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
  ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
  ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)

theorem denormDivPost_unfold (sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word) :
    denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
    (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
    ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
    ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
    ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
    ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
    ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
    ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3) := by
  delta denormDivPost; rfl

/-- `denormDivPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_denormDivPost (sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word) :
    (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3).pcFree := by
  rw [denormDivPost_unfold]; pcFree

instance pcFreeInst_denormDivPost (sp shift u0 u1 u2 u3 q0 q1 q2 q3 : Word) :
    Assertion.PCFree (denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3) :=
  ⟨pcFree_denormDivPost sp shift u0 u1 u2 u3 q0 q1 q2 q3⟩

/-- Postcondition for MOD denorm + epilogue (shift ≠ 0).
    Encapsulates antiShift and denormalized u'[0..3]. -/
@[irreducible]
def denormModPost (sp shift u0 u1 u2 u3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0') ** (.x6 ↦ᵣ u1') ** (.x7 ↦ᵣ u2') **
  (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3') **
  ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
  ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
  ((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
  ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3')

theorem denormModPost_unfold (sp shift u0 u1 u2 u3 : Word) :
    denormModPost sp shift u0 u1 u2 u3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0') ** (.x6 ↦ᵣ u1') ** (.x7 ↦ᵣ u2') **
    (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ u3') **
    ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
    ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
    ((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
    ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3') := by
  delta denormModPost; rfl

/-- `denormModPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_denormModPost (sp shift u0 u1 u2 u3 : Word) :
    (denormModPost sp shift u0 u1 u2 u3).pcFree := by
  rw [denormModPost_unfold]; pcFree

instance pcFreeInst_denormModPost (sp shift u0 u1 u2 u3 : Word) :
    Assertion.PCFree (denormModPost sp shift u0 u1 u2 u3) :=
  ⟨pcFree_denormModPost sp shift u0 u1 u2 u3⟩

-- ============================================================================
-- Postcondition bundle for normB (PhaseAB + CLZ + PhaseC2 + NormB)
-- ============================================================================

/-- Postcondition after PhaseAB + CLZ + PhaseC2(ntaken) + NormB.
    Encapsulates shift, antiShift, and normalized b'[0..3]. -/
@[irreducible]
def normBPost (sp nVal shift b0 b1 b2 b3 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
  (.x2 ↦ᵣ antiShift) **
  ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
  ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
  ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
  ((sp + signExtend12 3992) ↦ₘ shift)

theorem normBPost_unfold (sp nVal shift b0 b1 b2 b3 : Word) :
    normBPost sp nVal shift b0 b1 b2 b3 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
    let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
    let b0' := b0 <<< (shift.toNat % 64)
    (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b0') ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ (b0 >>> (antiShift.toNat % 64))) **
    (.x2 ↦ᵣ antiShift) **
    ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
    ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
    ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ nVal) **
    ((sp + signExtend12 3992) ↦ₘ shift) := by
  delta normBPost; rfl

/-- `normBPost` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_normBPost (sp nVal shift b0 b1 b2 b3 : Word) :
    (normBPost sp nVal shift b0 b1 b2 b3).pcFree := by
  rw [normBPost_unfold]; pcFree

instance pcFreeInst_normBPost (sp nVal shift b0 b1 b2 b3 : Word) :
    Assertion.PCFree (normBPost sp nVal shift b0 b1 b2 b3) :=
  ⟨pcFree_normBPost sp nVal shift b0 b1 b2 b3⟩

-- ============================================================================
-- `se12_32`/`se12_40`/`se12_48`/`se12_56` were deleted by issue #493 / #494:
-- they now live canonically in `Rv64/AddrNorm.lean` as part of the
-- `rv64_addr` grindset. Consumers should `open EvmAsm.Rv64.AddrNorm
-- (se12_32 se12_40 se12_48 se12_56)` directly instead of relying on these
-- duplicates.
-- ============================================================================

-- ============================================================================
-- Shared `phB_off_*` address rewrites.
-- `base + phaseBOff` is the entry PC of `divK_phaseB` (and the structurally
-- identical block in `modCode`). `phB_off_k` rewrites `(base + phaseBOff) + k`
-- to `base + (phaseBOff + k)` with the constant folded on the RHS, so that
-- `simp only [phB_off_k]` closes the address-matching goal that appears when
-- a `divK_phaseB_*` sub-spec is embedded in `divCode base` / `modCode base`.
-- Consumers: PhaseAB.lean (DIV side), ModPhaseB.lean, ModPhaseBn3.lean,
-- ModPhaseBn21.lean (MOD side). Previously duplicated as `private phB_off_*`
-- in PhaseAB.lean and `mod_phB_off_28` in ModPhaseB.lean.
-- ============================================================================

theorem phB_off_28 (base : Word) : (base + phaseBOff : Word) + 28 = base + 60 := by bv_addr

-- n=4 special: x1 = signExtend12 4 - 4 = 0, used by the shift-0 fast path
-- and the main `FullPathN4` path. Shared here so the two consumer files
-- (`FullPathN4.lean`, `FullPathN4Shift0.lean`) don't re-declare it privately.
theorem x1_val_n4 : signExtend12 (4 : BitVec 12) - (4 : Word) = (0 : Word) := by decide

-- Shared `signExtend13`/`signExtend21` evaluations for these seven concrete
-- offsets (8, 16, 24, 172, 464, 1020 and 21_40) used to live here as
-- `theorem signExtend13_N`. They have been migrated to the repo-wide
-- `rv64_addr` grindset (GRIND.md Phase 3): see `EvmAsm/Rv64/AddrNorm.lean`
-- for `se13_N` / `se21_N`. Consumer files `open EvmAsm.Rv64.AddrNorm (…)`
-- and rewrite via `simp only [se13_N]` / `rw [se13_N]` directly.

/-- When b ≠ 0, 0 < b in unsigned ordering (BitVec.ult). -/
theorem ult_zero_of_ne {b : Word} (h : b ≠ 0) : BitVec.ult 0 b := by
  unfold BitVec.ult; simp
  exact Nat.pos_of_ne_zero (fun h0 => h (by exact BitVec.eq_of_toNat_eq h0))

end EvmAsm.Evm64
