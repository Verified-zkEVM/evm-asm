/-
  EvmAsm.Evm64.DivMod.Compose.V5Code2

  Full DIV/MOD CodeReq bundles for the v5 div128 migration.

  Mechanical mirror of `EvmAsm.Evm64.DivMod.Compose.V4Code`, swapping
  `divK_div128_v4` → `divK_div128_v5` at the `div128Off` block. All other
  13 blocks are identical. The no-NOP bundles live in `Compose.V5NoNop`.
-/

import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Rv64.CPSSpec

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 DIV code bundle: mirror of `divCode_v4` with `divK_div128_v5` at
    the final `div128Off` block. -/
abbrev divCode_v5 (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + div128Off)     divK_div128_v5          -- block 13 (v5)
  ]

/-- v5 MOD code bundle: mirror of `modCode_v4` with `divK_div128_v5` at
    the final `div128Off` block. -/
abbrev modCode_v5 (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + nopOff)        (ADDI .x0 .x0 0),
    CodeReq.ofProg (base + div128Off)     divK_div128_v5
  ]

/-- v5 div128 block is included in the full DIV v5 code surface. -/
theorem div128_v5_ofProg_sub_divCode_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128_v5) a = some i →
      (divCode_v5 base) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left

/-- v5 div128 block is included in the full MOD v5 code surface. -/
theorem div128_v5_ofProg_sub_modCode_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128_v5) a = some i →
      (modCode_v5 base) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock
  exact CodeReq.union_mono_left

-- Per-block bridge from the no-NOP v5 DIV surface to the full DIV v5 bundle.
private theorem noNop_v5_b0_div {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left
private theorem noNop_v5_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b3_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b5_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b7_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b8_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b10_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b11_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (divCode_v5 b) a = some i := by
  unfold divCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

/-- The DIV no-NOP v5 surface is included in the full DIV v5 code bundle. -/
theorem divCode_noNop_v5_sub_divCode_v5 {base : Word} :
    ∀ a i, (divCode_noNop_v5 base) a = some i → (divCode_v5 base) a = some i := by
  unfold divCode_noNop_v5; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono noNop_v5_b0_div
    (CodeReq.union_split_mono noNop_v5_b1_div
    (CodeReq.union_split_mono noNop_v5_b2_div
    (CodeReq.union_split_mono noNop_v5_b3_div
    (CodeReq.union_split_mono noNop_v5_b4_div
    (CodeReq.union_split_mono noNop_v5_b5_div
    (CodeReq.union_split_mono noNop_v5_b6_div
    (CodeReq.union_split_mono noNop_v5_b7_div
    (CodeReq.union_split_mono noNop_v5_b8_div
    (CodeReq.union_split_mono noNop_v5_b9_div
    (CodeReq.union_split_mono noNop_v5_b10_div
    (CodeReq.union_split_mono noNop_v5_b11_div
    (CodeReq.union_split_mono div128_v5_ofProg_sub_divCode_v5
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

/-- Lift a DIV proof over the no-NOP v5 code surface to the full v5 bundle. -/
theorem cpsTripleWithin_divCode_noNop_v5_to_divCode_v5
    {nSteps : Nat} {entry exit_ base : Word} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ (divCode_noNop_v5 base) P Q) :
    cpsTripleWithin nSteps entry exit_ (divCode_v5 base) P Q := by
  exact cpsTripleWithin_extend_code (hmono := divCode_noNop_v5_sub_divCode_v5) h

-- Per-block bridge from the no-NOP v5 MOD surface to the full MOD v5 bundle.
private theorem noNop_v5_b0_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left
private theorem noNop_v5_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b3_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b5_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b7_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b8_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b10_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem noNop_v5_b11_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (modCode_v5 b) a = some i := by
  unfold modCode_v5; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

/-- The MOD no-NOP v5 surface is included in the full MOD v5 code bundle. -/
theorem modCode_noNop_v5_sub_modCode_v5 {base : Word} :
    ∀ a i, (modCode_noNop_v5 base) a = some i → (modCode_v5 base) a = some i := by
  unfold modCode_noNop_v5; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono noNop_v5_b0_mod
    (CodeReq.union_split_mono noNop_v5_b1_mod
    (CodeReq.union_split_mono noNop_v5_b2_mod
    (CodeReq.union_split_mono noNop_v5_b3_mod
    (CodeReq.union_split_mono noNop_v5_b4_mod
    (CodeReq.union_split_mono noNop_v5_b5_mod
    (CodeReq.union_split_mono noNop_v5_b6_mod
    (CodeReq.union_split_mono noNop_v5_b7_mod
    (CodeReq.union_split_mono noNop_v5_b8_mod
    (CodeReq.union_split_mono noNop_v5_b9_mod
    (CodeReq.union_split_mono noNop_v5_b10_mod
    (CodeReq.union_split_mono noNop_v5_b11_mod
    (CodeReq.union_split_mono div128_v5_ofProg_sub_modCode_v5
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

/-- Lift a MOD proof over the no-NOP v5 code surface to the full v5 bundle. -/
theorem cpsTripleWithin_modCode_noNop_v5_to_modCode_v5
    {nSteps : Nat} {entry exit_ base : Word} {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ (modCode_noNop_v5 base) P Q) :
    cpsTripleWithin nSteps entry exit_ (modCode_v5 base) P Q := by
  exact cpsTripleWithin_extend_code (hmono := modCode_noNop_v5_sub_modCode_v5) h

end EvmAsm.Evm64
