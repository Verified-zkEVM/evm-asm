/-
  EvmAsm.Evm64.DivMod.Compose.V4NoNop

  Shared no-NOP code surface for v4 div128 migration.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.Base

public section

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 mirror of `sharedDivModCodeNoNop`: shared DIV/MOD blocks with the
    NOP return slot omitted and the final block using `divK_div128_v4`. -/
abbrev sharedDivModCodeNoNop_v4 (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- v4 mirror of `divCode_noNop`: the DIV no-NOP code surface with the
    migrated `divK_div128_v4` block. Keep this separate from the old
    `divCode_noNop` while downstream v1 proofs are still present. -/
abbrev divCode_noNop_v4 (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- v4 mirror of `modCode_noNop`: the MOD no-NOP code surface with the
    migrated `divK_div128_v4` block. -/
abbrev modCode_noNop_v4 (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- v4 div128 block is included in `sharedDivModCodeNoNop_v4 base`. -/
theorem sharedNoNop_b11_div128_v4_sub {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
           (sharedDivModCodeNoNop_v4 b) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

theorem sharedNoNop_v4_b0_div {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b3_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b5_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b7_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b8_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
/-- DIV epilogue block is included in the DIV no-NOP v4 code surface. -/
theorem divNoNop_v4_b10_divEpilogue {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b10_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b11_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
      (divCode_noNop_v4 b) a = some i := by
  unfold divCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

/-- `sharedDivModCodeNoNop_v4 ⊆ divCode_noNop_v4`: every shared no-NOP v4
    block is also present in the DIV no-NOP v4 code bundle. -/
theorem sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4 {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop_v4 base) a = some i →
      (divCode_noNop_v4 base) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono sharedNoNop_v4_b0_div
    (CodeReq.union_split_mono sharedNoNop_v4_b1_div
    (CodeReq.union_split_mono sharedNoNop_v4_b2_div
    (CodeReq.union_split_mono sharedNoNop_v4_b3_div
    (CodeReq.union_split_mono sharedNoNop_v4_b4_div
    (CodeReq.union_split_mono sharedNoNop_v4_b5_div
    (CodeReq.union_split_mono sharedNoNop_v4_b6_div
    (CodeReq.union_split_mono sharedNoNop_v4_b7_div
    (CodeReq.union_split_mono sharedNoNop_v4_b8_div
    (CodeReq.union_split_mono sharedNoNop_v4_b9_div
    (CodeReq.union_split_mono sharedNoNop_v4_b10_div
    (CodeReq.union_split_mono sharedNoNop_v4_b11_div
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))

theorem sharedNoNop_v4_b0_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b3_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b5_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b7_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b8_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
/-- MOD epilogue block is included in the MOD no-NOP v4 code surface. -/
theorem modNoNop_v4_b10_modEpilogue {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b10_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
theorem sharedNoNop_v4_b11_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
      (modCode_noNop_v4 b) a = some i := by
  unfold modCode_noNop_v4; simp only [CodeReq.unionAll_cons]; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left

/-- `sharedDivModCodeNoNop_v4 ⊆ modCode_noNop_v4`: every shared no-NOP v4
    block is also present in the MOD no-NOP v4 code bundle. -/
theorem sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4 {base : Word} :
    ∀ a i, (sharedDivModCodeNoNop_v4 base) a = some i →
      (modCode_noNop_v4 base) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono sharedNoNop_v4_b0_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b1_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b2_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b3_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b4_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b5_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b6_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b7_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b8_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b9_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b10_mod
    (CodeReq.union_split_mono sharedNoNop_v4_b11_mod
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h))))))))))))

end EvmAsm.Evm64
