import EvmAsm.Evm64.DivMod.Callable

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Legacy LP64-callable DIV wrapper pinned to the original one-correction
    `divK_div128` subroutine. This gives existing v1 no-NOP specs a stable
    target when the default callable name migrates to v4. -/
def evm_div_callable_v1 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128

/-- Legacy LP64-callable MOD wrapper pinned to the original one-correction
    `divK_div128` subroutine. -/
def evm_mod_callable_v1 : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;
  divK_div128

theorem evm_div_callable_v1_length : evm_div_callable_v1.length = 319 := by
  unfold evm_div_callable_v1
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_len]

theorem evm_mod_callable_v1_length : evm_mod_callable_v1.length = 319 := by
  unfold evm_mod_callable_v1
  simp only [seq, Program.length_append, divK_phaseA_len, divK_phaseB_len, divK_clz_len,
    divK_phaseC2_len,
    divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
    divK_loopBody_len, divK_denorm_len, divK_modEpilogue_len, divK_zeroPath_len,
    cc_ret_len, divK_div128_len]

/-- Legacy v1 CodeReq layout for `evm_div_callable_v1`. -/
abbrev evm_div_callable_code_v1 (base : Word) : CodeReq :=
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
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

/-- Legacy v1 CodeReq layout for `evm_mod_callable_v1`. -/
abbrev evm_mod_callable_code_v1 (base : Word) : CodeReq :=
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
    cc_ret_code   (base + nopOff),
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

open EvmAsm.Rv64.CodeReq in
theorem evm_div_callable_code_v1_eq_ofProg (base : Word) :
    evm_div_callable_code_v1 base = CodeReq.ofProg base evm_div_callable_v1 := by
  unfold evm_div_callable_code_v1 evm_div_callable_v1 cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_div_epilogue 24).length) =
        base + zeroPathOff by rw [divK_divEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

open EvmAsm.Rv64.CodeReq in
theorem evm_mod_callable_code_v1_eq_ofProg (base : Word) :
    evm_mod_callable_code_v1 base = CodeReq.ofProg base evm_mod_callable_v1 := by
  unfold evm_mod_callable_code_v1 evm_mod_callable_v1 cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_mod_epilogue 24).length) =
        base + zeroPathOff by rw [divK_modEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

-- ----------------------------------------------------------------------------
-- Legacy v1 code subsumption lemmas
-- ----------------------------------------------------------------------------

private theorem callable_b0_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_div_v1 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_div_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i →
      (evm_div_callable_code_v1 b) a = some i := by
  unfold evm_div_callable_code_v1; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

private theorem callable_b0_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_mod_v1 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_mod_v1 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i →
      (evm_mod_callable_code_v1 b) a = some i := by
  unfold evm_mod_callable_code_v1; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

theorem divCode_noNop_sub_div_callable_code_v1 {base : Word} :
    ∀ a i, (divCode_noNop base) a = some i →
           (evm_div_callable_code_v1 base) a = some i := by
  unfold divCode_noNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_div_v1
    (CodeReq.union_split_mono callable_b1_div_v1
    (CodeReq.union_split_mono callable_b2_div_v1
    (CodeReq.union_split_mono callable_b3_div_v1
    (CodeReq.union_split_mono callable_b4_div_v1
    (CodeReq.union_split_mono callable_b5_div_v1
    (CodeReq.union_split_mono callable_b6_div_v1
    (CodeReq.union_split_mono callable_b7_div_v1
    (CodeReq.union_split_mono callable_b8_div_v1
    (CodeReq.union_split_mono callable_b9_div_v1
    (CodeReq.union_split_mono callable_b10_div_v1
    (CodeReq.union_split_mono callable_b11_div_v1
    (CodeReq.union_split_mono callable_b13_div_v1
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

theorem modCode_noNop_sub_mod_callable_code_v1 {base : Word} :
    ∀ a i, (modCode_noNop base) a = some i →
           (evm_mod_callable_code_v1 base) a = some i := by
  unfold modCode_noNop; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_mod_v1
    (CodeReq.union_split_mono callable_b1_mod_v1
    (CodeReq.union_split_mono callable_b2_mod_v1
    (CodeReq.union_split_mono callable_b3_mod_v1
    (CodeReq.union_split_mono callable_b4_mod_v1
    (CodeReq.union_split_mono callable_b5_mod_v1
    (CodeReq.union_split_mono callable_b6_mod_v1
    (CodeReq.union_split_mono callable_b7_mod_v1
    (CodeReq.union_split_mono callable_b8_mod_v1
    (CodeReq.union_split_mono callable_b9_mod_v1
    (CodeReq.union_split_mono callable_b10_mod_v1
    (CodeReq.union_split_mono callable_b11_mod_v1
    (CodeReq.union_split_mono callable_b13_mod_v1
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

theorem evm_div_callable_code_v1_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_div_callable_code_v1 base) a = some i := by
  intro a i h
  apply callable_b12_div_v1
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

theorem evm_mod_callable_code_v1_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_mod_callable_code_v1 base) a = some i := by
  intro a i h
  apply callable_b12_mod_v1
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

theorem evm_div_callable_v1_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (divStackDispatchPost sp a b).pcFree := by
    rw [divStackDispatchPost_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hStackFramed :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPost sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackFramed hRetFramed

theorem evm_div_callable_v1_spec_from_branch_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (divStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact evm_div_callable_v1_spec_from_noNop
    sp base raVal a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch
    (evm_div_stack_spec_noNop
      sp base a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch)

theorem evm_div_callable_v1_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (divStackDispatchPostNoX1 sp a b).pcFree := by
    rw [divStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_div_callable_v1_spec_from_noNop_branch_return_x1 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) := by
  have hpcFreePost : (divStackDispatchPostNoX1 sp a b).pcFree := by
    rw [divStackDispatchPostNoX1_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) branch.returnX1)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_div_callable_v1_spec_from_noNop_branch_return_x1_framed
    {F : Assertion} [Assertion.PCFree F] (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : DivStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.returnX1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1))) :
    cpsTripleWithin (unifiedDivBound + 1) base (branch.returnX1 &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.returnX1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** F)
      ((divStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ branch.returnX1)) ** F) := by
  exact
    cpsTripleWithin_frameR F (by pcFree)
      (evm_div_callable_v1_spec_from_noNop_branch_return_x1
        sp base a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 branch hStack)

theorem evm_div_callable_v1_spec_from_noNop_concrete_preserving_x1_x9
    (sp base x9Val raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  let retFrame : Assertion :=
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x2 ↦ᵣ v2) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        evmWordIs sp a **
        divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0))
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v1 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (retFrame ** (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
      rw [divConcretePostNoX1Frame_unfold] at hp
      dsimp [retFrame] at hp ⊢
      xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL retFrame
      (by
        dsimp [retFrame]
        rw [divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by
    rw [divConcretePostNoX1Frame_unfold]
    dsimp [retFrame] at hp ⊢
    xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

theorem evm_div_callable_v1_spec_from_noNop_preserving_x1_x9
    (sp base x9Val raVal : Word) (a b : EvmWord)
    (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
          (.x9 ↦ᵣ x9Val))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v1 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val)) **
          (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val))
      (by
        rw [divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
          divScratchOwn_unfold]
        pcFree)
      hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

theorem evm_div_callable_bzero_v1_concrete_preserving_x1_spec
    (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  exact
    evm_div_callable_v1_spec_from_noNop_concrete_preserving_x1_x9
      sp base x9Val raVal a b v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0
      (evm_div_bzero_stack_spec_within_dispatch_noNop_concrete_callable_uni
        sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz)

theorem evm_div_callable_bzero_v1_preserving_x1_spec (sp base x9Val raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v1 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) := by
  have hStack :=
    evm_div_bzero_stack_spec_within_dispatch_noNop_callable_uni
      sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := divCode_noNop_sub_div_callable_code_v1) hStack
  have hStackForRet :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (evm_div_callable_code_v1 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        ((divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val)) **
          (.x1 ↦ᵣ raVal)) :=
    cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_div_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (divStackDispatchPostCallable sp a b ** (.x9 ↦ᵣ x9Val))
      (by rw [divStackDispatchPostCallable_unfold, divScratchOwnCallNoX1_unfold,
        divScratchOwn_unfold]; pcFree) hRet
  exact cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_seq_same_cr hStackForRet hRetFramed)

theorem evm_mod_callable_v1_spec_from_noNop_preserving_x1 (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (modStackDispatchPostNoX1 sp a b).pcFree :=
    modStackDispatchPostNoX1_pcFree sp a b
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := modCode_noNop_sub_mod_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostNoX1 sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

theorem evm_mod_callable_v1_spec_from_noNop (sp base raVal : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (branch : ModStackSpecCase base a b)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPre sp a b
          branch.x1 branch.x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPost sp a b)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPre sp a b
        branch.x1 branch.x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 ** (.x1 ↦ᵣ raVal))
      (modStackDispatchPost sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hpcFreePost : (modStackDispatchPost sp a b).pcFree := by
    rw [modStackDispatchPost_unfold]
    rw [divScratchOwnCall_unfold, divScratchOwn_unfold]
    pcFree
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := modCode_noNop_sub_mod_callable_code_v1) hStack
  have hStackFramed :=
    cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree) hStackCall
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPost sp a b) hpcFreePost hRet
  exact cpsTripleWithin_seq_same_cr hStackFramed hRetFramed

/-- Legacy v1 MOD callable wrapper with exact `x1` and no `x9` frame.

This is the return/`cc_ret` adapter only: callers supply a v1 no-NOP stack
proof already shaped for `divModStackDispatchPreCallable`. -/
theorem evm_mod_callable_v1_spec_from_noNop_preserving_x1_noX9
    (sp base raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hStack :
      cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
        (divModStackDispatchPreCallable sp a b
          raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal))) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := modCode_noNop_sub_mod_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostCallable sp a b)
      (modStackDispatchPostCallable_pcFree sp a b) hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

/-- Legacy v1 zero-divisor MOD callable wrapper with exact `x1` and no `x9` frame. -/
theorem evm_mod_callable_bzero_v1_preserving_x1_noX9_spec (sp base raVal : Word)
    (a b : EvmWord) (v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_mod_callable_code_v1 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  have hStack :=
    evm_mod_bzero_stack_spec_within_dispatch_noNop_callable_x1_uni
      sp base a b raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 hbz
  have hStackCall :=
    cpsTripleWithin_extend_code (hmono := modCode_noNop_sub_mod_callable_code_v1) hStack
  have hRet :=
    cpsTripleWithin_extend_code (hmono := evm_mod_callable_code_v1_ret_sub (base := base))
      (ret_spec_within' (base + nopOff) raVal)
  have hRetFramed :=
    cpsTripleWithin_frameL (modStackDispatchPostCallable sp a b)
      (modStackDispatchPostCallable_pcFree sp a b) hRet
  exact cpsTripleWithin_seq_same_cr hStackCall hRetFramed

end EvmAsm.Evm64
