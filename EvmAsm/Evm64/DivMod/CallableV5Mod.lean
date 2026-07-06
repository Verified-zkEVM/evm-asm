/-
  EvmAsm.Evm64.DivMod.CallableV5Mod

  v5 LP64-callable MOD adapter: code-subsumption lemmas from the v5 MOD body
  surface (`modCode_noNop_v5`) into the callable code `evm_mod_callable_code_v5`,
  and the `cc_ret` return-instruction subsumption.

  Mechanical mirror of `EvmAsm.Evm64.DivMod.CallableV5Div`, swapping the div
  epilogue block (`divK_div_epilogue`) for the mod epilogue (`divK_mod_epilogue`);
  all other blocks are byte-identical.  Toward `evm_mod_callable_v5` correctness
  (SMOD `.proven` track).
-/

import EvmAsm.Evm64.DivMod.Callable
import EvmAsm.Evm64.DivMod.Compose.V5NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem callable_b0_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_mod_v5 {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_mod_v5 {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v5) a = some i →
      (evm_mod_callable_code_v5 b) a = some i := by
  unfold evm_mod_callable_code_v5; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [divK_div128_v5_len, cc_ret_len] at hk1 hk2
      bv_omega))
  exact CodeReq.union_mono_left

/-- The callable `cc_ret` return instruction sits at `base + nopOff` inside
    `evm_mod_callable_code_v5`. -/
theorem evm_mod_callable_code_v5_ret_sub {base : Word} :
    ∀ a i, (CodeReq.singleton (base + nopOff) (.JALR .x0 .x1 0)) a = some i →
      (evm_mod_callable_code_v5 base) a = some i := by
  intro a i h
  apply callable_b12_mod_v5
  unfold cc_ret_code cc_ret
  simpa [CodeReq.ofProg] using h

/-- `modCode_noNop_v5 ⊆ evm_mod_callable_code_v5`: the callable v5 MOD code is
    the exact v5 no-NOP MOD body followed by the callable return. -/
theorem modCode_noNop_v5_sub_mod_callable_code_v5 {base : Word} :
    ∀ a i, (modCode_noNop_v5 base) a = some i →
           (evm_mod_callable_code_v5 base) a = some i := by
  unfold modCode_noNop_v5; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_split_mono callable_b0_mod_v5
    (CodeReq.union_split_mono callable_b1_mod_v5
    (CodeReq.union_split_mono callable_b2_mod_v5
    (CodeReq.union_split_mono callable_b3_mod_v5
    (CodeReq.union_split_mono callable_b4_mod_v5
    (CodeReq.union_split_mono callable_b5_mod_v5
    (CodeReq.union_split_mono callable_b6_mod_v5
    (CodeReq.union_split_mono callable_b7_mod_v5
    (CodeReq.union_split_mono callable_b8_mod_v5
    (CodeReq.union_split_mono callable_b9_mod_v5
    (CodeReq.union_split_mono callable_b10_mod_v5
    (CodeReq.union_split_mono callable_b11_mod_v5
    (CodeReq.union_split_mono callable_b13_mod_v5
    (fun _ _ h => by simp [CodeReq.unionAll_nil, CodeReq.empty] at h)))))))))))))

end EvmAsm.Evm64
