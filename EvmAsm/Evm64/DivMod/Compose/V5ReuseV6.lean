/-
  EvmAsm.Evm64.DivMod.Compose.V5ReuseV6

  Infrastructure for reusing the v5 unconditional stack spec inside `divCodeV6`.
  The embedded `evm_div_v5` sits at `base + v6V5Off` and is the last (index 11)
  element of `divCodeV6`'s `unionAll`. To frame the v5 spec into `divCodeV6` we
  need each preceding fast-path block disjoint from `divCode_v5 (base+v6V5Off)`,
  which follows from a support lemma: every address `divCode_v5 b` maps lies at
  `b + 4·K` for some `K < 353` (the v5 program is 353 instrs, laid out
  contiguously by the block offsets).

  Bead `evm-asm-dr466`.
-/

import EvmAsm.Evm64.DivMod.Compose.V5Code2
import EvmAsm.Evm64.DivMod.Compose.Base

namespace EvmAsm.Rv64

/-- A hit in a `unionAll` comes from some component block. -/
theorem CodeReq.unionAll_some_mem (crs : List CodeReq) (a : Word) (i : Instr)
    (h : (CodeReq.unionAll crs) a = some i) :
    ∃ j, ∃ (hj : j < crs.length), (crs.get ⟨j, hj⟩) a = some i := by
  induction crs with
  | nil => simp [CodeReq.unionAll, CodeReq.empty] at h
  | cons cr rest ih =>
    rw [CodeReq.unionAll_cons] at h
    simp only [CodeReq.union] at h
    cases hc : cr a with
    | some i' => exact ⟨0, by simp, by simp [hc]; rw [hc] at h; simpa using h⟩
    | none =>
      rw [hc] at h
      obtain ⟨j, hj, hjj⟩ := ih h
      exact ⟨j + 1, by simp; omega, by simpa using hjj⟩

end EvmAsm.Rv64

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Support lemma: every address `divCode_v5 b` maps lies at `b + 4·K` for some
    `K < 353`. The 14 blocks are laid out contiguously (offsets
    `0/32/116/212/228/312/396/432/448/908/1008/1048/1068/1072`, lengths summing
    to 353), so block `j` starting at instruction `Kⱼ` contributes `Kⱼ + k`. -/
theorem divCode_v5_addr_mul4 (b a : Word) (i : Instr)
    (h : divCode_v5 b a = some i) :
    ∃ K, K < 353 ∧ a = b + BitVec.ofNat 64 (4 * K) := by
  unfold divCode_v5 at h
  obtain ⟨j, hj, hblk⟩ := CodeReq.unionAll_some_mem _ a i h
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j <;> simp only [List.get] at hblk
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨0 + k, by simp only [divK_phaseA_len] at hk; omega, by rw [haddr]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨8 + k, by simp only [divK_phaseB_len] at hk; omega,
      by rw [haddr]; simp only [phaseBOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨29 + k, by simp only [divK_clz_len] at hk; omega,
      by rw [haddr]; simp only [clzOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨53 + k, by simp only [divK_phaseC2_len] at hk; omega,
      by rw [haddr]; simp only [phaseC2Off]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨57 + k, by simp only [divK_normB_len] at hk; omega,
      by rw [haddr]; simp only [normBOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨78 + k, by simp only [divK_normA_len] at hk; omega,
      by rw [haddr]; simp only [normAOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨99 + k, by simp only [divK_copyAU_len] at hk; omega,
      by rw [haddr]; simp only [copyAUOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨108 + k, by simp only [divK_loopSetup_len] at hk; omega,
      by rw [haddr]; simp only [loopSetupOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨112 + k, by simp only [divK_loopBody_len] at hk; omega,
      by rw [haddr]; simp only [loopBodyOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨227 + k, by simp only [divK_denorm_len] at hk; omega,
      by rw [haddr]; simp only [denormOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨252 + k, by simp only [divK_divEpilogue_len] at hk; omega,
      by rw [haddr]; simp only [epilogueOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨262 + k, by simp only [divK_zeroPath_len] at hk; omega,
      by rw [haddr]; simp only [zeroPathOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨267 + k, by simp only [divK_nop_len] at hk; omega,
      by rw [haddr]; simp only [nopOff]; bv_omega⟩
  · obtain ⟨k, hk, haddr⟩ := CodeReq.ofProg_some_range _ _ a i hblk
    exact ⟨268 + k, by simp only [divK_div128_v5_len] at hk; omega,
      by rw [haddr]; simp only [div128Off]; bv_omega⟩

end EvmAsm.Evm64
