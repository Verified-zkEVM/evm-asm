/-
  EvmAsm.Evm64.DivMod.Compose.V5ReuseModV6

  MOD analog of `V5ReuseV6`: infrastructure for reusing the unconditional MOD v5
  stack spec inside `modCodeV6`. The embedded `evm_mod_v5` sits at
  `base + modV6V5Off` (index 12, the last element of `modCodeV6`'s `unionAll`).
  To frame the v5 MOD spec into `modCodeV6` we need each preceding fast-path
  block disjoint from `modCode_v5 (base + modV6V5Off)`.

  `modCode_v5` shares `divCode_v5`'s 14-block layout exactly except block 10
  (`divK_mod_epilogue` instead of `divK_div_epilogue`, same length 10), so the
  address-support lemma below mirrors `divCode_v5_addr_mul4` line-for-line.

  Bead `evm-asm-9iqmw` (MOD v6 unconditional closure; cf. #9538).
-/

import EvmAsm.Evm64.DivMod.Compose.V5ReuseV6

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Support lemma: every address `modCode_v5 b` maps lies at `b + 4·K` for some
    `K < 353`. Same 14-block contiguous layout as `divCode_v5_addr_mul4`; only
    block 10 differs (`divK_mod_epilogue`, also length 10, `K = 252`). -/
theorem modCode_v5_addr_mul4 (b a : Word) (i : Instr)
    (h : modCode_v5 b a = some i) :
    ∃ K, K < 353 ∧ a = b + BitVec.ofNat 64 (4 * K) := by
  unfold modCode_v5 at h
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
    exact ⟨252 + k, by simp only [divK_modEpilogue_len] at hk; omega,
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

/-- A fast-path block at base address `c = base + d` that fits entirely below
    `modV6V5Off` (= 844) is disjoint from the embedded `modCode_v5` at
    `base + modV6V5Off`. Mirror of `fast_disjoint_divCode_v5`. -/
theorem fast_disjoint_modCode_v5 {base : Word} (c : Word) (pFast : Program) (d : Nat)
    (hc : c = base + BitVec.ofNat 64 d) (hfit : d + 4 * pFast.length ≤ 844) :
    (CodeReq.ofProg c pFast).Disjoint (modCode_v5 (base + modV6V5Off)) := by
  intro a
  rcases Option.eq_none_or_eq_some (CodeReq.ofProg c pFast a) with hA | ⟨i, hA⟩
  · left; exact hA
  · right
    by_contra hB
    obtain ⟨i', hv5⟩ := Option.ne_none_iff_exists'.mp hB
    obtain ⟨K, hK, haddrV5⟩ := modCode_v5_addr_mul4 _ a i' hv5
    obtain ⟨k1, hk1, haddrF⟩ := CodeReq.ofProg_some_range _ _ a i hA
    rw [haddrF, hc] at haddrV5
    simp only [modV6V5Off] at haddrV5
    bv_omega

/-- The embedded `evm_mod_v5` (block 12 of `modCodeV6`) is subsumed by
    `modCodeV6`: every address `modCode_v5 (base + modV6V5Off)` maps is mapped
    the same by `modCodeV6 base`. The 12 preceding fast-path blocks each fit
    below `modV6V5Off`, so they are disjoint from the v5 block. -/
theorem modCode_v5_sub_modCodeV6 {base : Word} :
    ∀ a i, (modCode_v5 (base + modV6V5Off)) a = some i → (modCodeV6 base) a = some i := by
  unfold modCodeV6
  refine CodeReq.mono_sub_unionAll (modCode_v5 (base + modV6V5Off)) _ 12 ?_ ?_ ?_
  · simp only [List.length_cons, List.length_nil]; omega
  · intro a i h; simpa only [List.get] using h
  · intro j hj
    interval_cases j <;> simp only [List.get]
    · exact fast_disjoint_modCode_v5 _ _ 0 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 32 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 128 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 156 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 240 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 276 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 316 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 356 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 396 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 436 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 464 (by bv_omega) (by decide)
    · exact fast_disjoint_modCode_v5 _ _ 504 (by bv_omega) (by decide)

end EvmAsm.Evm64
