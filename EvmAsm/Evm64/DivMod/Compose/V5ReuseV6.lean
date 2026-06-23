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
import EvmAsm.Evm64.DivMod.Compose.OffsetsV6
import EvmAsm.Evm64.DivMod.Compose.FullPathV5DivUnconditionalFull

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

/-- A fast-path block at base address `c = base + d` (`d` an instruction-byte
    offset) that fits entirely below `v6V5Off` (= 816) is disjoint from the
    embedded `divCode_v5` at `base + v6V5Off`: any shared address would be both
    `base + (d + 4·k₁)` with `d + 4·k₁ < 816` and `base + 816 + 4·K` (v5
    support), impossible. -/
theorem fast_disjoint_divCode_v5 {base : Word} (c : Word) (pFast : Program) (d : Nat)
    (hc : c = base + BitVec.ofNat 64 d) (hfit : d + 4 * pFast.length ≤ 816) :
    (CodeReq.ofProg c pFast).Disjoint (divCode_v5 (base + v6V5Off)) := by
  intro a
  rcases Option.eq_none_or_eq_some (CodeReq.ofProg c pFast a) with hA | ⟨i, hA⟩
  · left; exact hA
  · right
    by_contra hB
    obtain ⟨i', hv5⟩ := Option.ne_none_iff_exists'.mp hB
    obtain ⟨K, hK, haddrV5⟩ := divCode_v5_addr_mul4 _ a i' hv5
    obtain ⟨k1, hk1, haddrF⟩ := CodeReq.ofProg_some_range _ _ a i hA
    rw [haddrF, hc] at haddrV5
    simp only [v6V5Off] at haddrV5
    bv_omega

/-- The embedded `evm_div_v5` (block 11 of `divCodeV6`) is subsumed by
    `divCodeV6`: every address `divCode_v5 (base + v6V5Off)` maps is mapped the
    same by `divCodeV6 base`. The 11 preceding fast-path blocks each fit below
    `v6V5Off`, so they are disjoint from the v5 block. -/
theorem divCode_v5_sub_divCodeV6 {base : Word} :
    ∀ a i, (divCode_v5 (base + v6V5Off)) a = some i → (divCodeV6 base) a = some i := by
  unfold divCodeV6
  refine CodeReq.mono_sub_unionAll (divCode_v5 (base + v6V5Off)) _ 11 ?_ ?_ ?_
  · simp only [List.length_cons, List.length_nil]; omega
  · intro a i h; simpa only [List.get] using h
  · intro j hj
    interval_cases j <;> simp only [List.get]
    · exact fast_disjoint_divCode_v5 _ _ 0 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 32 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 128 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 156 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 240 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 276 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 316 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 356 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 396 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 436 (by bv_omega) (by decide)
    · exact fast_disjoint_divCode_v5 _ _ 476 (by bv_omega) (by decide)

/-- The reused, unconditional v5 DIV stack spec, lifted from `divCode_v5
    (base+v6V5Off)` onto `divCodeV6 base` (the n≥2 / b=0 arm of `evm_div_v6`).
    Entry `base+v6V5Off`, exit `base+v6ExitOff`. -/
theorem evm_div_v5_unconditional_over_divCodeV6
    (sp base : Word) (a b : EvmWord) (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + v6V5Off) + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + v6V5Off) + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound (base + v6V5Off) (base + v6ExitOff) (divCodeV6 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have h := evm_div_stack_spec_unconditional sp (base + v6V5Off) a b raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign
  rw [show ((base + v6V5Off) + nopOff : Word) = base + v6ExitOff from by
    simp only [v6V5Off, nopOff, v6ExitOff]; bv_omega] at h
  exact cpsTripleWithin_extend_code (hmono := fun a i hh => divCode_v5_sub_divCodeV6 a i hh) h

end EvmAsm.Evm64
