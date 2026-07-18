/-
  Shared declaration home for the V5 DIV/MOD stack-surface wrappers.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShift0
import EvmAsm.Evm64.DivMod.DivN2V5ShiftShared
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.DivDispatchShift
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Bzero
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5StackSpecUnconditional
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfShapeNative
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeLimbProjections
import EvmAsm.Evm64.DivMod.Compose.V5Code2
import EvmAsm.Evm64.DivMod.Compose.Base
import EvmAsm.Evm64.DivMod.Compose.OffsetsV6
import EvmAsm.Evm64.DivMod.Compose.FullPathV5ModAssembly
import EvmAsm.Evm64.DivMod.Compose.V6FastArmTripleMod
import EvmAsm.Evm64.DivMod.Compose.DispatchV6Mod
import EvmAsm.Rv64.Tactics.ExtractPure

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

/-- The complete v5 n=1 DIV lane, under the named `N1ShapeIs` predicate. -/
theorem evm_div_n1_stack_spec_unconditional (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hshape : N1ShapeIs b)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro heq
    exact hshape.2.2.2.2
      (BitVec.or_eq_zero_iff.mp
        (BitVec.or_eq_zero_iff.mp
          (BitVec.or_eq_zero_iff.mp heq).1).1).1
  exact evm_div_n1_lane_v5 sp base a b raVal v5 v6 v7 v10 v11Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hshape.2.1 hshape.2.2.1 hshape.2.2.2.1 halign

/-- The complete v5 n=2 DIV lane, under the named `N2ShapeIs` predicate. -/
theorem evm_div_n2_stack_spec_unconditional (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hshape : N2ShapeIs b)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) :=
  evm_div_n2_lane_complete_v5 sp base a b raVal v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem
    hshape.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2 halign

open EvmAsm.Rv64

/-- The v5 DIV unconditional spec, reduced to the n4 lane: with the uniform shift
    `divDispatchShiftX2 b` in `x2`, the full dispatch triple holds for every divisor
    shape, given only the n4 lane. -/
theorem evm_div_stack_spec_unconditional_v5_div_of_n4lane
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  refine evm_div_stack_spec_unconditional_of_lanes_v5_div sp base a b
    (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    exact evm_div_bzero_lane_v5 sp base a b
      (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hbz
  case n1 =>
    intro hshape
    rw [divDispatchShiftX2_n1 hshape]
    exact evm_div_n1_stack_spec_unconditional sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hshape halign
  case n2 =>
    intro hshape
    rw [divDispatchShiftX2_n2 hshape]
    exact evm_div_n2_stack_spec_unconditional sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hshape halign
  case n3 =>
    intro hshape
    rw [divDispatchShiftX2_n3 hshape]
    exact evm_div_n3_stack_spec_unconditional sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hshape halign
  case n4 =>
    intro hshape
    rw [divDispatchShiftX2_n4 hshape]
    exact lane_n4 hshape

open EvmAsm.Rv64

/-- The v5 DIV unconditional spec: with the uniform shift `divDispatchShiftX2 b`
    in `x2`, the full dispatch triple holds for every divisor shape, with no
    remaining lane hypothesis (the n=4 lane is discharged from shape via
    `evm_div_n4_lane_of_shape_native`). -/
theorem evm_div_stack_spec_unconditional_v5_div
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  refine evm_div_stack_spec_unconditional_v5_div_of_n4lane sp base a b
    raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign ?lane_n4
  intro hshape
  exact evm_div_n4_lane_of_shape_native sp base a b
    raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    (N4ShapeIs.b3_ne_zero hshape) halign

open EvmAsm.Rv64

/-- **The unconditional EVM-stack-level DIV spec.**  Over the production v5 code
    surface `divCode_v5`, with the uniform dispatch shift `divDispatchShiftX2 b`
    in `x2`, the full DIV dispatch triple holds for every 256-bit divisor `b` —
    with no premise about `b` whatsoever (the `b = 0`, n=1, n=2, n=3 and n=4
    divisor shapes are all discharged internally). -/
theorem evm_div_stack_spec_unconditional
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) :=
  cpsTripleWithin_divCode_noNop_v5_to_divCode_v5
    (evm_div_stack_spec_unconditional_v5_div sp base a b
      raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign)

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

open EvmAsm.Rv64

/-- **The unconditional EVM-stack-level MOD spec** over the production v5 code
    surface `modCode_v5`, with the uniform dispatch shift `divDispatchShiftX2 b`
    in `x2` — the full MOD dispatch triple holds for every 256-bit divisor `b`
    (the `b = 0`, n=1, n=2, n=3 and n=4 divisor shapes are all discharged
    internally). -/
theorem evm_mod_stack_spec_unconditional
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) :=
  cpsTripleWithin_modCode_noNop_v5_to_modCode_v5
    (evm_mod_stack_spec_unconditional_v5_mod sp base a b
      raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign)

/-- The unconditional MOD dispatch triple over the canonical v6 code surface
    `modCodeV6`, entered at the embedded-v5 offset `modV6V5Off` and exiting at
    `modV6ExitOff`.  MOD mirror of `evm_div_v5_unconditional_over_divCodeV6`. -/
theorem evm_mod_v5_unconditional_over_modCodeV6
    (sp base : Word) (a b : EvmWord) (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : (((base + modV6V5Off) + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + modV6V5Off) + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound (base + modV6V5Off) (base + modV6ExitOff) (modCodeV6 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  have h := evm_mod_stack_spec_unconditional sp (base + modV6V5Off) a b raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign
  rw [show ((base + modV6V5Off) + nopOff : Word) = base + modV6ExitOff from by
    simp only [modV6V5Off, nopOff, modV6ExitOff]; bv_omega] at h
  exact cpsTripleWithin_extend_code (hmono := fun a i hh => modCode_v5_sub_modCodeV6 a i hh) h

open EvmAsm.Rv64

/-- `fromLimbs` of the per-limb `getLimbN` match recovers the word. -/
private theorem fromLimbs_match_getLimbN_mod (v : EvmWord) :
    (EvmWord.fromLimbs fun i : Fin 4 => match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3) = v := by
  rw [show (fun i : Fin 4 => match i with
      | 0 => v.getLimbN 0 | 1 => v.getLimbN 1 | 2 => v.getLimbN 2 | 3 => v.getLimbN 3)
      = v.getLimb from by
    funext i; fin_cases i <;> rfl]
  exact EvmWord.fromLimbs_getLimb v

/-- Peel a pure `⌜fact⌝` from the right of the precondition into an ambient
    hypothesis. -/
private theorem cpsTripleWithin_of_pure_imp_mod
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {fact : Prop}
    (h : fact → cpsTripleWithin nSteps entry exit_ cr P Q) :
    cpsTripleWithin nSteps entry exit_ cr (P ** ⌜fact⌝) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, hpq⟩ := hPR
  obtain ⟨h1, h2, hd, hunion, hPF, hR_⟩ := hpq
  have hpf := (sepConj_pure_right h1).1 hPF
  exact h hpf.2 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hunion, hpf.1, hR_⟩ hpc

/-- **The v6 MOD stack spec.** Over `modCodeV6`, entry `base`, exit
    `base + modV6ExitOff`: the full n=1 fast-path dispatch computes `a mod b`
    for every 256-bit divisor, landing `modStackDispatchPostV5 sp a b`. -/
theorem evm_mod_v6_stack_spec
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halignV5 : (((base + modV6V5Off) + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      (base + modV6V5Off) + div128CallRetOff)
    (halign3 : ((base + v6Digit3Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit3Off + 16)
    (halign2 : ((base + v6Digit2Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit2Off + 16)
    (halign1 : ((base + v6Digit1Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit1Off + 16)
    (halign0 : ((base + v6Digit0Off + 16) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word)
      = base + v6Digit0Off + 16) :
    cpsTripleWithin 954 base (base + modV6ExitOff) (modCodeV6 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (modStackDispatchPostV5 sp a b) := by
  -- v5 arm, parametric in the (post-dispatch) values of x5 / x10.
  have hv5app : ∀ (x5v x10v : Word),
      cpsTripleWithin unifiedDivBound (base + modV6V5Off) (base + modV6ExitOff) (modCodeV6 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          (divDispatchShiftX2 b) x5v v6 v7 x10v v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (modStackDispatchPostV5 sp a b) := fun x5v x10v =>
    evm_mod_v5_unconditional_over_modCodeV6 sp base a b raVal x5v v6 v7 x10v v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halignV5
  -- Fast arm, given the n=1 divisor facts (b0 ≠ 0, b1|b2|b3 = 0); its post is
  -- already `modStackDispatchPostV5 sp a b` after the `fromLimbs∘getLimbN` fold.
  have hfastapp :
      (b.getLimbN 0 ≠ (0 : Word)) →
      ((b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)) →
      cpsTripleWithin 441 (base + v6ClzOff) (base + modV6ExitOff) (modCodeV6 base)
        ((((((.x5 ↦ᵣ b.getLimbN 0) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x0 ↦ᵣ (0 : Word))) **
            ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ divDispatchShiftX2 b) ** ((sp + signExtend12 32) ↦ₘ b.getLimbN 0) **
             ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3984) ↦ₘ nMem))) **
           ((.x10 ↦ᵣ b.getLimbN 3) ** ((sp + 0) ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
            ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3) **
            ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4032) ↦ₘ u3) **
            ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4048) ↦ₘ u1) **
            ((sp + signExtend12 4056) ↦ₘ u0))) **
          ((.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x11 ↦ᵣ v11) **
           (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
           (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0) **
           (sp + signExtend12 3936 ↦ₘ scratchMem) **
           ((sp + signExtend12 4064) ↦ₘ q3) ** ((sp + signExtend12 4072) ↦ₘ q2) **
           ((sp + signExtend12 4080) ↦ₘ q1) ** ((sp + signExtend12 4088) ↦ₘ q0) **
           ((sp + 40) ↦ₘ b.getLimbN 1) ** ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3))) **
         (((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
          ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
          ((.x1 : Reg) ↦ᵣ raVal)))
        (modStackDispatchPostV5 sp a b) := by
    intro hb0 hor
    have hb3z : b.getLimbN 3 = 0 := (BitVec.or_eq_zero_iff.mp hor).2
    have hb1z : b.getLimbN 1 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp hor).1).1
    have hb2z : b.getLimbN 2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp hor).1).2
    have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
      rw [hb1z, hb2z, hb3z]; simpa using hb0
    refine cpsTripleWithin_weaken (fun h hp => hp) (fun h hq => ?_)
      (modK_fastBody_dispatchPostV5_within_v6 sp (b.getLimbN 0)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        v6 v7 (divDispatchShiftX2 b) (b.getLimbN 3) (signExtend12 (4 : BitVec 12) - (4 : Word)) v11
        q3 q2 q1 q0 shiftMem nMem retMem dMem dloMem scratch_un0 scratchMem
        (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) u0 u1 u2 u3 u4
        u5 u6 u7 jMem raVal (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) base
        hbnz hb1z hb2z hb3z halign3 halign2 halign1 halign0)
    convert hq using 3 <;> exact (fromLimbs_match_getLimbN_mod _).symm
  -- Fast arm with the two divisor facts bundled into the precondition.
  have hfast_full := cpsTripleWithin_of_pure_imp_mod (fun
      (hor : (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)) =>
    cpsTripleWithin_of_pure_imp_mod (fun (hb0 : b.getLimbN 0 ≠ (0 : Word)) =>
      hfastapp hb0 hor))
  -- v5 arms with the dispatch pure facts bundled (so xperm matches them as atoms).
  have hv5_beqT := cpsTripleWithin_of_pure_imp_mod (fun
      (_ : (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)) =>
    cpsTripleWithin_of_pure_imp_mod (fun (_ : b.getLimbN 0 = (0 : Word)) =>
      hv5app (b.getLimbN 0) (b.getLimbN 3)))
  have hv5_bneT := cpsTripleWithin_of_pure_imp_mod (fun
      (_ : (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) ≠ (0 : Word)) =>
    hv5app (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) (b.getLimbN 3))
  -- INNER merge: BEQ {v5 (b0=0) | fast (b0≠0)} at base+24.
  have hbeq := modK_dispatchN1_beq_spec_within_v6 sp
    (b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) (b.getLimbN 0) base
  have hbeqf := cpsBranchWithin_frameR
    ((.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x1 ↦ᵣ raVal) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ b.getLimbN 3) ** (.x11 ↦ᵣ v11) **
     (.x2 ↦ᵣ divDispatchShiftX2 b) ** evmWordIs sp a **
     ((sp + 40) ↦ₘ b.getLimbN 1) ** ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3) **
     divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
     ((sp + signExtend12 3936) ↦ₘ scratchMem) **
     ⌜(b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3) = (0 : Word)⌝)
    (by pcFree) hbeq
  have hinner := cpsBranchWithin_merge_same_cr hbeqf
    (cpsTripleWithin_weaken (fun h hp => by
        rw [divModStackDispatchPreNoX1_unfold, evmWordIs_sp32_unfold]
        simp only [AddrNorm.se12_32] at hp
        xperm_hyp hp)
      (fun h hq => hq)
      hv5_beqT)
    (cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken (fun h hp => by
          rw [show (sp + 0 : Word) = sp from by bv_omega]
          rw [evmWordIs_sp_unfold, divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
          xperm_hyp hp)
        (fun h hq => hq)
        hfast_full))
  -- OUTER merge: BNE {v5 (n≥2) | inner (base+24)} at base.
  have hbne := modK_dispatchN1_bne_spec_within_v6 sp v5 v10
    (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) base
  have hbnef := cpsBranchWithin_frameR
    ((.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (4 : Word))) ** (.x1 ↦ᵣ raVal) ** (.x6 ↦ᵣ v6) **
     (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x2 ↦ᵣ divDispatchShiftX2 b) ** evmWordIs sp a **
     ((sp + 32) ↦ₘ b.getLimbN 0) **
     divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
     ((sp + signExtend12 3936) ↦ₘ scratchMem))
    (by pcFree) hbne
  have houter := cpsBranchWithin_merge_same_cr hbnef
    (cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_weaken (fun h hp => by
          rw [divModStackDispatchPreNoX1_unfold, evmWordIs_sp32_unfold]
          simp only [AddrNorm.se12_40, AddrNorm.se12_48, AddrNorm.se12_56] at hp
          xperm_hyp hp)
        (fun h hq => hq)
        hv5_bneT))
    (cpsTripleWithin_weaken (fun h hp => by
        simp only [AddrNorm.se12_32, AddrNorm.se12_40, AddrNorm.se12_48, AddrNorm.se12_56] at hp ⊢
        xperm_hyp hp)
      (fun h hq => hq)
      hinner)
  -- Fold the entry precondition back to `divModStackDispatchPreNoX1 … ** sp+3936`.
  refine cpsTripleWithin_weaken (fun h hp => by
      rw [divModStackDispatchPreNoX1_unfold, evmWordIs_sp32_unfold] at hp
      simp only [AddrNorm.se12_40, AddrNorm.se12_48, AddrNorm.se12_56] at ⊢
      xperm_hyp hp)
    (fun h hq => hq) houter

end EvmAsm.Evm64
