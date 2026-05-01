/-
  EvmAsm.Evm64.DivMod.Spec.N3ModBridge

  Stack-level bridge for the n=3 MOD path: lifts the unified post
  `fullModN3UnifiedPost` (= `fullModN3DenormPost ** fullDivN3Frame`)
  produced by `evm_mod_n3_full_unified_spec` to the stack-dispatch
  postcondition `modStackDispatchPost`.

  Mirror of `fullModN2UnifiedPost_to_modStackDispatchPost` in
  `Spec.N2ModBridge`, downshifted to n=3 (two trial iterations: bltu_1,
  bltu_0). At n=3 there is no separate `n3ScratchFinal` struct — the
  scratch cells live inline in `fullDivN3Scratch`, so the bridge unfolds
  `fullDivN3Frame` and `fullDivN3Scratch` directly (mirroring the n=3
  DIV bridge `fullDivN3UnifiedPost_to_divStackDispatchPost`).

  Will be consumed by the follow-up slice that introduces
  `evm_mod_n3_stack_spec_within{,_word}`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-bxbs`, parent `evm-asm-pb2h` (#61 slice 2d).
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Lift `fullModN3UnifiedPost` to `modStackDispatchPost`.

The unified post is unfolded to its `denormModPost` skeleton plus the
`fullDivN3Frame` cells (whose 4 scratch slots come from
`fullDivN3Scratch`). After exposing the limb-shaped `evmWordIs` on `sp`
and `sp + 32` and the `divScratchValuesCall`/`divScratchValues` shape,
a single `xperm_hyp` closes the goal. Mirror of
`fullModN2UnifiedPost_to_modStackDispatchPost` (Spec/N2ModBridge.lean)
and `fullDivN3UnifiedPost_to_divStackDispatchPost`
(Spec/Dispatcher.lean line 1097). -/
theorem fullModN3UnifiedPost_to_modStackDispatchPost
    (bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64))) :
    ∀ h,
      fullModN3UnifiedPost bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0 h →
      modStackDispatchPost sp a b h := by
  intro h hq
  let shift := fullDivN3Shift b2
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let r1 := fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  let u0' := (r0.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.1 <<< (antiShift.toNat % 64))
  let u1' := (r0.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.1 <<< (antiShift.toNat % 64))
  let u2' := (r0.2.2.2.1 >>> (shift.toNat % 64)) ||| (r0.2.2.2.2.1 <<< (antiShift.toNat % 64))
  let u3' := r0.2.2.2.2.1 >>> (shift.toNat % 64)
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let scratch_ret1 := if bltu_1 then (base + div128CallRetOff) else retMem
  let scratch_d1 := if bltu_1 then v.2.2.1 else dMem
  let scratch_dlo1 := if bltu_1 then div128DLo v.2.2.1 else dloMem
  let scratch_un01 := if bltu_1 then div128Un0 u.2.2.2.1 else scratch_un0
  refine modStackDispatchPost_weaken (sp := sp) (a := a) (b := b)
    (v1 := signExtend12 4095) (v2 := antiShift)
    (v5 := u0') (v6 := u1') (v7 := u2')
    (v10 := u3') (v11 := r0.1)
    (q0 := r0.1) (q1 := r1.1) (q2 := (0 : Word)) (q3 := (0 : Word))
    (u0 := u0') (u1 := u1') (u2 := u2') (u3 := u3')
    (u4 := r0.2.2.2.2.2) (u5 := r1.2.2.2.2.2)
    (u6 := (0 : Word)) (u7 := (0 : Word))
    (shiftMem := shift) (nMem := 3) (jMem := 0)
    (retMem := if bltu_0 then (base + div128CallRetOff) else scratch_ret1)
    (dMem := if bltu_0 then v.2.2.1 else scratch_d1)
    (dloMem := if bltu_0 then div128DLo v.2.2.1 else scratch_dlo1)
    (scratch_un0 := if bltu_0 then div128Un0 r1.2.2.1 else scratch_un01) h ?_
  delta fullModN3UnifiedPost fullModN3DenormPost fullDivN3Frame fullDivN3Scratch at hq
  simp only [denormModPost_unfold] at hq
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      from by rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3]]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) =
      (((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
       ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3'))
      from by
        rw [evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
          hmod0 hmod1 hmod2 hmod3]]
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

end EvmAsm.Evm64
