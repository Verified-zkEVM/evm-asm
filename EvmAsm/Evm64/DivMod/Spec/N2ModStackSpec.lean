/-
  EvmAsm.Evm64.DivMod.Spec.N2ModStackSpec

  Stack-level entry point for the n=2 MOD path: composes
  `evm_mod_n2_full_unified_spec` with the limb-shaped `evmWordIs` bridge
  `fullModN2UnifiedPost_to_modStackDispatchPost`. Mirrors
  `evm_mod_n1_stack_spec_within{,_word}` from `Spec.Dispatcher`.

  The `_word` variant takes a single packed `EvmWord` equality hypothesis
  `fullModN2RemainderWord ... = EvmWord.mod a b` and projects it into the
  four per-limb hypotheses required by `evm_mod_n2_stack_spec_within`,
  using `fullModN2_hmods_of_word_eq`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-e7pq`, parent `evm-asm-kxrl` (#61 slice 2c).
-/

import EvmAsm.Evm64.DivMod.Spec.N2ModBridge
import EvmAsm.Evm64.DivMod.Spec.N2RemainderWord

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- N=2 MOD stack-level entry point: mirrors `evm_mod_n1_stack_spec_within`.

Composes `evm_mod_n2_full_unified_spec` with the limb-shaped pre and post
bridges (`divModStackDispatchPre` ↔ raw cells, and
`fullModN2UnifiedPost_to_modStackDispatchPost`). -/
theorem evm_mod_n2_stack_spec_within
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hmod0 : (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hmod1 : (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hmod2 : (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64)) |||
        ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))))
    (hmod3 : (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN2Shift b1).toNat % 64))) :
    cpsTripleWithin 744 base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  have hFull := evm_mod_n2_full_unified_spec
    bltu_2 bltu_1 bltu_0 sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3z hb2z hb1nz hshift_nz halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta divModStackDispatchPre at hp
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun h hq =>
      fullModN2UnifiedPost_to_modStackDispatchPost
        bltu_2 bltu_1 bltu_0 sp base a b
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratch_un0
        ha0 ha1 ha2 ha3 hmod0 hmod1 hmod2 hmod3 h hq)
    hFull

/-- `_word` form: mirror of `evm_mod_n1_stack_spec_within_word`. Takes a
single `EvmWord`-valued equality `fullModN2RemainderWord ... = EvmWord.mod a b`
and projects it into the four per-limb hypotheses via
`fullModN2_hmods_of_word_eq`. -/
theorem evm_mod_n2_stack_spec_within_word
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0)
    (hshift_nz : (clzResult b1).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : isTrialN2_j2 bltu_2 a3 b0 b1)
    (hbltu_1 : isTrialN2_j1 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3)
    (hbltu_0 : isTrialN2_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b1).1).toNat % 64))
      ((b1 <<< (((clzResult b1).1).toNat % 64)) ||| (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b2 <<< (((clzResult b1).1).toNat % 64)) ||| (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64)))
      ((b3 <<< (((clzResult b1).1).toNat % 64)) ||| (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b1).1).toNat % 64))))
    (hmodWord : fullModN2RemainderWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    cpsTripleWithin 744 base (base + nopOff) (modCode base)
      (divModStackDispatchPre sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word))
        ((clzResult b1).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPost sp a b) := by
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ :=
    fullModN2_hmods_of_word_eq bltu_2 bltu_1 bltu_0
      a b a0 a1 a2 a3 b0 b1 b2 b3 hmodWord
  exact evm_mod_n2_stack_spec_within bltu_2 bltu_1 bltu_0
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1nz
    hshift_nz halign hbltu_2 hbltu_1 hbltu_0 hcarry2
    hmod0 hmod1 hmod2 hmod3

end EvmAsm.Evm64
