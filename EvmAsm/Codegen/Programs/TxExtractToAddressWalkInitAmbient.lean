/-
  Ambient dual of extract walk_init short call.

  Leaf already ambient-capable: pass `listBase := regionBase`,
  `listOff := ambientAbsOff off rel`, `listBytes := bs`. Pure guards on
  `bs[absOff]` (same as slice guards via `txSlice_getElem`).
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressWalkInit
import EvmAsm.Codegen.Programs.TxTypeDispatchAmbient

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Codegen
open EvmAsm.Codegen.TxTypeDispatchSpec

/-- Ambient short walk_init call: regionBase + abs listOff into full blob. -/
theorem extractWalkInitCall_short_ambient
    (regionBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (bs : List (BitVec 8)) (absOff : Nat) (old1 : Word)
    (hsalign : regionBase.toNat % 8 = 0)
    (hoff : absOff < bs.length)
    (hover : regionBase.toNat + absOff < 2 ^ 64)
    (hvalid : isValidByteAccess (regionBase + BitVec.ofNat 64 absOff) = true)
    (hlen : listLen ≠ (0 : Word))
    (h_ge : ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true)
    (h_exact : (regionBase + BitVec.ofNat 64 absOff) +
        (((bs[absOff]'hoff).zeroExtend 64 - (0xc0 : Word)) +
          signExtend12 (1 : BitVec 12)) =
      (regionBase + BitVec.ofNat 64 absOff) + listLen) :
    cpsTripleWithin (1 + 15) WalkInitJalPc LinkWalkInit extractLinkedCode
      ((.x1 ↦ᵣ old1) **
        extractWalkInitPrest regionBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
          t5Old t6Old bs absOff)
      (extractWalkInitShortPost regionBase listLen bs absOff t5Old t6Old) :=
  extractWalkInitCall_short regionBase listLen a2Old t0Old t1Old t2Old t3Old t4Old
    t5Old t6Old bs absOff old1 hsalign hoff hover hvalid hlen h_ge h_hi h_exact

/-- Bridge slice-relative short guards to ambient absOff via `txSlice_getElem`. -/
theorem short_walkInit_guards_ambient
    (bs : List (BitVec 8)) (off len rel : Nat)
    (hrel : rel < len) (hbound : off + len ≤ bs.length)
    (h_ge : ¬ BitVec.ult
      (((txSlice bs off len)[rel]'(by rw [txSlice_length bs off len hbound]; exact hrel)
        ).zeroExtend 64) (0xc0 : Word) = true)
    (h_hi : BitVec.ult
      (((txSlice bs off len)[rel]'(by rw [txSlice_length bs off len hbound]; exact hrel)
        ).zeroExtend 64) (0xf8 : Word) = true) :
    let absOff := ambientAbsOff off rel
    have hoff : absOff < bs.length := ambientAbsOff_lt bs off rel len hrel hbound
    ¬ BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xc0 : Word) = true ∧
      BitVec.ult ((bs[absOff]'hoff).zeroExtend 64) (0xf8 : Word) = true := by
  intro absOff hoff
  have hbyte := txSlice_getElem bs off len rel hrel hbound
  constructor
  · intro h; apply h_ge; simpa [hbyte] using h
  · simpa [hbyte] using h_hi

#print axioms extractWalkInitCall_short_ambient
#print axioms short_walkInit_guards_ambient

end EvmAsm.Codegen.TxExtractToAddressSpec
