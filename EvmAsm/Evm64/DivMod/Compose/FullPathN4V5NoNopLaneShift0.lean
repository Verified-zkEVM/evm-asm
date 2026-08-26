/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0

  The n=4 v5 DIV lane, shift=0 case, with the runtime borrow case-split: from the
  stack-dispatch precondition `divModStackDispatchPreNoX1` to `divStackDispatchPostV5`
  over `divCode_noNop_v5`.  Dispatches on a bundled runtime+quotient certificate
  `n4Shift0LaneRuntimeCertV5` (the shift=0 analog of `n4ShiftNzLaneRuntimeCertV5`):
  the skip branch applies the shift=0 call-skip lane skeleton (#7624), the addback
  branch applies the shift=0 call-addback lane skeleton (#7625).  Both branches use
  the RAW shift=0 window (`v = b`, `u = a`, `uTop = 0`).  The lane has the same
  pre/post as `evm_div_n4_lane_shiftNz_v5_of_cert` (#7614), so the two combine into
  `lane_n4` by `by_cases (clzResult b3).1 = 0`.  The certificate still carries the
  per-branch quotient-correctness (`hdiv`) facts; a later step discharges them from
  shape via the shift=0 word equalities.  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallSkip
public import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0CallAddback

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled runtime + quotient certificate for the n=4 v5 shift=0 lane: either the
    runtime took the call+skip branch (raw-window no-borrow + the single-limb
    quotient correctness with `qHat = divKTrialCallV5QHat 0 a3 b3`), or it took the
    call+addback branch (raw-window addback borrow + carry2 + the single-limb
    quotient correctness with the corrected `fullDivN4CallAddbackShift0QuotientV5`).
    Shift=0 analog of `n4ShiftNzLaneRuntimeCertV5`. -/
def n4Shift0LaneRuntimeCertV5 (a b : EvmWord) : Prop :=
  (mulsubN4NoBorrow (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) (0 : Word) ∧
   (EvmWord.div a b).getLimbN 0 = divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3) ∧
   (EvmWord.div a b).getLimbN 1 = 0 ∧
   (EvmWord.div a b).getLimbN 2 = 0 ∧
   (EvmWord.div a b).getLimbN 3 = 0) ∨
  ((if BitVec.ult (0 : Word)
      (mulsubN4 (divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3))
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)).2.2.2.2
    then (1 : Word) else 0) ≠ (0 : Word) ∧
   (let qHat := divKTrialCallV5QHat (0 : Word) (a.getLimbN 3) (b.getLimbN 3)
    let ms := mulsubN4 qHat (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 ((0 : Word) - c3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≠ 0) ∧
   (EvmWord.div a b).getLimbN 0 = fullDivN4CallAddbackShift0QuotientV5
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   (EvmWord.div a b).getLimbN 1 = 0 ∧
   (EvmWord.div a b).getLimbN 2 = 0 ∧
   (EvmWord.div a b).getLimbN 3 = 0)

/-- n=4 v5 DIV lane, shift=0 case, dispatching on the runtime borrow certificate.
    Shift=0 analog of `evm_div_n4_lane_shiftNz_v5_of_cert` (#7614). -/
theorem evm_div_n4_lane_shift0_v5_of_cert (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert : n4Shift0LaneRuntimeCertV5 a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hbnz_lor : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  rcases hcert with ⟨hborrow, hd0, hd1, hd2, hd3⟩ | ⟨hborrow, hcarry2, hd0, hd1, hd2, hd3⟩
  · -- call+skip branch
    exact evm_div_n4_lane_shift0_callSkip_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hbnz_lor hb3nz hshift_z halign hborrow hd0 hd1 hd2 hd3
  · -- call+addback branch
    exact evm_div_n4_lane_shift0_callAddback_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hbnz_lor hb3nz hshift_z halign hborrow hcarry2 hd0 hd1 hd2 hd3

end EvmAsm.Evm64
