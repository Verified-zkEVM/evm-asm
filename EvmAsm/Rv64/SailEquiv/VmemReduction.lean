/-
  EvmAsm.Rv64.SailEquiv.VmemReduction

  Building blocks for discharging the `h_exec` hypothesis carried by the `MemProofs`
  `*_sail_equiv` lemmas — i.e. for proving the SAIL `execute_LOAD`/`execute_STORE`
  bare-mode `vmem_read`/`vmem_write` reduction the original lemmas defer.

  This file currently establishes **lemma #1**: the leaf data-correctness bridge tying
  the SAIL physical read (`readBytes`, which appends bytes little-endian) to the
  abstraction relation's `reconstructDword`. With all `width` bytes present in `mem`,
  `readBytes 8 a` succeeds and yields exactly `reconstructDword sSail.mem a` — so the
  value a doubleword `LOAD` writes back is provably the toy model's `getMem` value.

  Remaining building blocks (for the full discharge, see
  `docs/agents/sail-memory-discharge-bootstrap.md`): the `pmpCheck` 16-entry loop, the
  `untilFuelM` single-iteration reduction, `translateAddr` bare-mode, and `pmaCheck`
  region membership — each consuming part of the bare-mode precondition bundle.
-/

import EvmAsm.Rv64.SailEquiv.MemProofs

open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

/-- Pure `BitVec` identity: the little-endian nested `append` that `readBytes 8`
    produces equals the or-of-shifts that `reconstructDword` uses (`b0` = lowest byte). -/
theorem append8_eq_or_shifts (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0
      : BitVec 64)
    = b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< 8) ||| (b2.zeroExtend 64 <<< 16) |||
      (b3.zeroExtend 64 <<< 24) ||| (b4.zeroExtend 64 <<< 32) ||| (b5.zeroExtend 64 <<< 40) |||
      (b6.zeroExtend 64 <<< 48) ||| (b7.zeroExtend 64 <<< 56) := by
  show (((((((b7 ++ b6) ++ b5) ++ b4) ++ b3) ++ b2) ++ b1) ++ b0 : BitVec 64) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
             BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, ← Bool.if_false_right]
  have h64 : i < 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 := hi
  simp only [if_pos h64, if_pos (show i - 8  < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 16 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 24 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 32 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 40 < 8+8+8+8+8+8+8+8 by omega),
                         if_pos (show i - 48 < 8+8+8+8+8+8+8+8 by omega)]
  rcases Nat.lt_or_ge i 8 with h0 | h0
  · -- [0, 8): b0 is active
    simp [h0, show i < 16 by omega, show i < 24 by omega, show i < 32 by omega,
          show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  rcases Nat.lt_or_ge i 16 with h1 | h1
  · -- [8, 16): b1 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega),
          show ¬ i < 8 by omega, show i < 16 by omega, show i < 24 by omega,
          show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show i - 8 < 8 by omega]
  rcases Nat.lt_or_ge i 24 with h2 | h2
  · -- [16, 24): b2 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show i < 24 by omega,
          show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 32 with h3 | h3
  · -- [24, 32): b3 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show i < 32 by omega,
          show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show i - 8 - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 40 with h4 | h4
  · -- [32, 40): b4 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show i - 8 - 8 - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 48 with h5 | h5
  · -- [40, 48): b5 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          BitVec.getLsbD_of_ge b4 (i-32) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show ¬ i < 40 by omega, show i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 < 8 by omega, show i - 8 - 8 - 8 - 8 - 8 < 8 by omega]
    rfl
  rcases Nat.lt_or_ge i 56 with h6 | h6
  · -- [48, 56): b6 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          BitVec.getLsbD_of_ge b4 (i-32) (by omega), BitVec.getLsbD_of_ge b5 (i-40) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show ¬ i < 40 by omega, show ¬ i < 48 by omega, show i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 - 8 < 8 by omega,
          show i - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega]
    rfl
  · -- [56, 64): b7 is active
    simp [BitVec.getLsbD_of_ge b0 i (by omega), BitVec.getLsbD_of_ge b1 (i-8) (by omega),
          BitVec.getLsbD_of_ge b2 (i-16) (by omega), BitVec.getLsbD_of_ge b3 (i-24) (by omega),
          BitVec.getLsbD_of_ge b4 (i-32) (by omega), BitVec.getLsbD_of_ge b5 (i-40) (by omega),
          BitVec.getLsbD_of_ge b6 (i-48) (by omega),
          show ¬ i < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, show ¬ i < 32 by omega,
          show ¬ i < 40 by omega, show ¬ i < 48 by omega, show ¬ i < 56 by omega,
          show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 < 8 by omega, show ¬ i - 8 - 8 - 8 - 8 - 8 < 8 by omega,
          show ¬ i - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega, show i - 56 < 64 by omega]
    rfl

/-- **Leaf data bridge.** If the 8 bytes at `a … a+7` are present in SAIL memory, the
    physical doubleword read `readBytes 8 a` succeeds, leaves the state untouched, and
    returns exactly `reconstructDword sSail.mem a` — the value the abstraction relation
    (`StateRel.mem_agree`) ties to the toy model's `getMem`. -/
theorem readBytes8_eq_reconstruct (sSail : SailState) (a : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : sSail.mem.get? a = some b0) (h1 : sSail.mem.get? (a+1) = some b1)
    (h2 : sSail.mem.get? (a+2) = some b2) (h3 : sSail.mem.get? (a+3) = some b3)
    (h4 : sSail.mem.get? (a+4) = some b4) (h5 : sSail.mem.get? (a+5) = some b5)
    (h6 : sSail.mem.get? (a+6) = some b6) (h7 : sSail.mem.get? (a+7) = some b7) :
    runSail (readBytes 8 a) sSail = some ((reconstructDword sSail.mem a, none), sSail) := by
  simp only [runSail, readBytes, readByte, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [reconstructDword, Std.ExtHashMap.getD_eq_getD_getElem?,
    h0, h1, h2, h3, h4, h5, h6, h7, Option.getD_some, append8_eq_or_shifts]

end EvmAsm.Rv64.SailEquiv
