/-
  EvmAsm.Rv64.SAsm.LoopFuel

  The counter-register bridge toolkit for data-dependent and nested loops
  (docs/sasm-design.md §3.10, docs/sasm-howto.md §4).

  A loop whose iteration count is only known at runtime (an RLP length
  field, a BAL item count) is verified with a *static* fuel cap and a
  runtime exit condition: the invariant ties the counter register to the
  index (`rf.get ctr = BitVec.ofNat 64 i`) and the limit register to the
  count decoded from the input ghost, and the `exhausted` VC closes from
  `i ≤ n` (in the invariant) plus `n ≤ cap` (a precondition on the decoded
  input).  These lemmas discharge the recurring BitVec/Nat conversions of
  that pattern: counter increments, `toNat` round-trips, and the
  `bltu`-vs-`Nat.lt` bridge in both directions.
-/

import EvmAsm.Rv64.SAsm.Ast

namespace EvmAsm.Rv64
namespace SAsm

/-- Counter increment: bumping the counter register is bumping the index.
    No side condition — both sides reduce mod `2^64`. -/
theorem ofNat_succ (i : Nat) :
    BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

/-- `toNat` round-trip for an in-range index. -/
theorem toNat_ofNat_lt {i : Nat} (h : i < 2 ^ 64) :
    (BitVec.ofNat 64 i).toNat = i := by
  simp only [BitVec.toNat_ofNat]
  omega

/-- The counter/limit bridge: an unsigned compare of the counter register
    (tied to index `i`) against a limit word is the `Nat` compare of the
    index against the limit's value.  Forward it gives `i < n` in
    `inv_step`/`.mem` goals; backward (via `not_congr`) it turns the
    negated exit condition into `n ≤ i` in `exhausted`/post goals. -/
theorem ult_ofNat_left {i : Nat} (v : Word) (hi : i < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 i) v = true ↔ i < v.toNat := by
  simp [BitVec.ult, toNat_ofNat_lt hi]

/-- `Cond.bltu` on a counter register tied to index `i`: the branch holds
    iff the index is below the limit register's value. -/
theorem Cond.holds_bltu_iff {rf : RegFile} {r1 r2 : Reg} {i : Nat}
    (h1 : rf.get r1 = BitVec.ofNat 64 i) (hi : i < 2 ^ 64) :
    (Cond.bltu r1 r2).holds rf ↔ i < (rf.get r2).toNat := by
  rw [Cond.holds, h1, ult_ofNat_left _ hi]

/-- Loop exit at the runtime count: if the counter (index `i ≤ n`) no
    longer compares below the limit register (value `n`), the loop ran
    exactly `n` iterations. -/
theorem index_eq_of_not_bltu {rf : RegFile} {r1 r2 : Reg} {i n : Nat}
    (h1 : rf.get r1 = BitVec.ofNat 64 i) (h2 : (rf.get r2).toNat = n)
    (hle : i ≤ n) (hi : i < 2 ^ 64)
    (hn : ¬ (Cond.bltu r1 r2).holds rf) : i = n := by
  rw [Cond.holds_bltu_iff h1 hi, h2] at hn
  omega

/-- A zero-extended loaded byte, as a `Nat`-valued limit. -/
theorem toNat_zeroExtend_byte (b : BitVec 8) :
    ((b.zeroExtend 64 : Word)).toNat = b.toNat := by
  have hb := b.isLt
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  omega

end SAsm
end EvmAsm.Rv64
