/-
  EvmAsm.Evm64.DivMod.AddrNorm

  Address-normalization simp set and `divmod_addr` tactic for DivMod composition
  proofs. Resolves issue #263.

  The DivMod composition proofs contain ~112 one-off address-equality lemmas,
  each of the form
      `(sp + signExtend12 N₁ ± k <<< 3) ± signExtend12 N₂ = sp + signExtend12 N₃`
  and closed by
      `simp only [<atomic signExtend12/shift/toNat facts>]; bv_omega`.

  This file centralizes the atomic facts as the `divmod_addr` simp set (and
  `@[grind =]`-registers them for `grind`-based closing), then exposes a
  `divmod_addr` tactic that tries `grind` first and falls back to
  `simp only [divmod_addr]; bv_omega`.

  Adding a new concrete offset or shift amount is one line here — every
  downstream proof that uses `by divmod_addr` picks it up automatically.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Evm64.DivMod.AddrNormAttr

namespace EvmAsm.Evm64.DivMod.AddrNorm

open EvmAsm.Rv64

-- ============================================================================
-- Atomic `signExtend12` evaluations
--
-- For offsets < 2^11, the result equals the input (zero-extended).
-- For offsets ≥ 2^11, the result is (2^64 + offset - 2^12), i.e. the
-- two's-complement encoding of (offset - 4096).
-- All proofs are `by decide` (kernel-checkable).
-- ============================================================================

-- Small offsets (< 2^11): result = input
@[divmod_addr, grind =] theorem se12_0  : signExtend12 (0  : BitVec 12) = (0  : Word) := by decide
@[divmod_addr, grind =] theorem se12_1  : signExtend12 (1  : BitVec 12) = (1  : Word) := by decide
@[divmod_addr, grind =] theorem se12_2  : signExtend12 (2  : BitVec 12) = (2  : Word) := by decide
@[divmod_addr, grind =] theorem se12_3  : signExtend12 (3  : BitVec 12) = (3  : Word) := by decide
@[divmod_addr, grind =] theorem se12_4  : signExtend12 (4  : BitVec 12) = (4  : Word) := by decide
@[divmod_addr, grind =] theorem se12_8  : signExtend12 (8  : BitVec 12) = (8  : Word) := by decide
@[divmod_addr, grind =] theorem se12_12 : signExtend12 (12 : BitVec 12) = (12 : Word) := by decide
@[divmod_addr, grind =] theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
@[divmod_addr, grind =] theorem se12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide
@[divmod_addr, grind =] theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
@[divmod_addr, grind =] theorem se12_40 : signExtend12 (40 : BitVec 12) = (40 : Word) := by decide
@[divmod_addr, grind =] theorem se12_48 : signExtend12 (48 : BitVec 12) = (48 : Word) := by decide
@[divmod_addr, grind =] theorem se12_56 : signExtend12 (56 : BitVec 12) = (56 : Word) := by decide

-- Large offsets (≥ 2^11): result = 2^64 + offset - 2^12
@[divmod_addr, grind =] theorem se12_3944 : signExtend12 (3944 : BitVec 12) = (18446744073709551464 : Word) := by decide
@[divmod_addr, grind =] theorem se12_3952 : signExtend12 (3952 : BitVec 12) = (18446744073709551472 : Word) := by decide
@[divmod_addr, grind =] theorem se12_3960 : signExtend12 (3960 : BitVec 12) = (18446744073709551480 : Word) := by decide
@[divmod_addr, grind =] theorem se12_3968 : signExtend12 (3968 : BitVec 12) = (18446744073709551488 : Word) := by decide
@[divmod_addr, grind =] theorem se12_3976 : signExtend12 (3976 : BitVec 12) = (18446744073709551496 : Word) := by decide
@[divmod_addr, grind =] theorem se12_3984 : signExtend12 (3984 : BitVec 12) = (18446744073709551504 : Word) := by decide
@[divmod_addr, grind =] theorem se12_3992 : signExtend12 (3992 : BitVec 12) = (18446744073709551512 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4000 : signExtend12 (4000 : BitVec 12) = (18446744073709551520 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4008 : signExtend12 (4008 : BitVec 12) = (18446744073709551528 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4016 : signExtend12 (4016 : BitVec 12) = (18446744073709551536 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4024 : signExtend12 (4024 : BitVec 12) = (18446744073709551544 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4032 : signExtend12 (4032 : BitVec 12) = (18446744073709551552 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4040 : signExtend12 (4040 : BitVec 12) = (18446744073709551560 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4048 : signExtend12 (4048 : BitVec 12) = (18446744073709551568 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4056 : signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4064 : signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4072 : signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4080 : signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4088 : signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) := by decide
@[divmod_addr, grind =] theorem se12_4095 : signExtend12 (4095 : BitVec 12) = (18446744073709551615 : Word) := by decide

-- ============================================================================
-- Atomic `(k : BitVec 6).toNat` evaluations
-- ============================================================================

@[divmod_addr, grind =] theorem bv6_toNat_2  : (2  : BitVec 6).toNat = 2  := by decide
@[divmod_addr, grind =] theorem bv6_toNat_3  : (3  : BitVec 6).toNat = 3  := by decide
@[divmod_addr, grind =] theorem bv6_toNat_4  : (4  : BitVec 6).toNat = 4  := by decide
@[divmod_addr, grind =] theorem bv6_toNat_8  : (8  : BitVec 6).toNat = 8  := by decide
@[divmod_addr, grind =] theorem bv6_toNat_16 : (16 : BitVec 6).toNat = 16 := by decide
@[divmod_addr, grind =] theorem bv6_toNat_32 : (32 : BitVec 6).toNat = 32 := by decide
@[divmod_addr, grind =] theorem bv6_toNat_48 : (48 : BitVec 6).toNat = 48 := by decide
@[divmod_addr, grind =] theorem bv6_toNat_56 : (56 : BitVec 6).toNat = 56 := by decide
@[divmod_addr, grind =] theorem bv6_toNat_60 : (60 : BitVec 6).toNat = 60 := by decide
@[divmod_addr, grind =] theorem bv6_toNat_62 : (62 : BitVec 6).toNat = 62 := by decide
@[divmod_addr, grind =] theorem bv6_toNat_63 : (63 : BitVec 6).toNat = 63 := by decide

-- ============================================================================
-- Atomic `(k : Word) <<< 3` evaluations
-- (k ∈ {0..4} is the range actually used by DivMod u-base offsets.)
-- ============================================================================

@[divmod_addr, grind =] theorem word_shl3_0 : (0 : Word) <<< 3 = (0  : Word) := by decide
@[divmod_addr, grind =] theorem word_shl3_1 : (1 : Word) <<< 3 = (8  : Word) := by decide
@[divmod_addr, grind =] theorem word_shl3_2 : (2 : Word) <<< 3 = (16 : Word) := by decide
@[divmod_addr, grind =] theorem word_shl3_3 : (3 : Word) <<< 3 = (24 : Word) := by decide
@[divmod_addr, grind =] theorem word_shl3_4 : (4 : Word) <<< 3 = (32 : Word) := by decide

-- ============================================================================
-- `divmod_addr` tactic
--
-- Primary: `grind` (sees all @[grind =]-registered atomic facts).
-- Fallback: `simp only [divmod_addr]; bv_omega` (matches hand-written shape;
-- tiny proof term). The fallback covers edge cases where grind's closure
-- doesn't fully land.
-- ============================================================================

/-- Close a DivMod address-arithmetic equality. Tries `grind` first (fastest,
    most resilient — picks up any `@[grind =]` fact in `AddrNorm`), then falls
    back to `simp only [divmod_addr]; bv_omega` for edge shapes. -/
macro "divmod_addr" : tactic =>
  `(tactic| first
    | grind
    | (simp only [divmod_addr]; bv_omega))

end EvmAsm.Evm64.DivMod.AddrNorm
