/-
  EvmAsm.Rv64.AddrNorm

  `rv64_addr` grindset for Rv64 address arithmetic (GRIND.md Phase 3).

  Historical baseline: the existing `bv_addr` macro (in `Tactics/SeqFrame.lean`)
  closes simple `(a + k₁) + k₂ = a + k₃` shapes via
  `simp only [BitVec.add_assoc]; rfl`. That works for 578 existing callsites
  in DivMod but does not handle address equalities that mix
  `signExtend13` / `signExtend21` evaluations (branch/jump/frame offsets),
  which are currently closed by hand-written `show … from by decide` chains.

  This file centralizes the atomic facts once:

    * `BitVec.add_assoc` (and the right-identity `x + 0 = x`) as `@[rv64_addr, grind =]`
    * every `signExtend13 N : Word = <const>` and `signExtend21 N : Word = <const>`
      pair used in the repo today

  and exposes a `rv64_addr` tactic that tries `grind` first (resilient to
  vocabulary growth) and falls back to `simp only [rv64_addr]; rfl` (smaller
  proof term, matches `bv_addr`'s shape). Callers that migrate from `bv_addr`
  get the signExtend13/21 reductions for free.

  Adding a new concrete offset is one line here — every downstream proof that
  uses `by rv64_addr` picks it up automatically.
-/

import EvmAsm.Rv64.Instructions
import EvmAsm.Rv64.AddrNormAttr

namespace EvmAsm.Rv64.AddrNorm

open EvmAsm.Rv64

-- ============================================================================
-- Core algebraic identities for Word
-- ============================================================================

@[rv64_addr, grind =]
theorem word_zero_add (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

@[rv64_addr, grind =]
theorem word_add_zero (x : Word) : x + (0 : Word) = x := BitVec.add_zero x

-- ============================================================================
-- Atomic `signExtend13` evaluations
--
-- For offsets < 2^12 the result equals the input (zero-extended).
-- For offsets ≥ 2^12 the result is 2^64 + offset - 2^13 (sign-bit triggered).
-- 2^12 = 4096; 2^13 = 8192. Callers generating ≥ 8192 are ill-formed.
-- All proofs are `by decide` (kernel-checkable).
-- ============================================================================

-- Small offsets (< 2^12): result = input
@[rv64_addr, grind =] theorem se13_0   : signExtend13 (0   : BitVec 13) = (0   : Word) := by decide
@[rv64_addr, grind =] theorem se13_4   : signExtend13 (4   : BitVec 13) = (4   : Word) := by decide
@[rv64_addr, grind =] theorem se13_8   : signExtend13 (8   : BitVec 13) = (8   : Word) := by decide
@[rv64_addr, grind =] theorem se13_12  : signExtend13 (12  : BitVec 13) = (12  : Word) := by decide
@[rv64_addr, grind =] theorem se13_16  : signExtend13 (16  : BitVec 13) = (16  : Word) := by decide
@[rv64_addr, grind =] theorem se13_20  : signExtend13 (20  : BitVec 13) = (20  : Word) := by decide
@[rv64_addr, grind =] theorem se13_24  : signExtend13 (24  : BitVec 13) = (24  : Word) := by decide
@[rv64_addr, grind =] theorem se13_32  : signExtend13 (32  : BitVec 13) = (32  : Word) := by decide
@[rv64_addr, grind =] theorem se13_36  : signExtend13 (36  : BitVec 13) = (36  : Word) := by decide
@[rv64_addr, grind =] theorem se13_44  : signExtend13 (44  : BitVec 13) = (44  : Word) := by decide
@[rv64_addr, grind =] theorem se13_60  : signExtend13 (60  : BitVec 13) = (60  : Word) := by decide
@[rv64_addr, grind =] theorem se13_68  : signExtend13 (68  : BitVec 13) = (68  : Word) := by decide
@[rv64_addr, grind =] theorem se13_92  : signExtend13 (92  : BitVec 13) = (92  : Word) := by decide
@[rv64_addr, grind =] theorem se13_96  : signExtend13 (96  : BitVec 13) = (96  : Word) := by decide
@[rv64_addr, grind =] theorem se13_100 : signExtend13 (100 : BitVec 13) = (100 : Word) := by decide
@[rv64_addr, grind =] theorem se13_128 : signExtend13 (128 : BitVec 13) = (128 : Word) := by decide
@[rv64_addr, grind =] theorem se13_140 : signExtend13 (140 : BitVec 13) = (140 : Word) := by decide
@[rv64_addr, grind =] theorem se13_156 : signExtend13 (156 : BitVec 13) = (156 : Word) := by decide
@[rv64_addr, grind =] theorem se13_168 : signExtend13 (168 : BitVec 13) = (168 : Word) := by decide
@[rv64_addr, grind =] theorem se13_172 : signExtend13 (172 : BitVec 13) = (172 : Word) := by decide
@[rv64_addr, grind =] theorem se13_176 : signExtend13 (176 : BitVec 13) = (176 : Word) := by decide
@[rv64_addr, grind =] theorem se13_188 : signExtend13 (188 : BitVec 13) = (188 : Word) := by decide
@[rv64_addr, grind =] theorem se13_308 : signExtend13 (308 : BitVec 13) = (308 : Word) := by decide
@[rv64_addr, grind =] theorem se13_320 : signExtend13 (320 : BitVec 13) = (320 : Word) := by decide
@[rv64_addr, grind =] theorem se13_332 : signExtend13 (332 : BitVec 13) = (332 : Word) := by decide
@[rv64_addr, grind =] theorem se13_464 : signExtend13 (464 : BitVec 13) = (464 : Word) := by decide
@[rv64_addr, grind =] theorem se13_1020 : signExtend13 (1020 : BitVec 13) = (1020 : Word) := by decide

-- Large offsets (≥ 2^12): result = 2^64 + offset - 2^13
@[rv64_addr, grind =] theorem se13_7736 : signExtend13 (7736 : BitVec 13) = (18446744073709551160 : Word) := by decide
@[rv64_addr, grind =] theorem se13_8044 : signExtend13 (8044 : BitVec 13) = (18446744073709551468 : Word) := by decide

-- ============================================================================
-- Atomic `signExtend21` evaluations
--
-- 2^20 = 1048576; all offsets seen in the repo are far below, so result
-- equals input. New large-offset entries (≥ 2^20) follow the
-- `2^64 + offset - 2^21` shape like `signExtend13`.
-- ============================================================================

@[rv64_addr, grind =] theorem se21_0   : signExtend21 (0   : BitVec 21) = (0   : Word) := by decide
@[rv64_addr, grind =] theorem se21_8   : signExtend21 (8   : BitVec 21) = (8   : Word) := by decide
@[rv64_addr, grind =] theorem se21_12  : signExtend21 (12  : BitVec 21) = (12  : Word) := by decide
@[rv64_addr, grind =] theorem se21_16  : signExtend21 (16  : BitVec 21) = (16  : Word) := by decide
@[rv64_addr, grind =] theorem se21_24  : signExtend21 (24  : BitVec 21) = (24  : Word) := by decide
@[rv64_addr, grind =] theorem se21_32  : signExtend21 (32  : BitVec 21) = (32  : Word) := by decide
@[rv64_addr, grind =] theorem se21_36  : signExtend21 (36  : BitVec 21) = (36  : Word) := by decide
@[rv64_addr, grind =] theorem se21_40  : signExtend21 (40  : BitVec 21) = (40  : Word) := by decide
@[rv64_addr, grind =] theorem se21_48  : signExtend21 (48  : BitVec 21) = (48  : Word) := by decide
@[rv64_addr, grind =] theorem se21_64  : signExtend21 (64  : BitVec 21) = (64  : Word) := by decide
@[rv64_addr, grind =] theorem se21_68  : signExtend21 (68  : BitVec 21) = (68  : Word) := by decide
@[rv64_addr, grind =] theorem se21_96  : signExtend21 (96  : BitVec 21) = (96  : Word) := by decide
@[rv64_addr, grind =] theorem se21_124 : signExtend21 (124 : BitVec 21) = (124 : Word) := by decide
@[rv64_addr, grind =] theorem se21_132 : signExtend21 (132 : BitVec 21) = (132 : Word) := by decide
@[rv64_addr, grind =] theorem se21_200 : signExtend21 (200 : BitVec 21) = (200 : Word) := by decide
@[rv64_addr, grind =] theorem se21_212 : signExtend21 (212 : BitVec 21) = (212 : Word) := by decide
@[rv64_addr, grind =] theorem se21_252 : signExtend21 (252 : BitVec 21) = (252 : Word) := by decide
@[rv64_addr, grind =] theorem se21_268 : signExtend21 (268 : BitVec 21) = (268 : Word) := by decide
@[rv64_addr, grind =] theorem se21_560 : signExtend21 (560 : BitVec 21) = (560 : Word) := by decide

-- ============================================================================
-- `rv64_addr` tactic
--
-- Primary: `grind` (sees every `@[grind =]` fact in this file + BitVec
-- associativity via `word_zero_add`/`word_add_zero`).
-- Fallback: `simp only [rv64_addr, BitVec.add_assoc]; rfl` (smaller proof
-- term, matches `bv_addr`'s historical shape and resolves most pure
-- associativity goals in one step).
-- ============================================================================

/-- Close an Rv64 address-arithmetic equality, including shapes with
    `signExtend13`/`signExtend21` on concrete offsets. Tries `grind` first
    (fastest, most resilient — picks up any `@[grind =]` fact registered in
    `AddrNorm`), then falls back to `simp only [rv64_addr, BitVec.add_assoc]; rfl`
    for the pure associativity shape handled by the legacy `bv_addr`. -/
macro "rv64_addr" : tactic =>
  `(tactic| first
    | grind
    | (simp only [rv64_addr, BitVec.add_assoc]; rfl))

end EvmAsm.Rv64.AddrNorm

-- ============================================================================
-- Sanity: the tactic closes goals previously handled by `bv_addr` plus new
-- signExtend13/21 shapes that `bv_addr` could not touch.
-- ============================================================================

section Sanity
open EvmAsm.Rv64

-- Pure associativity (the old `bv_addr` workload).
example (a : Word) : (a + 4) + 8 = a + 12 := by rv64_addr

-- signExtend13 on a small positive offset.
example (a : Word) : a + signExtend13 (24 : BitVec 13) = a + 24 := by rv64_addr

-- signExtend13 on a large offset (≥ 2^12, sign-extended negative).
example (a : Word) : a + signExtend13 (7736 : BitVec 13) =
    a + (18446744073709551160 : Word) := by rv64_addr

-- signExtend21 on a small positive offset.
example (a : Word) : a + signExtend21 (252 : BitVec 21) = a + 252 := by rv64_addr

end Sanity
