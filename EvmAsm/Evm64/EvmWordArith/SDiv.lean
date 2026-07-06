/-
  EvmAsm.Evm64.EvmWordArith.SDiv

  EVM SDIV semantics: signed two's-complement division of 256-bit words,
  with the EVM spec short-circuits already baked into `BitVec.sdiv`:

    * `divisor = 0` ⇒ result `0`        (`BitVec.sdiv_zero`)
    * `dividend = −2^255 ∧ divisor = −1` ⇒ result `−2^255`
                                          (`BitVec.intMin_sdiv_neg_one`)

  Both align with the executable spec
  (`execution-specs/src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py`,
  function `sdiv`) and the EVM Yellow Paper §3 truncating-toward-zero
  semantics. This file provides the `EvmWord.sdiv` wrapper plus the
  correctness bridge connecting it to `Int.tdiv`.

  Slice 3 of evm-asm-34sg (#90 SDIV / SMOD opcodes), beads
  `evm-asm-kvs4`. SMOD lives in a sibling slice (5 / `evm-asm-bjnb`).
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- EVM SDIV semantics
-- ============================================================================

/-- EVM SDIV: signed two's-complement integer division on 256-bit words.

    Identical to `BitVec.sdiv` because the latter already implements the
    EVM short-circuits:

    * `BitVec.sdiv_zero` makes any-by-zero return `0`.
    * `BitVec.intMin_sdiv_neg_one` makes `(−2^255).sdiv (−1) = −2^255`,
      so the signed-overflow case is handled (rather than wrapping to the
      mathematical result `+2^255` which is unrepresentable). -/
def sdiv (a b : EvmWord) : EvmWord := BitVec.sdiv a b

-- ============================================================================
-- Edge-case lemmas
-- ============================================================================

@[simp]
theorem sdiv_zero_right {a : EvmWord} : sdiv a 0 = 0 := by
  simp [sdiv]

@[simp]
theorem zero_sdiv_left {b : EvmWord} : sdiv 0 b = 0 := by
  simp [sdiv]

/-- The signed-division overflow case: `(−2^255) / (−1) = −2^255` rather
    than the unrepresentable `+2^255`. This matches the EVM executable
    spec's short-circuit on the unique signed overflow point. -/
theorem sdiv_intMin_neg_one : sdiv (BitVec.intMin 256) (-1) = BitVec.intMin 256 := by
  show (BitVec.intMin 256).sdiv (-1) = BitVec.intMin 256
  have h : (-1 : BitVec 256) = -1#256 := by decide
  rw [h, BitVec.intMin_sdiv_neg_one]

-- Closed truncation examples used by the opcode-level edge-case suite.
theorem sdiv_neg_one_two : sdiv (-1 : EvmWord) 2 = 0 := by
  show (-1 : BitVec 256).sdiv 2 = 0
  decide

theorem sdiv_pos_neg_trunc : sdiv (7 : EvmWord) (-2) = (-3 : EvmWord) := by
  show (7 : BitVec 256).sdiv (-2) = (-3 : BitVec 256)
  decide

theorem sdiv_neg_pos_trunc : sdiv (-7 : EvmWord) 2 = (-3 : EvmWord) := by
  show (-7 : BitVec 256).sdiv 2 = (-3 : BitVec 256)
  decide

-- ============================================================================
-- Correctness vs `Int.tdiv` (the spec formula)
-- ============================================================================

/-- Outside the unique overflow point, `EvmWord.sdiv` agrees with the
    executable-spec formula: the truncating-toward-zero integer division
    of the signed interpretations of the operands.

    `BitVec.toInt_sdiv_of_ne_or_ne` is the underlying lemma; this just
    relabels it through the `EvmWord.sdiv` wrapper. The two short-circuit
    cases (`b = 0`, the overflow point) are handled by `sdiv_zero_right`
    and `sdiv_intMin_neg_one`. -/
theorem sdiv_correct (a b : EvmWord)
    (h : a ≠ BitVec.intMin 256 ∨ b ≠ -1) :
    (sdiv a b).toInt = a.toInt.tdiv b.toInt := by
  simpa [sdiv] using BitVec.toInt_sdiv_of_ne_or_ne (w := 256) a b h

end EvmWord

end EvmAsm.Evm64
