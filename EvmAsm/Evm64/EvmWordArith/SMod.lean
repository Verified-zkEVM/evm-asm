/-
  EvmAsm.Evm64.EvmWordArith.SMod

  EVM SMOD semantics: signed two's-complement modulo of 256-bit words,
  with the result taking the sign of the dividend.

  EVM short-circuit: `divisor = 0` ⇒ result `0`.
  Otherwise SMOD is the truncating-toward-zero remainder:
  `r = sign(x) * (|x| % |y|)`, matching `Int.tmod` of the signed
  interpretations.

  Mirrors `EvmAsm.Evm64.EvmWordArith.SDiv` (slice 3 / `evm-asm-kvs4`).
  Slice 5a of evm-asm-34sg (#90 SDIV / SMOD opcodes), beads
  `evm-asm-pc8g6`. The full evm_smod RISC-V program + stack spec lives
  in sibling slice 5 (`evm-asm-bjnb`).

  Reference: `execution-specs/src/ethereum/forks/amsterdam/vm/instructions/arithmetic.py`,
  function `smod`. Underlying lemma: `BitVec.toInt_srem`. Note that
  `BitVec.srem x 0#w = x` (not `0`), so we wrap `BitVec.srem` with the
  EVM zero-divisor short-circuit.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- EVM SMOD semantics
-- ============================================================================

/-- EVM SMOD: signed two's-complement integer remainder on 256-bit words,
    sign of the dividend.

    Wraps `BitVec.srem` with the EVM zero-divisor short-circuit
    (`y = 0 ⇒ 0`). `BitVec.srem` itself returns `x` on `y = 0`, which is
    the SMT-LIB convention but not the EVM one. -/
def smod (a b : EvmWord) : EvmWord :=
  if b = 0 then 0 else BitVec.srem a b

-- ============================================================================
-- Edge-case lemmas
-- ============================================================================

@[simp]
theorem smod_zero_right {a : EvmWord} : smod a 0 = 0 := by
  simp [smod]

@[simp]
theorem zero_smod_left {b : EvmWord} : smod 0 b = 0 := by
  unfold smod
  split
  · rfl
  · simp [BitVec.zero_srem]

-- Closed sign-of-dividend examples used by the opcode-level edge-case suite.
theorem smod_neg_pos_sign : smod (-3 : EvmWord) 2 = (-1 : EvmWord) := by
  decide

theorem smod_pos_neg_sign : smod (3 : EvmWord) (-2) = (1 : EvmWord) := by
  decide

theorem smod_neg_neg_sign : smod (-3 : EvmWord) (-2) = (-1 : EvmWord) := by
  decide

theorem smod_intMin_neg_one : smod (BitVec.intMin 256) (-1) = 0 := by
  decide

-- ============================================================================
-- Correctness vs `Int.tmod` (the spec formula)
-- ============================================================================

/-- For nonzero divisors, `EvmWord.smod` agrees with the executable-spec
    formula: the truncating-toward-zero integer remainder of the signed
    interpretations of the operands.

    `BitVec.toInt_srem` is the underlying lemma; this just relabels it
    through the `EvmWord.smod` wrapper. The zero-divisor short-circuit
    is handled by `smod_zero_right`. -/
theorem smod_correct (a b : EvmWord) (h : b ≠ 0) :
    (smod a b).toInt = a.toInt.tmod b.toInt := by
  unfold smod
  rw [if_neg h]
  exact BitVec.toInt_srem (w := 256) a b

end EvmWord

end EvmAsm.Evm64
