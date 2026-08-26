/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5CodeModelBridge

  Mathematical core of the v5 div128 **code-vs-model** bridge.

  The div128 RISC-V code (whose post is `div128V5SpecPost`) computes the capped
  Phase-1a / Phase-2a remainder *incrementally*:

      rhatc_code = rhat + (q1 - cap) * dHi        -- one extra FMA after capping

  whereas the clean model `div128Quot_v5` (used by the n=1 schoolbook
  `fullDivN1*V5` and the trial defs `divKTrialCallV5*`) writes the same value in
  closed form:

      rhatc_model = uHi - q1c * dHi    (with q1c = cap on the capped branch)

  Since `rhat = uHi - q1 * dHi`, these agree by ring arithmetic over the
  `CommRing` `Word = BitVec 64`.  This lemma is the key step in the eventual
  bridge `div128V5SpecPost`'s quotient register `q = div128Quot_v5` (= the proved
  `divKTrialCallV5QHat`), which connects the v5 loop-body execution result to the
  proven v5 quotient correctness (`fullDivN1QuotientWordV5 = EvmWord.div`, #7232).
  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.LoopDefs.IterV5
public import Mathlib.Tactic.Ring
public import Mathlib.Data.BitVec

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **rhatc code = model (capped branch).**  The incremental code form
    `rhat + (q1 - cap) * dHi` (with `rhat = uHi - q1 * dHi`) equals the closed
    model form `uHi - cap * dHi`.  Pure ring identity over `Word = BitVec 64`. -/
theorem div128V5_rhatc_correction_eq (uHi q1 cap dHi : Word) :
    (uHi - q1 * dHi) + (q1 - cap) * dHi = uHi - cap * dHi := by
  ring

/-- The same identity in the exact shape the code post uses, with `rhat`
    abstracted: given `rhat = uHi - q1 * dHi`, the code's capped remainder
    `rhat + (q1 - cap) * dHi` is the model's `uHi - cap * dHi`. -/
theorem div128V5_rhatc_correction_eq_of_rhat
    (uHi q1 cap dHi rhat : Word) (hrhat : rhat = uHi - q1 * dHi) :
    rhat + (q1 - cap) * dHi = uHi - cap * dHi := by
  subst hrhat; ring

end EvmAsm.Evm64
