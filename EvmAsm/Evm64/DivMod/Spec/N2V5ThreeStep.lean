/-
  EvmAsm.Evm64.DivMod.Spec.N2V5ThreeStep

  The generic 3-digit telescoping lemma for the v5 n=2 schoolbook — the n=2
  analog of `fullDivN1V5_four_step_nat` (N1V5Quotient.lean).  It accumulates the
  three per-digit conservation equations (top window `W2`, then each lower digit
  bringing in the next dividend limb at the bottom with the previous remainder
  shifted up by `2^64`) into the single Knuth mulsub equation

      a = (q2·2^128 + q1·2^64 + q0)·V + R0r.

  The per-digit conservations of `iterN2V5_true_conservation`
  (`fullDivN2R{2,1,0}V5_conservation`, #7342/#7343) supply the three step
  equations once each remainder is collapsed to its low two limbs (rem < V ≤
  2^128 ⇒ high limbs and the overflow cell are zero); feeding them here gives
  `fullDivN2MulSubEqV5`.  Bead `evm-asm-wbc4i.9.2`.
-/

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Linarith
import EvmAsm.Evm64.EvmWord

namespace EvmAsm.Evm64


open EvmWord

/-- The v5 n=2 3-digit accumulation (pure `Nat`).  `W2` is the top 3-limb window
    value `nu2 + 2^64·nu3 + 2^128·nu4`; `R2r`/`R1r` are the collapsed 2-limb
    intermediate remainders; `R0r` is the final remainder value.  Mirror of
    `fullDivN1V5_four_step_nat`, one digit shorter (the top digit consumes a
    whole window at once). -/
theorem fullDivN2V5_three_step_nat
    {a V q2 q1 q0 nu0 nu1 W2 R2r R1r R0r : Nat}
    (hfirst : a = nu0 + 2 ^ 64 * nu1 + 2 ^ 128 * W2)
    (hstep2 : W2 = q2 * V + R2r)
    (hstep1 : nu1 + 2 ^ 64 * R2r = q1 * V + R1r)
    (hstep0 : nu0 + 2 ^ 64 * R1r = q0 * V + R0r) :
    a = (q2 * 2 ^ 128 + q1 * 2 ^ 64 + q0) * V + R0r := by
  subst hfirst hstep2
  nlinarith [hstep1, hstep0]

end EvmAsm.Evm64
