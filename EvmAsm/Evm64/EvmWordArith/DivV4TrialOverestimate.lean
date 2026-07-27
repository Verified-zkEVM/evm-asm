/-
  EvmAsm.Evm64.EvmWordArith.DivV4TrialOverestimate

  Named frontier predicate for the unconditional `+1` Knuth-A bound on the
  v4 call-trial quotient `divKTrialCallV4QHat`.

  The bead-level acceptance criteria (`7.1.4.1`) state:
    `(div128Quot_v4 uHi uLo vTop).toNat ≤ (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1`
  under `uHi < vTop` and normalisation conditions.

  Existing lemmas in `CallSkipLowerBoundV4/UpperBound.lean` prove this bound
  under *runtime* conditions (`un21 < vTop`, `rhatdd hi = 0`, etc.).  The
  bead frontier is to prove it under just the call regime + normalisation,
  by case-splitting on `un21 < vTop` and using the v4 Phase-2 2-correction
  exactness in the corner cases.

  This file names the predicate `DivKTrialCallV4QHatLeFloorPlusOne` so
  downstream beads and PRs have a single attackable target.  The
  predicate is *parametrised* on `(uHi, uLo, vTop)` and the normalisation
  context.

  Companion to `MulsubMaxC3OneOfCarryZero` / `MulsubBltC3OneOfCarryZero`
  (the c3 reachability frontiers).  Together these are the three named
  arithmetic frontiers gating the final `evm_div_stack_spec_unconditional`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The v4 call-trial Knuth-A `+1` bound at `(uHi, uLo, vTop)`.

    `vTop` is expected to be normalised (`2^63 ≤ vTop.toNat`) and `uHi`
    to be in the call regime (`uHi < vTop`); the unconditional discharge
    of this predicate is the open frontier (bead `7.1.4.1`).

    Specialises directly to the `hq_over` premise of the BLT-path bridges
    `loopBodyN{2,3}CallAddbackCarry2NzV4_of_overestimate_c3` when composed
    with val256-level normalisation. -/
def DivKTrialCallV4QHatLeFloorPlusOne (uHi uLo vTop : Word) : Prop :=
  (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1

end EvmAsm.Evm64
