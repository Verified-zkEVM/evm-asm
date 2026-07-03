/-
  EvmAsm.Evm64.AddMod.Compose.CarryBranch

  Carry-branch (`N ≠ 0`, 257th carry bit set) machine-pipeline composition for
  the total ADDMOD program. Chains the six carry-path prepare/finish blocks and
  the three `evm_mod_callable_v5` near-calls (via `evm_addmod_v5_call_adapter`)
  into the carry-branch stack spec landing `EvmWord.addmod a b N`.

  Sub-task 1 (this slice): the own→generic register helper that feeds each MOD
  adapter (registers x9/x2/x10/x11 arrive `regOwn` after the prior call, but the
  adapter PRE `divModStackDispatchPreNoX1` needs them as `regIs` at some value —
  the adapter is generic in those values, so we choose them via `regOwn`'s
  existential).
-/

import EvmAsm.Evm64.AddMod.Compose.CallAdapter
import EvmAsm.Evm64.AddMod.Compose.CondSubSpec

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Choose the concrete value of a `regOwn` in the leading position of a
    `cpsTripleWithin` precondition. If the triple holds for every concrete
    `regIs r v` (leading a common tail `B`), it holds with the register merely
    owned. Used to thread the callable-shed registers (x9/x2/x10/x11) into the
    next MOD adapter, whose PRE fixes them at a generic value. -/
theorem cpsTripleWithin_pre_regOwn
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {r : Reg} {B Q : Assertion}
    (h : ∀ v, cpsTripleWithin nSteps entry exit_ cr (regIs r v ** B) Q) :
    cpsTripleWithin nSteps entry exit_ cr (regOwn r ** B) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hst, hcompat, hP⟩ := hPR
  have hP' : (regOwn r ** (B ** R)) hst := (sepConj_assoc hst).mp hP
  obtain ⟨v, hv⟩ := sepConj_choose_regOwn hP'
  have hv' : ((regIs r v ** B) ** R) hst := (sepConj_assoc hst).mpr hv
  exact h v R hR s hcr ⟨hst, hcompat, hv'⟩ hpc

end EvmAsm.Evm64.AddMod.Compose
