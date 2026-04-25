/-
  EvmAsm.Rv64.RegOpsAttr

  Declares the `reg_ops` simp attribute used by `RegOps.lean`.

  Split out from `RegOps.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code should
  import `RegOps.lean` (which imports this file) — not this file directly.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp/grind set for `MachineState` register, PC, memory, code, committed,
    publicValues, and privateInput projection lemmas. Collects the shape
    `(s.set<Field> …).get<Other> = s.get<Other>` (plus `(s.set<F> …).<Other>
    = s.<Other>` for record fields) that fires at nearly every step of every
    `runBlock`-based proof. GRIND.md Phase 5. -/
register_simp_attr reg_ops
