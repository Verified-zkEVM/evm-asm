/-
  EvmAsm.Rv64.SailEquiv.SailStepAttr

  Registers the `sail_step` simp attribute used by the `sail_reduce` tactic (see
  `VmemReduction.lean`). `register_simp_attr` must live in a file imported by its
  users — it cannot be declared and used in the same file — mirroring the project's
  `RegOpsAttr.lean` / `AddrNormAttr.lean` convention (see GRIND.md).
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

register_simp_attr sail_step
