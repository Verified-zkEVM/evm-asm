/-
  EvmAsm.Evm64.Exp.AddrNormAttr

  Declares the `exp_addr` simp attribute used by `Exp/AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code should
  import `Exp/AddrNorm.lean` (which imports this file) rather than this file
  directly; tagged EXP address lemmas live there.
-/

module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

/-- Simp set for EXP address arithmetic: atomic evaluations of `signExtend12`,
    `signExtend13`, shifts, and `BitVec.toNat` on concrete literals that arise
    in EXP composition proofs. -/
register_simp_attr exp_addr
