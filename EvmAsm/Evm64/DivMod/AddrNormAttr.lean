/-
  EvmAsm.Evm64.DivMod.AddrNormAttr

  Declares the `divmod_addr` simp attribute used by `AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code should
  import `AddrNorm.lean` (which imports this file) — not this file directly.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set for DivMod address arithmetic. Collects atomic evaluations of
    `signExtend12`, `<<<`, and `BitVec.toNat` on concrete literals that appear
    throughout the DivMod composition proofs. -/
register_simp_attr divmod_addr
