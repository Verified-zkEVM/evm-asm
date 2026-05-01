/-
  EvmAsm.Evm64.Exp.AddrNormAttr

  Declares the `exp_addr` simp attribute used by `Exp/AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code should
  import `Exp/AddrNorm.lean` (which imports this file) — not this file directly.

  Skeleton placeholder for GH #92 (EXP opcode). No tagged lemmas yet.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set for EXP address arithmetic. Will collect atomic evaluations of
    `signExtend12`, `<<<`, and `BitVec.toNat` on concrete literals that arise
    in EXP composition proofs. -/
register_simp_attr exp_addr
