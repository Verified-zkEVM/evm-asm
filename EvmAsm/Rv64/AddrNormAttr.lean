/-
  EvmAsm.Rv64.AddrNormAttr

  Declares the `rv64_addr` simp attribute used by `AddrNorm.lean`.

  Split out from `AddrNorm.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code should
  import `AddrNorm.lean` (which imports this file) — not this file directly.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp/grind set for Rv64 address arithmetic. Collects `BitVec.add_assoc`
    rewrites plus atomic `signExtend13` / `signExtend21` evaluations on the
    concrete branch / jump / frame offsets that recur throughout the Rv64 and
    Evm64 proof layers. GRIND.md Phase 3. -/
register_simp_attr rv64_addr
