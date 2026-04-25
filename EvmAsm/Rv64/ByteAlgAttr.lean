/-
  EvmAsm.Rv64.ByteAlgAttr

  Declares the `byte_alg` simp attribute used by `ByteAlg.lean`.

  Split out from `ByteAlg.lean` because Lean 4 does not allow an attribute
  to be used in the same file in which it is declared. Downstream code should
  import `ByteAlg.lean` (which imports this file) — not this file directly.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp/grind set for `extractByte` / `replaceByte` algebra on 64-bit words.
    Collects the commute / cancel identities (`extractByte (replaceByte w p b) p
    = b`, future `..._diff` / `replaceByte_replaceByte_*` siblings) that drive
    byte-level opcode proofs. GRIND.md Phase 4. -/
register_simp_attr byte_alg
