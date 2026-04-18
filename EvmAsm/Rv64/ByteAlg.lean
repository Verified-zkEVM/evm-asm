/-
  EvmAsm.Rv64.ByteAlg

  `byte_alg` grindset for `extractByte` / `replaceByte` algebra on 64-bit
  words (GRIND.md Phase 4).

  Seeds the set with the single algebra identity that currently exists in
  `Rv64/ByteOps.lean`:

    extractByte_replaceByte_same
      : extractByte (replaceByte w pos.val b) pos.val = b

  Future siblings (`extractByte_replaceByte_diff` for `pos₁ ≠ pos₂`,
  `replaceByte_replaceByte_same` idempotency, byte-index arithmetic,
  `extractByte` of concrete word literals) land as one-line
  `@[byte_alg, grind =]` facts in this file as they are proved.

  The `byte_alg` tactic macro wraps `first | grind | simp only [byte_alg]`,
  matching the `divmod_addr` / `rv64_addr` / `reg_ops` pattern.
-/

import EvmAsm.Rv64.ByteOps
import EvmAsm.Rv64.ByteAlgAttr

namespace EvmAsm.Rv64

-- ============================================================================
-- Existing byte algebra lemmas — register in the `byte_alg` simp / grind sets
-- ============================================================================

attribute [byte_alg, grind =] extractByte_replaceByte_same

-- ============================================================================
-- `byte_alg` tactic
--
-- Primary: `grind` (sees every `@[grind =]`-registered byte-algebra fact).
-- Fallback: `simp only [byte_alg]` (matches the same vocabulary under the
-- named attribute; useful when the consumer wants a tight rewrite without
-- grind's congruence closure).
-- ============================================================================

/-- Close a byte-algebra equality (`extractByte`/`replaceByte` commute/cancel
    identities). Tries `grind` first, falls back to
    `simp only [byte_alg]`. -/
macro "byte_alg" : tactic =>
  `(tactic| first
    | grind
    | simp only [byte_alg])

end EvmAsm.Rv64

-- ============================================================================
-- Sanity: the tactic closes the seeded identity.
-- ============================================================================

section Sanity
open EvmAsm.Rv64

example (w : Word) (pos : Fin 8) (b : BitVec 8) :
    extractByte (replaceByte w pos.val b) pos.val = b := by byte_alg
end Sanity
