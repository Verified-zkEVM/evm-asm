/-
  EvmAsm.Rv64.RLP.Phase2Short

  EL.3 Phase 2 (short form): extract the payload length from an RLP prefix
  byte when the prefix encodes a short byte string (`0x80..0xB7`) or a short
  list (`0xC0..0xF7`).

  For both short categories the length is a simple subtraction:
    * short byte string: `length = prefix - 0x80`, range `[0, 55]`
    * short list:        `length = prefix - 0xC0`, range `[0, 55]`

  Both fit in a single `ADDI x11, x5, -k` instruction, where `k` is the
  category threshold (`0x80` or `0xC0`) encoded as a 12-bit negated
  immediate. The long form (length-of-length loop) is deferred to a
  separate file.

  Register usage:
    x5  — input: the RLP prefix byte (preserved)
    x11 — output: payload length (zero-extended)
-/

import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Program definition
-- ============================================================================

/-- One-instruction short-form length extractor: `ADDI x11, x5, -k`.

    For the two RLP short categories, instantiate with:
    * `k = 0x80` for short byte strings (threshold at exit `e2` of Phase 1)
    * `k = 0xC0` for short lists (threshold at exit `e4` of Phase 1) -/
def rlp_phase2_short_length_prog (k : BitVec 12) : Program :=
  [.ADDI .x11 .x5 (-k)]

example (k : BitVec 12) : (rlp_phase2_short_length_prog k).length = 1 := rfl

/-! ## Concrete sanity checks -/

-- Short byte string with prefix 0x85 (5-byte payload): length = 5.
example : ((0x85 : Word) + signExtend12 (-(0x80 : BitVec 12))) = (5 : Word) := by decide

-- Short byte string with prefix 0xB7 (55-byte payload): length = 55.
example : ((0xB7 : Word) + signExtend12 (-(0x80 : BitVec 12))) = (55 : Word) := by decide

-- Short list with prefix 0xC3 (3-byte payload): length = 3.
example : ((0xC3 : Word) + signExtend12 (-(0xC0 : BitVec 12))) = (3 : Word) := by decide

-- Empty short byte string (prefix = 0x80): length = 0.
example : ((0x80 : Word) + signExtend12 (-(0x80 : BitVec 12))) = (0 : Word) := by decide

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled postcondition: preserve `x5`, write `length = v5 - signExtend12 k`
    into `x11`. Wrapped `@[irreducible]` so the `let length := …` body stays
    out of the theorem signature (AGENTS.md "Bundling Postconditions with
    `let` Bindings"). -/
@[irreducible]
def rlp_phase2_short_length_post
    (v5 : Word) (k : BitVec 12) : Assertion :=
  let length := v5 + signExtend12 (-k)
  (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ length)

theorem rlp_phase2_short_length_post_unfold {v5 : Word} {k : BitVec 12} :
    rlp_phase2_short_length_post v5 k =
    ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ (v5 + signExtend12 (-k)))) := by
  delta rlp_phase2_short_length_post; rfl

/-- `cpsTriple` spec for the short-form length extractor. Given the prefix
    byte in `x5` and arbitrary old value in `x11`, the program writes
    `v5 - k` (via `signExtend12 (-k)`) into `x11` and leaves `x5` unchanged.

    The spec places no range constraint on `v5`; if the caller reaches this
    program outside a short category, the result is still well-defined
    (just not interpretable as a payload length). Downstream consumers
    typically compose this with a preceding Phase 1 exit post so that
    `v5 ∈ [k, k + 55]` is available and the subtraction lands in `[0, 55]`. -/
theorem rlp_phase2_short_length_spec (v5 v11Old : Word)
    (k : BitVec 12) (base : Word) :
    cpsTriple base (base + 4)
      (CodeReq.ofProg base (rlp_phase2_short_length_prog k))
      ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11Old))
      (rlp_phase2_short_length_post v5 k) := by
  simp only [rlp_phase2_short_length_post_unfold]
  -- The one-instruction `ofProg` reduces to a singleton CodeReq.
  rw [show CodeReq.ofProg base (rlp_phase2_short_length_prog k) =
      CodeReq.singleton base (.ADDI .x11 .x5 (-k)) from CodeReq.ofProg_singleton]
  exact addi_spec_gen .x11 .x5 v11Old v5 (-k) base (by nofun)

end EvmAsm.Rv64.RLP
