/-
  EvmAsm.Rv64.RLP.Phase2LongLoopOne

  EL.3 Phase 2 (long form) — one-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` to the case where the
  initial counter `x14` is `1`. After the single iteration the counter
  decrements to `0`, the `BNE x14, x0, back` falls through, and control
  reaches the exit at `base + 24`. The "loop-back" branch is
  unreachable (its pure fact `cnt' ≠ 0` is `0 ≠ 0`, which is false),
  so the resulting spec is a plain `cpsTriple`.

  This is the simplest concrete closure of the long-form loop: it
  corresponds to RLP long-form prefixes `0xB8` or `0xF8`, where
  `lenLen = 1` and exactly one big-endian byte encodes the payload
  length.

  Further closures — arbitrary `n`-iteration loops via induction on the
  counter — are future work.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopBody

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the single-iteration loop closure: the registers are
    in the "one iteration done" state, `x14` is now `0`, and no dispatch
    fact is needed (the caller knows we exited via fall-through). -/
@[irreducible]
def rlp_phase2_long_loop_one_byte_post
    (len ptr byteZext wordVal dwordAddr : Word) : Assertion :=
  let length' := (len <<< 8) + byteZext
  let ptr'    := ptr + 1
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_loop_one_byte_post_unfold
    (len ptr byteZext wordVal dwordAddr : Word) :
    rlp_phase2_long_loop_one_byte_post len ptr byteZext wordVal dwordAddr =
    ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
     (.x13 ↦ᵣ (ptr + 1)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_loop_one_byte_post; rfl

/-- `cpsTriple` spec for the single-iteration (lenLen = 1) closure of
    the long-form length loop.

    Derived from `rlp_phase2_long_loop_body_spec` by observing that when
    `cnt = 1`, `cnt' = 1 + signExtend12 (-1) = 0`, so the taken-branch
    post `⌜cnt' ≠ 0⌝` collapses to `⌜(0 : Word) ≠ 0⌝ = False`. The
    `cpsBranch_elim_ntaken` rule then turns the two-exit branch into a
    single-exit triple at the fall-through. -/
theorem rlp_phase2_long_loop_one_byte_spec
    (len ptr v12Old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign : alignToDword ptr = dwordAddr)
    (hvalid : isValidByteAccess ptr = true) :
    let byteZext := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (1 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_loop_one_byte_post len ptr byteZext wordVal
         dwordAddr) := by
  simp only [rlp_phase2_long_loop_one_byte_post_unfold]
  -- Body spec instantiated at cnt = 1.
  have body := rlp_phase2_long_loop_body_spec len ptr (1 : Word) v12Old
    wordVal dwordAddr base back halign hvalid
  -- For cnt = 1, `cnt' = (1 : Word) + signExtend12 (-1 : BitVec 12) = 0`.
  have hcnt' : (1 : Word) + signExtend12 (-1 : BitVec 12) = (0 : Word) := by
    decide
  rw [hcnt'] at body
  -- The taken post carries `⌜(0 : Word) ≠ 0⌝`, which is False. Extract it
  -- via six layers of destructuring and derive the contradiction.
  set byteZext := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (1 : Word) byteZext wordVal
         dwordAddr ((0 : Word) ≠ 0) hp → False := by
    intro hp hpost
    simp only [rlp_phase2_long_loop_body_post_unfold] at hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x11
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x13
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x14
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x12
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x0
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel memory
    exact hpost.2 rfl
  -- `cpsBranch_elim_ntaken` drops the taken branch.
  have tri := cpsBranch_ntakenPath body h_absurd
  -- Weaken the post: unfold the `@[irreducible]` wrapper and strip the
  -- trailing `⌜(0 : Word) = 0⌝ = True` pure fact (via 5 `mono_right` wraps
  -- reaching the innermost `F ** ⌜P⌝`).
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by
      simp only [rlp_phase2_long_loop_body_post_unfold] at hp
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right ?_)))) h hp
      intro h' hp'
      exact ((sepConj_pure_right _ _ _).1 hp').1)
    tri

end EvmAsm.Rv64.RLP
