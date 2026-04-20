/-
  EvmAsm.Rv64.RLP.Phase2LongLoopTwo

  EL.3 Phase 2 (long form) — two-iteration closure of the loop body.

  Specializes `rlp_phase2_long_loop_body_spec` (#333) at `x14 = 2`,
  composed with `rlp_phase2_long_loop_one_byte_spec` (#335) for the
  second iteration. The overall execution:

      iter 1 @ base → state at base (taken back via BNE, cnt 2→1)
      iter 2 @ base → state at base + 24 (fall-through, cnt 1→0)

  Produces a `cpsTriple` from `base` to `base + 24` that decodes two
  big-endian bytes. Corresponds to RLP prefixes `0xB9` and `0xF9`
  (`lenLen = 2`).

  Memory model: both bytes (`mem[ptr]`, `mem[ptr + 1]`) are assumed to
  live in the same doubleword at `dwordAddr`. This is captured by two
  `alignToDword` hypotheses. Spans of more than one doubleword would
  require carrying a second memory atom.

  Further closures — arbitrary `n` via induction — are future work.
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopOne

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for the two-iteration loop closure: registers in the
    "two iterations done" state, `x14` now `0`, both bytes folded into
    `x11` in big-endian order. -/
@[irreducible]
def rlp_phase2_long_loop_two_byte_post
    (len ptr byte1 byte2 wordVal dwordAddr : Word) : Assertion :=
  let length' := ((len <<< 8) + byte1) <<< 8 + byte2
  let ptr'    := ptr + 2
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ (0 : Word)) **
    (.x12 ↦ᵣ byte2) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal)

theorem rlp_phase2_long_loop_two_byte_post_unfold
    (len ptr byte1 byte2 wordVal dwordAddr : Word) :
    rlp_phase2_long_loop_two_byte_post len ptr byte1 byte2 wordVal dwordAddr =
    ((.x11 ↦ᵣ (((len <<< 8) + byte1) <<< 8 + byte2)) **
     (.x13 ↦ᵣ (ptr + 2)) **
     (.x14 ↦ᵣ (0 : Word)) **
     (.x12 ↦ᵣ byte2) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal)) := by
  delta rlp_phase2_long_loop_two_byte_post; rfl

/-- `cpsTriple` spec for the two-iteration (lenLen = 2) closure of
    the long-form length loop.

    The first iteration runs the loop body with `cnt = 2`; the
    BNE is taken (`cnt' = 1 ≠ 0`), PC returns to `base`. The second
    iteration then runs with `cnt = 1`, falls through, and lands at
    `base + 24`. -/
theorem rlp_phase2_long_loop_two_byte_spec
    (len ptr v12Old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign1 : alignToDword ptr = dwordAddr)
    (halign2 : alignToDword (ptr + 1) = dwordAddr)
    (hvalid1 : isValidByteAccess ptr = true)
    (hvalid2 : isValidByteAccess (ptr + 1) = true)
    (hback : (base + 20) + signExtend13 back = base) :
    cpsTriple base (base + 24)
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (2 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      (rlp_phase2_long_loop_two_byte_post len ptr
        ((extractByte wordVal (byteOffset ptr)).zeroExtend 64)
        ((extractByte wordVal (byteOffset (ptr + 1))).zeroExtend 64)
        wordVal dwordAddr) := by
  simp only [rlp_phase2_long_loop_two_byte_post_unfold]
  -- Iter 1: loop-body spec at cnt = 2.
  have body := rlp_phase2_long_loop_body_spec len ptr (2 : Word) v12Old
    wordVal dwordAddr base back halign1 hvalid1
  -- cnt' = 2 + signExtend12 (-1) = 1. Rewrite.
  have hcnt' : (2 : Word) + signExtend12 (-1 : BitVec 12) = (1 : Word) := by
    decide
  rw [hcnt'] at body
  -- The fall-through carries `⌜(1 : Word) = 0⌝`, which is False.
  set byte1 := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  have h_absurd : ∀ hp,
      rlp_phase2_long_loop_body_post len ptr (2 : Word) byte1 wordVal
         dwordAddr ((1 : Word) = 0) hp → False := by
    intro hp hpost
    simp only [rlp_phase2_long_loop_body_post_unfold] at hpost
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x11
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x13
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x14
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x12
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel x0
    obtain ⟨_, _, _, _, _, hpost⟩ := hpost -- peel memory
    exact absurd hpost.2 (by decide)
  -- `cpsBranch_elim_taken` drops fall-through. Keeps taken exit (loops back).
  have tri1 := cpsBranch_takenPath body h_absurd
  -- Taken exit is `(base + 20) + signExtend13 back = base` by hback.
  rw [hback] at tri1
  -- Weaken post: unfold wrapper, strip trailing `⌜(1 : Word) ≠ 0⌝` pure fact,
  -- matching the one-byte spec's precondition at `base`.
  have tri1' : cpsTriple base base
      (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ (2 : Word)) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byte1)) ** (.x13 ↦ᵣ (ptr + 1)) **
       (.x14 ↦ᵣ (1 : Word)) ** (.x12 ↦ᵣ byte1) **
       (.x0 ↦ᵣ (0 : Word)) ** (dwordAddr ↦ₘ wordVal)) :=
    cpsTriple_weaken
      (fun _ hp => hp)
      (fun h hp => by
        simp only [rlp_phase2_long_loop_body_post_unfold] at hp
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right ?_)))) h hp
        intro h' hp'
        exact ((sepConj_pure_right _ _ _).1 hp').1)
      tri1
  -- Iter 2: one-byte spec at base, using state from tri1's post.
  -- Permute post to match one-byte spec's pre shape (put x13, x14 first).
  have one_byte := rlp_phase2_long_loop_one_byte_spec ((len <<< 8) + byte1)
    (ptr + 1) byte1 wordVal dwordAddr base back halign2 hvalid2
  simp only [rlp_phase2_long_loop_one_byte_post_unfold] at one_byte
  -- Both CRs are the same (loop body prog at base), so use `_seq_same_cr`.
  -- Need to convert tri1''s post into one_byte's pre shape via consequence.
  have composed :=
    cpsTriple_seq_perm_same_cr
      (fun h hp => by xperm_hyp hp) tri1' one_byte
  -- Final post: rewrite `ptr + 1 + 1 = ptr + 2` and reshape.
  have h_ptr_2 : (ptr + 1 : Word) + 1 = ptr + 2 := by bv_omega
  rw [h_ptr_2] at composed
  exact cpsTriple_weaken
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    composed

end EvmAsm.Rv64.RLP
