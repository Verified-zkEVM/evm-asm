/-
  EvmAsm.Rv64.RLP.Phase2LongLoopBody

  EL.3 Phase 2 (long form) — full loop body with back-branch.

  Extends the 5-instruction iteration body with a `BNE x14, x0, back`
  tail:

      LBU  x12, x13, 0        ; byte = mem[x13]
      SLLI x11, x11, 8        ; length <<= 8
      ADD  x11, x11, x12      ; length += byte
      ADDI x13, x13, 1        ; ptr += 1
      ADDI x14, x14, -1       ; counter -= 1
      BNE  x14, x0, back      ; if counter != 0, loop back

  The `back` offset is a parameter; the caller chooses it so the taken
  branch lands at the loop header.

  The spec is a `cpsBranchWithin` at the loop-body entry:
    * taken      → PC = `(base + 20) + signExtend13 back`,  ⌜cnt' ≠ 0⌝
    * not taken  → PC = `base + 24`,                        ⌜cnt' = 0⌝
  where `cnt' = cnt + signExtend12 (-1 : BitVec 12)`.

  Full loop closure (invariant over iterations) is a follow-up; this
  file provides the per-iteration `cpsBranchWithin` that that closure will
  unfold.
-/

import EvmAsm.Rv64.RLP.Phase2LongIter

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Program definition
-- ============================================================================

/-- Six-instruction loop body: the iteration body of `Phase2LongIter`
    followed by `BNE x14, x0, back`. -/
def rlp_phase2_long_loop_body_prog (back : BitVec 13) : Program :=
  [.LBU .x12 .x13 0, .SLLI .x11 .x11 8, .ADD .x11 .x11 .x12,
   .ADDI .x13 .x13 1, .ADDI .x14 .x14 (-1), .BNE .x14 .x0 back]

example (back : BitVec 13) :
    (rlp_phase2_long_loop_body_prog back).length = 6 := rfl

-- ============================================================================
-- Spec
-- ============================================================================

/-- Bundled post for either exit of the loop body: registers updated as
    per one iteration, plus a caller-supplied pure dispatch fact `P`
    (typically `cnt' ≠ 0` for the loop-back exit or `cnt' = 0` for the
    fall-through exit). -/
@[irreducible]
def rlp_phase2_long_loop_body_post
    (len ptr cnt byteZext wordVal dwordAddr : Word) (P : Prop) : Assertion :=
  let length' := (len <<< 8) + byteZext
  let ptr'    := ptr + 1
  let cnt'    := cnt + signExtend12 (-1 : BitVec 12)
  (.x11 ↦ᵣ length') ** (.x13 ↦ᵣ ptr') ** (.x14 ↦ᵣ cnt') **
    (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
    (dwordAddr ↦ₘ wordVal) ** ⌜P⌝

theorem rlp_phase2_long_loop_body_post_unfold
    (len ptr cnt byteZext wordVal dwordAddr : Word) (P : Prop) :
    rlp_phase2_long_loop_body_post len ptr cnt byteZext wordVal dwordAddr P =
    ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
     (.x13 ↦ᵣ (ptr + 1)) **
     (.x14 ↦ᵣ (cnt + signExtend12 (-1 : BitVec 12))) **
     (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
     (dwordAddr ↦ₘ wordVal) ** ⌜P⌝) := by
  delta rlp_phase2_long_loop_body_post; rfl

/-! ## Concrete `cnt' = cnt + signExtend12 (-1)` evaluations

Each per-iteration loop closure (`rlp_phase2_long_loop_*_byte_spec`)
specializes the body spec at a specific counter value `N : Word` and
needs the concrete decremented value `N - 1` to flow through the
post. These eight lemmas package the recurring `(N : Word) +
signExtend12 (-1 : BitVec 12) = (N - 1 : Word) := by decide` boiler.
-/

theorem cnt_dec_1 : (1 : Word) + signExtend12 (-1 : BitVec 12) = (0 : Word) := by decide
theorem cnt_dec_2 : (2 : Word) + signExtend12 (-1 : BitVec 12) = (1 : Word) := by decide
theorem cnt_dec_3 : (3 : Word) + signExtend12 (-1 : BitVec 12) = (2 : Word) := by decide
theorem cnt_dec_4 : (4 : Word) + signExtend12 (-1 : BitVec 12) = (3 : Word) := by decide
theorem cnt_dec_5 : (5 : Word) + signExtend12 (-1 : BitVec 12) = (4 : Word) := by decide
theorem cnt_dec_6 : (6 : Word) + signExtend12 (-1 : BitVec 12) = (5 : Word) := by decide
theorem cnt_dec_7 : (7 : Word) + signExtend12 (-1 : BitVec 12) = (6 : Word) := by decide
theorem cnt_dec_8 : (8 : Word) + signExtend12 (-1 : BitVec 12) = (7 : Word) := by decide

/-- Extract the pure proposition `P` carried by the loop-body post.

    Any caller that has built `rlp_phase2_long_loop_body_post len ptr cnt
    byteZext wordVal dwordAddr P` for some witness `hp` can recover the
    underlying `P` by traversing the six layers of `**` down to the
    trailing `⌜P⌝`. The eight per-iteration loop closures
    (`rlp_phase2_long_loop_*_byte_spec`) all use this to derive `False`
    from the impossible BNE-taken or BNE-ntaken branch. -/
theorem rlp_phase2_long_loop_body_post_pure
    {len ptr cnt byteZext wordVal dwordAddr : Word} {P : Prop} :
    ∀ hp,
      rlp_phase2_long_loop_body_post len ptr cnt byteZext wordVal
        dwordAddr P hp → P := by
  intro hp hpost
  simp only [rlp_phase2_long_loop_body_post_unfold] at hpost
  obtain ⟨_, _, _, _, _, hpost⟩ := hpost
  obtain ⟨_, _, _, _, _, hpost⟩ := hpost
  obtain ⟨_, _, _, _, _, hpost⟩ := hpost
  obtain ⟨_, _, _, _, _, hpost⟩ := hpost
  obtain ⟨_, _, _, _, _, hpost⟩ := hpost
  obtain ⟨_, _, _, _, _, hpost⟩ := hpost
  exact hpost.2

/-- Step-bounded spec for one pass through the long-form length-loop body.

    Composes `rlp_phase2_long_iter_spec_within` (the 5-instruction iteration
    body) with `bne_spec_gen_within` at `base + 20`. The pure dispatch fact
    (`cnt' ≠ 0` on taken, `cnt' = 0` on fall-through) flows directly from
    BNE's postcondition. -/
theorem rlp_phase2_long_loop_body_spec_within
    (len ptr cnt v12Old wordVal dwordAddr : Word)
    (base : Word) (back : BitVec 13)
    (halign : alignToDword ptr = dwordAddr)
    (hvalid : isValidByteAccess ptr = true) :
    let byteZext := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
    let cnt'      := cnt + signExtend12 (-1 : BitVec 12)
    cpsBranchWithin 6 base (CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back))
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((base + 20) + signExtend13 back)
        (rlp_phase2_long_loop_body_post len ptr cnt byteZext wordVal
           dwordAddr (cnt' ≠ 0))
      (base + 24)
        (rlp_phase2_long_loop_body_post len ptr cnt byteZext wordVal
           dwordAddr (cnt' = 0)) := by
  -- The loop-body `ofProg` splits as `ofProg base iter_prog ∪ ofProg (base+20) [BNE]`
  -- via `ofProg_append`; the tail is one singleton plus an `empty`.
  -- The loop-body CodeReq equals the iter CodeReq unioned with the BNE
  -- singleton (plus a trailing `empty` to match `cpsTriple_seq_cpsBranch`'s
  -- output shape). Proved pointwise via funext + case analysis on whether
  -- `a` matches each singleton address.
  have hcr_eq : CodeReq.ofProg base (rlp_phase2_long_loop_body_prog back) =
      (CodeReq.ofProg base rlp_phase2_long_iter_prog).union
      ((CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union
        CodeReq.empty) := by
    funext a
    have e2 : (base + 4 + 4 : Word) = base + 8 := by bv_omega
    have e3 : (base + 8 + 4 : Word) = base + 12 := by bv_omega
    have e4 : (base + 12 + 4 : Word) = base + 16 := by bv_omega
    have e5 : (base + 16 + 4 : Word) = base + 20 := by bv_omega
    simp only [rlp_phase2_long_loop_body_prog, rlp_phase2_long_iter_prog,
      CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union, CodeReq.empty,
      e2, e3, e4, e5, CodeReq.singleton]
    simp only [beq_iff_eq]
    by_cases h0 : a = base
    · simp [h0]
    by_cases h1 : a = base + 4#64
    · simp [h1]
    by_cases h2 : a = base + 8#64
    · simp [h2]
    by_cases h3 : a = base + 12#64
    · simp [h3]
    by_cases h4 : a = base + 16#64
    · simp [h4]
    by_cases h5 : a = base + 20#64
    · simp [h5]
    simp [h0, h1, h2, h3, h4]
  rw [hcr_eq]
  simp only [rlp_phase2_long_loop_body_post_unfold]
  -- Get iter_spec (5 instructions base → base+20).
  have iter := rlp_phase2_long_iter_spec_within len ptr cnt v12Old wordVal dwordAddr
    base halign hvalid
  simp only [rlp_phase2_long_iter_post_unfold] at iter
  set byteZext := (extractByte wordVal (byteOffset ptr)).zeroExtend 64
  set cnt' := cnt + signExtend12 (-1 : BitVec 12)
  -- Frame iter with (.x0 ↦ᵣ 0) so the composition state matches bne's.
  have iter' : cpsTripleWithin 5 base (base + 20)
      (CodeReq.ofProg base rlp_phase2_long_iter_prog)
      ((.x11 ↦ᵣ len) ** (.x13 ↦ᵣ ptr) ** (.x14 ↦ᵣ cnt) **
       (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
       (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
       (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) iter)
  -- BNE x14, x0, back at (base + 20). Taken when x14 ≠ 0, not taken when x14 = 0.
  have bne_raw := bne_spec_gen_within .x14 .x0 back cnt' (0 : Word) (base + 20)
  -- Frame BNE with all the other state (x11, x13, x12, dwordAddr) and
  -- permute to the shape produced by `iter'`'s post.
  have bne_framed : cpsBranchWithin 1 (base + 20)
      (CodeReq.singleton (base + 20) (.BNE .x14 .x0 back))
      ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
       (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
       (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
       (dwordAddr ↦ₘ wordVal))
      ((base + 20) + signExtend13 back)
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
         (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
         (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
         (dwordAddr ↦ₘ wordVal) ** ⌜cnt' ≠ 0⌝)
      (base + 24)
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
         (.x13 ↦ᵣ (ptr + 1)) ** (.x14 ↦ᵣ cnt') **
         (.x12 ↦ᵣ byteZext) ** (.x0 ↦ᵣ (0 : Word)) **
         (dwordAddr ↦ₘ wordVal) ** ⌜cnt' = 0⌝) := by
    have h_eq_20_4 : (base + 20 : Word) + 4 = base + 24 := by bv_omega
    rw [h_eq_20_4] at bne_raw
    exact cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((.x11 ↦ᵣ ((len <<< 8) + byteZext)) **
         (.x13 ↦ᵣ (ptr + 1)) ** (.x12 ↦ᵣ byteZext) **
         (dwordAddr ↦ₘ wordVal)) (by pcFree) bne_raw)
  -- Disjointness between iter CR and BNE-singleton-union-empty CR.
  have hd_iter_bne : (CodeReq.ofProg base rlp_phase2_long_iter_prog).Disjoint
      ((CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union
        CodeReq.empty) := by
    refine CodeReq.Disjoint.union_right ?_ (CodeReq.Disjoint.empty_right _)
    apply CodeReq.Disjoint.ofProg_singleton
    apply CodeReq.ofProg_none_range
    intro k hk
    simp only [rlp_phase2_long_iter_prog, List.length_cons, List.length_nil] at hk
    interval_cases k <;> bv_omega
  -- Extend bne_framed's CR with trailing empty.
  have bne_ext : cpsBranchWithin 1 (base + 20)
      ((CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union CodeReq.empty)
      _ _ _ _ _ :=
    cpsBranchWithin_extend_code
      (fun a _ hcr => by
        show (CodeReq.singleton (base + 20) (.BNE .x14 .x0 back)).union
            CodeReq.empty a = _
        simp only [CodeReq.union, hcr])
      bne_framed
  exact cpsTripleWithin_seq_cpsBranchWithin hd_iter_bne iter' bne_ext

end EvmAsm.Rv64.RLP
