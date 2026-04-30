/-
  EvmAsm.Evm64.DivMod.Compose.SharedLoopPost

  Issue #266 slice 2 — naming the shared intermediate assertion at the
  DIV/MOD divergence point.

  The DIV (`divCode`) and MOD (`modCode`) programs are byte-identical for the
  first ten blocks (PhaseA … denorm) and only differ in block 10, the
  epilogue:

    * `divCode` uses `divK_div_epilogue 24` — loads `q[]` to the output buffer.
    * `modCode` uses `divK_mod_epilogue 24` — loads the denormalized
      remainder `u'[]` to the output buffer.

  Both epilogues start at `base + epilogueOff = base + 1008`. Slice 1's
  survey (`docs/divmod-shared-loop-divergence.md`) found that the post-state
  of the (shared) denorm body at this PC is byte-for-byte identical between
  the two programs. This file gives that post-state a name,
  `denormDoneSharedPre`, plus the standard `_unfold` lemma and `PCFree`
  instance.

  Subsequent slices (#266 slice 3, slice 4) will use this name to factor a
  shared preloop+loop+denorm spec on `sharedDivModCode`, then compose it
  separately with the DIV and MOD epilogues to produce the final
  `denormDivPost` / `denormModPost` postconditions.

  This file is naming-only: it does not refactor any existing proof. The
  only consumer wiring it provides is the equality lemma showing the
  current inline post-state of `divK_denorm_body_spec_within` (augmented
  with the unchanged `x10`, `q[]`, and `m[]` chunks) equals
  `denormDoneSharedPre`.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Shared intermediate assertion at the DIV/MOD divergence PC
-- (base + epilogueOff = base + 1008)
-- ============================================================================

/-- Post-state at `base + epilogueOff` (the unique DIV/MOD divergence PC).

This is the pre-state consumed by both DIV's and MOD's epilogue:

* registers `x12 / x5 / x7 / x6 / x2 / x0 / x10` carrying `sp`, `u3'`,
  `u3 <<< (antiShift % 64)`, `shift`, `antiShift`, `0`, and `v10`;
* the denormalized remainder `u'[0..3]` at `sp + 4056 / 4048 / 4040 / 4032`;
* the (unchanged) quotient buffer `q[0..3]` at
  `sp + 4088 / 4080 / 4072 / 4064`;
* the (unchanged) output-buffer cells at `sp + 32 / 40 / 48 / 56`.

The primed `u'[]` values are the same denormalized chunks computed by
`divK_denorm_body_spec_within`. The `q[]` and `m[]` cells are inert frame.

The DIV epilogue overwrites `m[]` from `q[]`; the MOD epilogue overwrites
`m[]` from `u'[]`. Both share this exact pre-state. -/
@[irreducible]
def denormDoneSharedPre
    (sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10 : Word) : Assertion :=
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
  let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
  let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
  let u3' := u3 >>> (shift.toNat % 64)
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u3') ** (.x7 ↦ᵣ (u3 <<< (antiShift.toNat % 64))) **
  (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x10 ↦ᵣ v10) **
  ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
  ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
  ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
  ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
  ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
  ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24)

/-- Unfold lemma exposing the raw atoms of `denormDoneSharedPre`. Use this
to bridge between the named assertion and an inline atom chain inside an
`xperm_hyp` / `xperm` step. -/
theorem denormDoneSharedPre_unfold
    {sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10 : Word} :
    denormDoneSharedPre sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10 =
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u0' := (u0 >>> (shift.toNat % 64)) ||| (u1 <<< (antiShift.toNat % 64))
    let u1' := (u1 >>> (shift.toNat % 64)) ||| (u2 <<< (antiShift.toNat % 64))
    let u2' := (u2 >>> (shift.toNat % 64)) ||| (u3 <<< (antiShift.toNat % 64))
    let u3' := u3 >>> (shift.toNat % 64)
    (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ u3') ** (.x7 ↦ᵣ (u3 <<< (antiShift.toNat % 64))) **
    (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ antiShift) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x10 ↦ᵣ v10) **
    ((sp + signExtend12 4056) ↦ₘ u0') ** ((sp + signExtend12 4048) ↦ₘ u1') **
    ((sp + signExtend12 4040) ↦ₘ u2') ** ((sp + signExtend12 4032) ↦ₘ u3') **
    ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
    ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
    ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
    ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24) := by
  delta denormDoneSharedPre; rfl

/-- `denormDoneSharedPre` is pc-free: all its atoms are `regIs` / `memIs`. -/
theorem pcFree_denormDoneSharedPre
    {sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10 : Word} :
    (denormDoneSharedPre sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10).pcFree := by
  rw [denormDoneSharedPre_unfold]; pcFree

instance pcFreeInst_denormDoneSharedPre
    (sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10 : Word) :
    Assertion.PCFree
      (denormDoneSharedPre sp shift u0 u1 u2 u3 q0 q1 q2 q3 m0 m8 m16 m24 v10) :=
  ⟨pcFree_denormDoneSharedPre⟩

end EvmAsm.Evm64
