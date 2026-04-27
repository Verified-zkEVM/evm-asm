/-
  EvmAsm.Evm64.EvmWordArith.Div128NoWrapDischarge

  Discharge bridge: prove `Div128AllPhasesNoWrapInv` (or its weaker
  `Div128PhaseNoWrapInv` cousin) from algorithmic runtime conditions
  (`isSkipBorrowN4Call`, `isAddbackBorrowN4Call`, etc.).

  This is approach (a) from the n4CallAddbackBeq closure plan: prove
  the no-wrap invariant via Phase-1-level reasoning, which then makes
  KB-6d unconditional and unblocks the addback-BEQ semantic predicate.

  **Background**: a numerical counterexample
  (`memory/project_n4calladdbackbeq_counterexample.md`) shows that
  approach (b) — direct val256-level Knuth-B without Phase-1 reasoning —
  is impossible. Phase-1 reasoning is the only viable path.

  **Irreducible bundles** (per `feedback_bundle_pre_post_no_lets`):
  the CLZ-shifted Word inputs and Phase 1b output `rhat'` are bundled
  into `@[irreducible]` defs so the lemma signatures don't expose deep
  let-chains.

  - **`n4ClzShift`**, **`n4ClzAntiShift`**: shift / antiShift Nats.
  - **`n4U4`**, **`n4Un3`**, **`n4B3Prime`**: CLZ-normalized top limbs
    of a, b (computed from a2, a3, b2, b3).
  - **`algorithmRhatPrime`**: Phase 1b's corrected remainder.

  These compose with the existing `algorithmUn21`, `algorithmQ1Prime`,
  `algorithmQ0Prime` (in `CallSkipLowerBoundV2/Algorithm.lean`).

  **Decomposition** (planned):
  - **D1c**: Phase 1 tight (`q1' = q_top_phase1`) under skip-borrow.
  - **D2/D3**: From q1' = q_top_phase1, derive Phase 1 no-wrap
    inequality.
  - **D2b**: From Phase 1 no-wrap + tight q1', derive un21 < vTop.
  - **D5** (parent): compose into `Div128PhaseNoWrapInv`.

  Each sub-stub is a `sorry`'d theorem with a proof sketch in its
  docstring. Estimated ~300-500 LOC total over multiple iterations.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.EvmWordArith.Div128CallSkipClose

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)
open EvmWord (val256)

-- ============================================================================
-- Irreducible bundles for CLZ-normalized inputs
-- ============================================================================

/-- CLZ shift (mod 64) for a divisor's top limb. -/
@[irreducible]
def n4ClzShift (b3 : Word) : Nat := (clzResult b3).1.toNat % 64

/-- CLZ anti-shift (mod 64). -/
@[irreducible]
def n4ClzAntiShift (b3 : Word) : Nat :=
  (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64

/-- CLZ-normalized top limb of `a` (top 64 bits of `a` after shift). -/
@[irreducible]
def n4U4 (a3 b3 : Word) : Word := a3 >>> n4ClzAntiShift b3

/-- CLZ-normalized second-from-top limb of `a` (combines a3 and a2). -/
@[irreducible]
def n4Un3 (a2 a3 b3 : Word) : Word :=
  (a3 <<< n4ClzShift b3) ||| (a2 >>> n4ClzAntiShift b3)

/-- CLZ-normalized top limb of `b` (combines b3 and b2). -/
@[irreducible]
def n4B3Prime (b2 b3 : Word) : Word :=
  (b3 <<< n4ClzShift b3) ||| (b2 >>> n4ClzAntiShift b3)

theorem n4ClzShift_unfold (b3 : Word) :
    n4ClzShift b3 = (clzResult b3).1.toNat % 64 := by
  delta n4ClzShift; rfl

theorem n4ClzAntiShift_unfold (b3 : Word) :
    n4ClzAntiShift b3 =
      (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64 := by
  delta n4ClzAntiShift; rfl

theorem n4U4_unfold (a3 b3 : Word) :
    n4U4 a3 b3 = a3 >>> n4ClzAntiShift b3 := by
  delta n4U4; rfl

theorem n4Un3_unfold (a2 a3 b3 : Word) :
    n4Un3 a2 a3 b3 = (a3 <<< n4ClzShift b3) ||| (a2 >>> n4ClzAntiShift b3) := by
  delta n4Un3; rfl

theorem n4B3Prime_unfold (b2 b3 : Word) :
    n4B3Prime b2 b3 = (b3 <<< n4ClzShift b3) ||| (b2 >>> n4ClzAntiShift b3) := by
  delta n4B3Prime; rfl

/-- Top half of the CLZ-normalized divisor (32-bit divisor for Phase 1). -/
@[irreducible]
def n4DHi (b2 b3 : Word) : Word :=
  n4B3Prime b2 b3 >>> (32 : BitVec 6).toNat

/-- Bottom half of the CLZ-normalized divisor (low 32 bits). -/
@[irreducible]
def n4DLo (b2 b3 : Word) : Word :=
  (n4B3Prime b2 b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

/-- Top 32 bits of `un3` (used as `div_un1` in the algorithm). -/
@[irreducible]
def n4DivUn1 (a2 a3 b3 : Word) : Word :=
  n4Un3 a2 a3 b3 >>> (32 : BitVec 6).toNat

/-- Bottom 32 bits of `un3` (used as `div_un0`). -/
@[irreducible]
def n4DivUn0 (a2 a3 b3 : Word) : Word :=
  (n4Un3 a2 a3 b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat

theorem n4DHi_unfold (b2 b3 : Word) :
    n4DHi b2 b3 = n4B3Prime b2 b3 >>> (32 : BitVec 6).toNat := by
  delta n4DHi; rfl

theorem n4DLo_unfold (b2 b3 : Word) :
    n4DLo b2 b3 = (n4B3Prime b2 b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat := by
  delta n4DLo; rfl

theorem n4DivUn1_unfold (a2 a3 b3 : Word) :
    n4DivUn1 a2 a3 b3 = n4Un3 a2 a3 b3 >>> (32 : BitVec 6).toNat := by
  delta n4DivUn1; rfl

theorem n4DivUn0_unfold (a2 a3 b3 : Word) :
    n4DivUn0 a2 a3 b3 = (n4Un3 a2 a3 b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat := by
  delta n4DivUn0; rfl

/-- **Bundled n=4 algorithm Q1' output** at the (a, b)-limb level.
    Composes the CLZ-normalized inputs with `algorithmQ1Prime`. -/
@[irreducible]
def n4Q1Prime (a2 a3 b2 b3 : Word) : Word :=
  algorithmQ1Prime (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3)

theorem n4Q1Prime_unfold (a2 a3 b2 b3 : Word) :
    n4Q1Prime a2 a3 b2 b3 =
      algorithmQ1Prime (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3) := by
  delta n4Q1Prime; rfl

/-- **Bundled n=4 algorithm un21 output** at the (a, b)-limb level. -/
@[irreducible]
def n4Un21 (a2 a3 b2 b3 : Word) : Word :=
  algorithmUn21 (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3)

theorem n4Un21_unfold (a2 a3 b2 b3 : Word) :
    n4Un21 a2 a3 b2 b3 =
      algorithmUn21 (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3) := by
  delta n4Un21; rfl

/-- **Phase 1 abstract first digit** at the (a, b)-limb level (Nat).
    `q_top_phase1 := (u4 * 2^32 + div_un1) / b3'`. Matches the
    denominator in `algorithmQ1Prime_ge_q_true_1`'s lower bound.
    This is the Nat-level target that `n4Q1Prime` should equal
    under skip-borrow (D1c). -/
@[irreducible]
def n4QTopPhase1 (a2 a3 b2 b3 : Word) : Nat :=
  ((n4U4 a3 b3).toNat * 2^32 + (n4DivUn1 a2 a3 b3).toNat) /
    (n4B3Prime b2 b3).toNat

theorem n4QTopPhase1_unfold (a2 a3 b2 b3 : Word) :
    n4QTopPhase1 a2 a3 b2 b3 =
      ((n4U4 a3 b3).toNat * 2^32 + (n4DivUn1 a2 a3 b3).toNat) /
        (n4B3Prime b2 b3).toNat := by
  delta n4QTopPhase1; rfl

/-- Phase 1b corrected remainder `rhat'` (paired with `algorithmQ1Prime`). -/
@[irreducible]
def algorithmRhatPrime (u4 u3 b3' : Word) : Word :=
  let dHi := b3' >>> (32 : BitVec 6).toNat
  let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := u3 >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu u4 dHi
  let rhat := u4 - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
  if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc

theorem algorithmRhatPrime_unfold (u4 u3 b3' : Word) :
    algorithmRhatPrime u4 u3 b3' =
      (let dHi := b3' >>> (32 : BitVec 6).toNat
       let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
       let div_un1 := u3 >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu u4 dHi
       let rhat := u4 - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) := by
  delta algorithmRhatPrime; rfl

/-- **Bundled n=4 Phase 1b corrected rhat'** at the (a, b)-limb level. -/
@[irreducible]
def n4RhatPrime (a2 a3 b2 b3 : Word) : Word :=
  algorithmRhatPrime (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3)

theorem n4RhatPrime_unfold (a2 a3 b2 b3 : Word) :
    n4RhatPrime a2 a3 b2 b3 =
      algorithmRhatPrime (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3) := by
  delta n4RhatPrime; rfl

-- ============================================================================
-- D1c: Phase 1 tight under skip-borrow (the key structural lemma)
--
-- Decomposed into three sub-stubs (A, B, C) and a composition.
-- ============================================================================

/-- **D1c-A (STUB)**: Phase 1 upper bound under skip-borrow, wrapped on
    bundles. Repackages `div128Quot_q1_prime_le_q_true_top_call_skip` so
    the LHS is `(n4Q1Prime …).toNat` (matching our irreducible bundles).

    **Proof sketch**: apply
    `div128Quot_q1_prime_le_q_true_top_call_skip`, then bridge the
    let-form `q1'` in the conclusion to `algorithmQ1Prime` via
    `algorithmQ1Prime_unfold` and finally to `n4Q1Prime` via
    `n4Q1Prime_unfold`.

    Estimated: ~15 LOC. -/
theorem n4Q1Prime_le_q_true_top_of_skip_borrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    (n4Q1Prime a2 a3 b2 b3).toNat ≤
      (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) / 2^32 := by
  have h := div128Quot_q1_prime_le_q_true_top_call_skip a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall hborrow
  simp only [] at h
  rw [n4Q1Prime_unfold, n4U4_unfold, n4Un3_unfold, n4B3Prime_unfold,
      n4ClzShift_unfold, n4ClzAntiShift_unfold, algorithmQ1Prime_unfold]
  exact h

/-- **D1c-B (STUB)**: Knuth Theorem A at the val256 level — the
    *trial digit* using truncated dividend (u4*2^32 + div_un1) and
    full divisor b3' is at least the true high digit q_true_1.

    Statement: `(val256(a) / val256(b)) / 2^32 ≤ q_top_phase1`
    where `q_top_phase1 = (u4*2^32 + div_un1) / b3'` and
    `(u4, div_un1, b3')` are the CLZ-normalized top portions.

    **Proof sketch**: standard Nat-division monotonicity argument
    bridging val256-level to limb-level. Under CLZ shift, the
    quotient is preserved (shift is a multiplication of both
    numerator and denominator by `2^antiShift`). Then:
    `q_true_full = N / D ≤ (N / 2^128) / b3'` where N/2^128 = u4*2^32
    + div_un1 (the top 96 bits) + 1 (slop). This requires careful
    bounds and the b3' ≥ 2^63 hypothesis from CLZ normalization.

    This is the genuinely new content of D1c — no existing lemma
    captures it.

    Estimated: ~80-100 LOC. -/
theorem q_true_top_le_n4QTopPhase1
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0) :
    (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) / 2^32 ≤
      n4QTopPhase1 a2 a3 b2 b3 := by
  sorry

/-- **D1c-C (STUB)**: Phase 1 lower bound, wrapped on bundles.
    Repackages `algorithmQ1Prime_ge_q_true_1` so the inequality is
    expressed in our bundle vocabulary.

    The original lemma's hypotheses are dHi-domain bounds and
    `u4 < dHi*2^32` (narrow_u4). For the call+skip path under
    `hcall = isCallTrialN4`, narrow_u4 holds because hcall implies
    u4 < b3' ≤ dHi*2^32 + dLo, but the dHi-only form requires
    additional refinement via Phase 1b reasoning. We may need to
    use the CompensationCases-flavored variant instead.

    Estimated: ~15 LOC (mostly bundle bridging). -/
theorem n4Q1Prime_ge_n4QTopPhase1_of_call
    (a2 a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    n4QTopPhase1 a2 a3 b2 b3 ≤ (n4Q1Prime a2 a3 b2 b3).toNat := by
  rw [n4QTopPhase1_unfold, n4Q1Prime_unfold, n4DivUn1_unfold]
  -- Preconditions for the case-split.
  have h_b3'_ge : (n4B3Prime b2 b3).toNat ≥ 2^63 := by
    rw [n4B3Prime_unfold, n4ClzShift_unfold, n4ClzAntiShift_unfold]
    exact b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_u4_lt_b3' : (n4U4 a3 b3).toNat < (n4B3Prime b2 b3).toNat := by
    rw [n4U4_unfold, n4B3Prime_unfold, n4ClzShift_unfold, n4ClzAntiShift_unfold]
    exact isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 : (n4U4 a3 b3).toNat < 2^63 := by
    rw [n4U4_unfold, n4ClzAntiShift_unfold]
    exact u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  -- dHi / dLo decomposition of b3'.
  have h_dHi_ge : ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
    have : (n4B3Prime b2 b3).toNat ≥ 2^63 := h_b3'_ge; omega
  have h_dHi_lt : ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
    have : (n4B3Prime b2 b3).toNat < 2^64 := (n4B3Prime b2 b3).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt :
      (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
    have : ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : (n4B3Prime b2 b3).toNat =
      ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp _
  have h_u4_lt_vTop : (n4U4 a3 b3).toNat <
      ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]; exact h_u4_lt_b3'
  -- Case-split on u4 < dHi*2^32.
  by_cases hu4_lt :
      (n4U4 a3 b3).toNat < ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat).toNat * 2^32
  · have h := algorithmQ1Prime_ge_q_true_1 (n4U4 a3 b3) (n4Un3 a2 a3 b3)
      (n4B3Prime b2 b3)
      h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt h_u4_lt_vTop
    rw [← h_v_eq] at h; exact h
  · exact algorithmQ1Prime_ge_q_true_1_in_wide_u4 (n4U4 a3 b3) (n4Un3 a2 a3 b3)
      (n4B3Prime b2 b3) h_b3'_ge h_u4_lt_b3' (by omega) h_u4_lt_pow63

/-- **D1c (COMPOSED)**: Under `isSkipBorrowN4Call`, Phase 1 trial is
    tight: `q1' = q_top_phase1` (= `(u4 * 2^32 + div_un1) / b3'`).

    **Composition**: D1c-A (q1' ≤ q_true_top) + D1c-B
    (q_true_top ≤ q_top_phase1) gives q1' ≤ q_top_phase1. Combined
    with D1c-C (q_top_phase1 ≤ q1') and `Nat.le_antisymm`. -/
theorem div128Quot_q1_prime_eq_q_top_phase1_of_skip_borrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    (n4Q1Prime a2 a3 b2 b3).toNat = n4QTopPhase1 a2 a3 b2 b3 := by
  have h_le_top := n4Q1Prime_le_q_true_top_of_skip_borrow a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall hborrow
  have h_top_le := q_true_top_le_n4QTopPhase1 a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz
  have h_le : (n4Q1Prime a2 a3 b2 b3).toNat ≤ n4QTopPhase1 a2 a3 b2 b3 :=
    h_le_top.trans h_top_le
  have h_ge := n4Q1Prime_ge_n4QTopPhase1_of_call a2 a3 b2 b3
    hb3nz hshift_nz hcall
  exact Nat.le_antisymm h_le h_ge

-- ============================================================================
-- D2/D3: Phase 1 no-wrap from tight Phase 1
-- ============================================================================

/-- **D2/D3 (STUB)**: From `q1' = q_top_phase1`, derive Phase 1 no-wrap
    `q1' * dLo ≤ (rhat'%2^32)*2^32 + div_un1`.

    **Proof sketch**: From `q1' = (u4*2^32 + div_un1)/dHi`, get
    `q1' * dHi ≤ u4*2^32 + div_un1 < (q1'+1)*dHi`, hence
    `q1' * dHi*2^32 ≤ u4*2^64 + div_un1*2^32`. Multiply Phase 1
    Euclidean by 2^32 and rearrange to get the no-wrap inequality.

    Estimated: ~50 LOC. -/
theorem div128Quot_phase1_no_wrap_of_q1_prime_eq_q_top_phase1
    (a2 a3 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_h_q1_eq : (n4Q1Prime a2 a3 b2 b3).toNat = n4QTopPhase1 a2 a3 b2 b3) :
    (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat ≤
      ((n4RhatPrime a2 a3 b2 b3).toNat % 2^32) * 2^32 +
        (n4DivUn1 a2 a3 b3).toNat := by
  sorry

-- ============================================================================
-- D2b: un21 < vTop from tight Phase 1
-- ============================================================================

/-- **D2b (STUB)**: Under `q1' = q_top_phase1` AND Phase 1 no-wrap,
    derive `un21.toNat < vTop.toNat` (= `dHi.toNat * 2^32 + dLo.toNat`).

    **Proof sketch**: From the no-wrap form (D2/D3), the BitVec
    subtraction doesn't wrap, so
    `un21.toNat = (rhat'%2^32)*2^32 + div_un1 - q1'*dLo`. Combined with
    KB-3m's additive identity (which holds under no-wrap), gives
    `un21 + r1*2^64 + q1'*vTop = uHi*2^32 + div_un1`. Under
    `q1' = q_top_phase1 = (uHi*2^32 + div_un1)/vTop`:
    `q1' * vTop ≤ uHi*2^32 + div_un1 < (q1'+1)*vTop`,
    so `un21 + r1*2^64 < vTop`, hence `un21 < vTop` (with r1 ≥ 0).

    Estimated: ~40 LOC. -/
theorem div128Quot_un21_lt_vTop_from_phase1_tight
    (a2 a3 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_h_q1_eq : (n4Q1Prime a2 a3 b2 b3).toNat = n4QTopPhase1 a2 a3 b2 b3)
    (_h_no_wrap_phase1 :
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat ≤
        ((n4RhatPrime a2 a3 b2 b3).toNat % 2^32) * 2^32 +
          (n4DivUn1 a2 a3 b3).toNat) :
    (n4Un21 a2 a3 b2 b3).toNat <
      (n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat := by
  sorry

-- ============================================================================
-- D5: Compose into Div128PhaseNoWrapInv
-- ============================================================================

/-- **D5 (STUB)**: Skip-borrow implies `Div128PhaseNoWrapInv`.

    Composes D1c (Phase 1 tight) → D2/D3 (Phase 1 no-wrap) → D2b
    (un21 < vTop). This is the core bridge for the call+skip path.

    For the call+addback path, similar reasoning via
    `isAddbackBorrowN4Call` instead of skip-borrow — the analogous
    Phase 1 tight lemma needs to be developed (D1c-addback variant). -/
theorem div128_phase_no_wrap_of_skip_borrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    Div128PhaseNoWrapInv (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3) := by
  sorry

end EvmAsm.Evm64
