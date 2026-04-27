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
import EvmAsm.Evm64.EvmWordArith.Div128PhaseNoWrap

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
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) / 2^32 ≤
      n4QTopPhase1 a2 a3 b2 b3 := by
  -- Apply existing val256-level ratio bound:
  --   val256(a)/val256(b) ≤ (u4*2^64 + u3) / b3'.
  have h := val256_ratio_le_u_total_div_b3_prime a0 a1 a2 a3 b0 b1 b2 b3
    hshift_nz hb3nz
  simp only [] at h
  -- Set up Nat shorthand: u4n = u4.toNat, u3n = u3.toNat, b3'n = b3'.toNat.
  set u4n :=
    (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)).toNat
    with hu4n_def
  set u3n :=
    ((a3 <<< ((clzResult b3).1.toNat % 64)) |||
      (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat
    with hu3n_def
  set b3'n :=
    ((b3 <<< ((clzResult b3).1.toNat % 64)) |||
      (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat
    with hb3'n_def
  -- Divide both sides of h by 2^32.
  have h_div : (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) / 2^32 ≤
      (u4n * 2^64 + u3n) / b3'n / 2^32 := Nat.div_le_div_right h
  -- Algebraic bridge: (u4n*2^64 + u3n) / b3'n / 2^32 = (u4n*2^32 + u3n/2^32) / b3'n.
  have h_alg : (u4n * 2^64 + u3n) / b3'n / 2^32 =
      (u4n * 2^32 + u3n / 2^32) / b3'n := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm b3'n (2^32),
        ← Nat.div_div_eq_div_mul]
    congr 1
    -- Goal: (u4n * 2^64 + u3n) / 2^32 = u4n * 2^32 + u3n / 2^32.
    have h_rearr : u4n * 2^64 + u3n = u3n + u4n * 2^32 * 2^32 := by ring
    rw [h_rearr, Nat.add_mul_div_right _ _ (by decide : (0:Nat) < 2^32)]
    omega
  rw [h_alg] at h_div
  -- Now goal RHS uses bundles; unfold them and compare.
  rw [n4QTopPhase1_unfold, n4U4_unfold, n4DivUn1_unfold, n4Un3_unfold,
      n4B3Prime_unfold, n4ClzShift_unfold, n4ClzAntiShift_unfold]
  -- Convert (un3 >>> 32).toNat to u3n / 2^32 via BitVec lemmas.
  have h_u3_shift :
      (((a3 <<< ((clzResult b3).1.toNat % 64)) |||
        (a2 >>>
          ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))) >>>
          (32 : BitVec 6).toNat).toNat = u3n / 2^32 := by
    rw [BitVec.toNat_ushiftRight, EvmAsm.Rv64.AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow]
  rw [h_u3_shift]
  exact h_div

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
--
-- Decomposed into D2/D3-A (rhat' < 2^32 sub-stub) and D2/D3 main
-- (composition wrapping `div128Quot_phase1_no_wrap_skip`).
-- ============================================================================

/-- **D2/D3-A (STUB)**: Under `q1' = q_top_phase1`, the algorithm's Phase 1b
    output `rhat'` satisfies `rhat'.toNat < 2^32` — i.e., the Phase 1b
    correction stays within a single limb.

    **Proof sketch (algorithmic)**: rhat' is either rhatc or rhatc + dHi
    after Phase 1b correction. Under tight q1' = q_top_phase1, Phase 1b
    correction either doesn't fire (rhatc < dHi < 2^32 from Knuth Phase 1)
    or fires and rhat' = rhatc + dHi but our specific case excludes the
    rhatc + dHi ≥ 2^32 sub-case via the q1' = q_top_phase1 invariant.

    This is the genuinely hard sub-piece: the relationship between the
    algorithm's BitVec arithmetic and the abstract Knuth invariant.

    Estimated: ~60-80 LOC (case-split on hi1 = 0 / hi1 ≠ 0 and Phase 1b
    fired / not fired, with arithmetic in each branch). -/
theorem n4RhatPrime_lt_pow32_of_q1_prime_eq_q_top_phase1
    (a2 a3 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_h_q1_eq : (n4Q1Prime a2 a3 b2 b3).toNat = n4QTopPhase1 a2 a3 b2 b3) :
    (n4RhatPrime a2 a3 b2 b3).toNat < 2^32 := by
  sorry

/-- **D2/D3 (STUB, with sub-stub D2/D3-A used)**: From `q1' = q_top_phase1`,
    derive Phase 1 no-wrap `q1' * dLo ≤ (rhat'%2^32)*2^32 + div_un1`.

    **Plan**: Compose
    - `div128Quot_phase1_no_wrap_skip` (existing, in `Div128PhaseNoWrap`,
      takes `hq1_prime_le_q_true_1` and `hrhat'_lt` as hypotheses)
    - `n4RhatPrime_lt_pow32_of_q1_prime_eq_q_top_phase1` (D2/D3-A sub-stub)
    - The ≤ side of h_q1_eq (an equality trivially gives ≤)
    - Bundle ↔ let-form bridging via the unfold lemmas.

    The unwrapping/bridging is mechanical (~30 LOC) once the `Div128PhaseNoWrap`
    import is added (current file imports `Div128CallSkipClose`; need to also
    import `Div128PhaseNoWrap`). Deferred to next iteration.

    Estimated: ~30-50 LOC for the bridging once D2/D3-A is closed. -/
theorem div128Quot_phase1_no_wrap_of_q1_prime_eq_q_top_phase1
    (a2 a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (h_q1_eq : (n4Q1Prime a2 a3 b2 b3).toNat = n4QTopPhase1 a2 a3 b2 b3) :
    (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat ≤
      ((n4RhatPrime a2 a3 b2 b3).toNat % 2^32) * 2^32 +
        (n4DivUn1 a2 a3 b3).toNat := by
  -- Derive dHi bounds from b3' ≥ 2^63.
  have h_b3'_ge : (n4B3Prime b2 b3).toNat ≥ 2^63 := by
    rw [n4B3Prime_unfold, n4ClzShift_unfold, n4ClzAntiShift_unfold]
    exact b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_dHi_ge : (n4DHi b2 b3).toNat ≥ 2^31 := by
    rw [n4DHi_unfold]
    exact div128Quot_dHi_ge_pow31 (n4B3Prime b2 b3) h_b3'_ge
  have h_dHi_ne : n4DHi b2 b3 ≠ 0 := by
    intro hzero
    have h0 : (n4DHi b2 b3).toNat = 0 := by rw [hzero]; rfl
    omega
  have h_dHi_lt : (n4DHi b2 b3).toNat < 2^32 := by
    rw [n4DHi_unfold, BitVec.toNat_ushiftRight,
        EvmAsm.Rv64.AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (n4B3Prime b2 b3).toNat < 2^64 := (n4B3Prime b2 b3).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dLo_lt : (n4DLo b2 b3).toNat < 2^32 := by
    rw [n4DLo_unfold, BitVec.toNat_ushiftRight,
        EvmAsm.Rv64.AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : (n4B3Prime b2 b3).toNat =
      (n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat := by
    rw [n4DHi_unfold, n4DLo_unfold]
    exact div128Quot_vTop_decomp _
  -- Discharge rhat' < 2^32 via D2/D3-A.
  have h_rhat'_lt : (n4RhatPrime a2 a3 b2 b3).toNat < 2^32 :=
    n4RhatPrime_lt_pow32_of_q1_prime_eq_q_top_phase1 a2 a3 b2 b3
      hb3nz hshift_nz hcall h_q1_eq
  -- The let-form q1' inside `div128Quot_phase1_no_wrap_skip` matches
  -- algorithmQ1Prime's body when we use dHi = n4DHi, dLo = n4DLo.
  -- And rhat' similarly matches algorithmRhatPrime's body.
  have h_app := div128Quot_phase1_no_wrap_skip
    (n4U4 a3 b3) (n4DHi b2 b3) (n4DLo b2 b3) (n4Un3 a2 a3 b3)
    h_dHi_ne h_dHi_ge h_dHi_lt
    (by
      -- hq1_prime_le_q_true_1: in let-form, q1'.toNat ≤
      -- (uHi*2^32+div_un1)/(dHi*2^32+dLo).
      simp only []
      have h_le : (n4Q1Prime a2 a3 b2 b3).toNat ≤
          ((n4U4 a3 b3).toNat * 2^32 +
            ((n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat).toNat) /
            ((n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat) := by
        rw [h_q1_eq, n4QTopPhase1_unfold, n4DivUn1_unfold, ← h_v_eq]
      -- The let-form q1' in lemma = body computed with our dHi, dLo.
      -- This should equal n4Q1Prime by unfolding algorithmQ1Prime.
      have h_q1_eq_letform :
          (n4Q1Prime a2 a3 b2 b3).toNat =
          (let q1 := rv64_divu (n4U4 a3 b3) (n4DHi b2 b3)
           let rhat := (n4U4 a3 b3) - q1 * (n4DHi b2 b3)
           let hi1 := q1 >>> (32 : BitVec 6).toNat
           let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
           let rhatc : Word := if hi1 = 0 then rhat else rhat + (n4DHi b2 b3)
           let qDlo := q1c * (n4DLo b2 b3)
           let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
           let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
           if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c).toNat := by
        rw [n4Q1Prime_unfold, algorithmQ1Prime_unfold, n4DHi_unfold, n4DLo_unfold]
      rw [← h_q1_eq_letform]
      exact h_le)
    (by
      -- hrhat'_lt: in let-form rhat'.toNat < 2^32.
      simp only []
      have h_rhat_eq_letform :
          (n4RhatPrime a2 a3 b2 b3).toNat =
          (let q1 := rv64_divu (n4U4 a3 b3) (n4DHi b2 b3)
           let rhat := (n4U4 a3 b3) - q1 * (n4DHi b2 b3)
           let hi1 := q1 >>> (32 : BitVec 6).toNat
           let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
           let rhatc : Word := if hi1 = 0 then rhat else rhat + (n4DHi b2 b3)
           let qDlo := q1c * (n4DLo b2 b3)
           let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
           let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
           if BitVec.ult rhatUn1 qDlo then rhatc + (n4DHi b2 b3) else rhatc).toNat := by
        rw [n4RhatPrime_unfold, algorithmRhatPrime_unfold, n4DHi_unfold, n4DLo_unfold]
      rw [← h_rhat_eq_letform]
      exact h_rhat'_lt)
  -- h_app's conclusion uses let-form q1', dLo, rhat', div_un1.
  -- Bridge back to bundles.
  simp only [] at h_app
  have h_q1_letform :
      (let q1 := rv64_divu (n4U4 a3 b3) (n4DHi b2 b3)
       let rhat := (n4U4 a3 b3) - q1 * (n4DHi b2 b3)
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc : Word := if hi1 = 0 then rhat else rhat + (n4DHi b2 b3)
       let qDlo := q1c * (n4DLo b2 b3)
       let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) =
      n4Q1Prime a2 a3 b2 b3 := by
    rw [n4Q1Prime_unfold, algorithmQ1Prime_unfold, n4DHi_unfold, n4DLo_unfold]
  have h_rhat_letform :
      (let q1 := rv64_divu (n4U4 a3 b3) (n4DHi b2 b3)
       let rhat := (n4U4 a3 b3) - q1 * (n4DHi b2 b3)
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc : Word := if hi1 = 0 then rhat else rhat + (n4DHi b2 b3)
       let qDlo := q1c * (n4DLo b2 b3)
       let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then rhatc + (n4DHi b2 b3) else rhatc) =
      n4RhatPrime a2 a3 b2 b3 := by
    rw [n4RhatPrime_unfold, algorithmRhatPrime_unfold, n4DHi_unfold, n4DLo_unfold]
  rw [h_q1_letform, h_rhat_letform] at h_app
  rw [n4DivUn1_unfold]
  exact h_app

-- ============================================================================
-- D2b: un21 < vTop from tight Phase 1
-- ============================================================================

/-- **D2b-A (CLOSED)**: Phase 1b Euclidean identity at bundle level.
    `q1' * dHi + rhat' = u4` (toNat). Wraps `div128Quot_phase1b_post`
    over our irreducible bundles. -/
theorem n4_phase1b_eucl
    (a2 a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3) :
    (n4Q1Prime a2 a3 b2 b3).toNat * (n4DHi b2 b3).toNat +
      (n4RhatPrime a2 a3 b2 b3).toNat = (n4U4 a3 b3).toNat := by
  -- dHi bounds.
  have h_b3'_ge : (n4B3Prime b2 b3).toNat ≥ 2^63 := by
    rw [n4B3Prime_unfold, n4ClzShift_unfold, n4ClzAntiShift_unfold]
    exact b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_dHi_ge : (n4DHi b2 b3).toNat ≥ 2^31 := by
    rw [n4DHi_unfold]; exact div128Quot_dHi_ge_pow31 _ h_b3'_ge
  have h_dHi_ne : n4DHi b2 b3 ≠ 0 := by
    intro hzero
    have h0 : (n4DHi b2 b3).toNat = 0 := by rw [hzero]; rfl
    omega
  have h_dHi_lt : (n4DHi b2 b3).toNat < 2^32 := by
    rw [n4DHi_unfold, BitVec.toNat_ushiftRight,
        EvmAsm.Rv64.AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (n4B3Prime b2 b3).toNat < 2^64 := (n4B3Prime b2 b3).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  -- Phase 1a Euclidean and rhatc bound.
  -- Bridge to n4DHi-based form: rewrite n4Q1Prime, n4RhatPrime to algorithm bodies.
  rw [n4Q1Prime_unfold, n4RhatPrime_unfold, algorithmQ1Prime_unfold,
      algorithmRhatPrime_unfold]
  -- Substitute dHi := b3' >>> 32 to match the let-form's dHi.
  rw [show (n4DHi b2 b3) = (n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat
        from n4DHi_unfold b2 b3]
  -- Now the goal is in let-form. Apply the existing lemma.
  -- Construct the q1c, rhatc, dLo, rhatUn1 args needed.
  set b3' := n4B3Prime b2 b3 with hb3'_def
  set u4 := n4U4 a3 b3 with hu4_def
  set u3 := n4Un3 a2 a3 b3 with hu3_def
  -- Replicate the structure that algorithmQ1Prime_unfold leaves.
  -- After unfolding, the goal references b3' >>> 32, etc.
  -- Use h_post and h_rhatc_lt with dHi := b3' >>> 32.
  have h_dHi_ne' : (b3' >>> (32 : BitVec 6).toNat) ≠ 0 := by
    rw [hb3'_def, ← n4DHi_unfold]; exact h_dHi_ne
  have h_dHi_lt' : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [hb3'_def, ← n4DHi_unfold]; exact h_dHi_lt
  exact div128Quot_phase1b_post u4 (b3' >>> (32 : BitVec 6).toNat)
    (if rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat = 0
     then rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat)
     else rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) + signExtend12 4095)
    (if rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat = 0
     then u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
              (b3' >>> (32 : BitVec 6).toNat)
     else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
              (b3' >>> (32 : BitVec 6).toNat) + (b3' >>> (32 : BitVec 6).toNat))
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)
    (((if rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) >>>
          (32 : BitVec 6).toNat = 0
       then u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
              (b3' >>> (32 : BitVec 6).toNat)
       else u4 - rv64_divu u4 (b3' >>> (32 : BitVec 6).toNat) *
              (b3' >>> (32 : BitVec 6).toNat) +
              (b3' >>> (32 : BitVec 6).toNat)) <<< (32 : BitVec 6).toNat) |||
       (u3 >>> (32 : BitVec 6).toNat))
    h_dHi_lt'
    (div128Quot_first_round_post u4 (b3' >>> (32 : BitVec 6).toNat)
      h_dHi_ne' h_dHi_lt')
    (div128Quot_rhatc_lt_2dHi u4 (b3' >>> (32 : BitVec 6).toNat)
      h_dHi_ne' h_dHi_lt')

/-- **D2b-B (STUB)**: BitVec un21 to Nat decomposition under no-wrap.
    `un21.toNat = (rhat'%2^32)*2^32 + div_un1 - q1'*dLo` when no-wrap.

    **Proof sketch**: `n4Un21 = ((rhat' << 32) ||| div_un1) - (q1' * dLo)`
    (BitVec). Under no-wrap (h_no_wrap_phase1), the BitVec subtraction is
    no-wrap, so `un21.toNat = cu_rhat_un1.toNat - cu_q1_dlo.toNat`.
    `cu_rhat_un1.toNat = (rhat'%2^32)*2^32 + div_un1` via
    `halfword_combine_mod`. `cu_q1_dlo.toNat = q1'*dLo` (no Word overflow,
    since q1' < 2^32 and dLo < 2^32 so product < 2^64).

    **Blocker (2026-04-27 iteration)**: the structural identity
    `n4Un21 = (n4RhatPrime << 32 ||| n4DivUn1) - (n4Q1Prime * n4DLo)`
    triggers `whnf` heartbeat blow-up when proven via combined `_unfold`
    rewrites, due to algorithm let-bindings duplicating large
    if-then-else terms across bundle boundaries. Likely needs a more
    delicate proof structure or restatement of `algorithmUn21` in
    terms of `algorithmQ1Prime` / `algorithmRhatPrime` explicitly. -/
theorem n4Un21_toNat_of_no_wrap
    (a2 a3 b2 b3 : Word)
    (_hb3nz : b3 ≠ 0)
    (_hshift_nz : (clzResult b3).1 ≠ 0)
    (_hcall : isCallTrialN4 a3 b2 b3)
    (_h_no_wrap_phase1 :
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat ≤
        ((n4RhatPrime a2 a3 b2 b3).toNat % 2^32) * 2^32 +
          (n4DivUn1 a2 a3 b3).toNat) :
    (n4Un21 a2 a3 b2 b3).toNat =
      ((n4RhatPrime a2 a3 b2 b3).toNat % 2^32) * 2^32 +
        (n4DivUn1 a2 a3 b3).toNat -
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat := by
  sorry

/-- **D2b (CLOSED via composition mod sub-stubs)**: Under
    `q1' = q_top_phase1` AND Phase 1 no-wrap, derive `un21 < vTop`.

    Composes:
    - **D2b-A** (`n4_phase1b_eucl`): Phase 1b Euclidean.
    - **D2b-B** (`n4Un21_toNat_of_no_wrap`): BitVec un21 in Nat.
    - h_q1_eq + Nat.lt_div_iff_mul_lt: q_top_phase1 strict upper bound.
    - Final arithmetic. -/
theorem div128Quot_un21_lt_vTop_from_phase1_tight
    (a2 a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (h_q1_eq : (n4Q1Prime a2 a3 b2 b3).toNat = n4QTopPhase1 a2 a3 b2 b3)
    (h_no_wrap_phase1 :
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat ≤
        ((n4RhatPrime a2 a3 b2 b3).toNat % 2^32) * 2^32 +
          (n4DivUn1 a2 a3 b3).toNat) :
    (n4Un21 a2 a3 b2 b3).toNat <
      (n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat := by
  -- b3' = dHi*2^32 + dLo, b3' ≥ 2^63 (so > 0).
  have h_b3'_ge : (n4B3Prime b2 b3).toNat ≥ 2^63 := by
    rw [n4B3Prime_unfold, n4ClzShift_unfold, n4ClzAntiShift_unfold]
    exact b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_v_eq : (n4B3Prime b2 b3).toNat =
      (n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat := by
    rw [n4DHi_unfold, n4DLo_unfold]; exact div128Quot_vTop_decomp _
  -- D2b-A: Phase 1b Euclidean.
  have h_eucl := n4_phase1b_eucl a2 a3 b2 b3 hb3nz hshift_nz hcall
  -- D2b-B: un21.toNat formula.
  have h_un21_eq := n4Un21_toNat_of_no_wrap a2 a3 b2 b3
    hb3nz hshift_nz hcall h_no_wrap_phase1
  -- q_top_phase1 strict upper: u4*2^32+div_un1 < (q1'+1)*vTop.
  have h_b3'_pos : 0 < (n4B3Prime b2 b3).toNat := by
    have : (n4B3Prime b2 b3).toNat ≥ 2^63 := h_b3'_ge; omega
  have h_q1_eq' :
      (n4Q1Prime a2 a3 b2 b3).toNat =
      ((n4U4 a3 b3).toNat * 2^32 + (n4DivUn1 a2 a3 b3).toNat) /
        (n4B3Prime b2 b3).toNat := by
    rw [h_q1_eq, n4QTopPhase1_unfold]
  have h_q_top_upper :
      (n4U4 a3 b3).toNat * 2^32 + (n4DivUn1 a2 a3 b3).toNat <
      ((n4Q1Prime a2 a3 b2 b3).toNat + 1) * (n4B3Prime b2 b3).toNat := by
    rw [h_q1_eq']
    have h := Nat.lt_mul_div_succ
      ((n4U4 a3 b3).toNat * 2^32 + (n4DivUn1 a2 a3 b3).toNat) h_b3'_pos
    -- h : a < b * (a / b + 1) — commute multiplication.
    linarith
  -- Final arithmetic.
  rw [h_un21_eq]
  -- Goal: (rhat'%2^32)*2^32 + div_un1 - q1'*dLo < dHi*2^32 + dLo
  have h_mod_le : (n4RhatPrime a2 a3 b2 b3).toNat % 2^32 ≤
      (n4RhatPrime a2 a3 b2 b3).toNat := Nat.mod_le _ _
  have h_mod_pow32_le : (n4RhatPrime a2 a3 b2 b3).toNat % 2^32 * 2^32 ≤
      (n4RhatPrime a2 a3 b2 b3).toNat * 2^32 :=
    Nat.mul_le_mul_right _ h_mod_le
  -- From h_eucl: q1' * dHi + rhat' = u4. Multiply by 2^32:
  -- q1'*dHi*2^32 + rhat'*2^32 = u4*2^32.
  have h_eucl_pow32 :
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DHi b2 b3).toNat * 2^32 +
        (n4RhatPrime a2 a3 b2 b3).toNat * 2^32 =
      (n4U4 a3 b3).toNat * 2^32 := by
    have h := congrArg (· * 2^32) h_eucl
    simp only at h
    linarith
  -- h_q_top_upper expanded: u4*2^32 + div_un1
  --   < (q1'+1)*(dHi*2^32 + dLo) = q1'*dHi*2^32 + q1'*dLo + dHi*2^32 + dLo
  rw [h_v_eq] at h_q_top_upper
  have h_expand : ((n4Q1Prime a2 a3 b2 b3).toNat + 1) *
      ((n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat) =
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DHi b2 b3).toNat * 2^32 +
      (n4Q1Prime a2 a3 b2 b3).toNat * (n4DLo b2 b3).toNat +
      (n4DHi b2 b3).toNat * 2^32 + (n4DLo b2 b3).toNat := by ring
  rw [h_expand] at h_q_top_upper
  -- Conclude via omega.
  omega

-- ============================================================================
-- D5: Compose into Div128PhaseNoWrapInv
-- ============================================================================

/-- **D5 (CLOSED via composition)**: Skip-borrow implies
    `Div128PhaseNoWrapInv` (modulo D2b sub-stub).

    Composes D1c (Phase 1 tight) → D2/D3 (Phase 1 no-wrap) → D2b
    (un21 < vTop). The result is the conjunction in
    `Div128PhaseNoWrapInv` after bundle/let-form bridging. -/
theorem div128_phase_no_wrap_of_skip_borrow
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    Div128PhaseNoWrapInv (n4U4 a3 b3) (n4Un3 a2 a3 b3) (n4B3Prime b2 b3) := by
  -- Phase 1 tight from D1c.
  have h_q1_eq := div128Quot_q1_prime_eq_q_top_phase1_of_skip_borrow
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall hborrow
  -- Phase 1 no-wrap from D2/D3.
  have h_no_wrap := div128Quot_phase1_no_wrap_of_q1_prime_eq_q_top_phase1
    a2 a3 b2 b3 hb3nz hshift_nz hcall h_q1_eq
  -- un21 < vTop from D2b.
  have h_un21_lt := div128Quot_un21_lt_vTop_from_phase1_tight
    a2 a3 b2 b3 hb3nz hshift_nz hcall h_q1_eq h_no_wrap
  -- Unfold Div128PhaseNoWrapInv to expose the let-form conjuncts.
  unfold Div128PhaseNoWrapInv
  simp only []
  -- Establish bundle/let-form correspondences.
  have h_q1_letform :
      (let dHi := (n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat
       let dLo := ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
                    (32 : BitVec 6).toNat
       let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu (n4U4 a3 b3) dHi
       let rhat := (n4U4 a3 b3) - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc : Word := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c) =
      n4Q1Prime a2 a3 b2 b3 := by
    rw [n4Q1Prime_unfold, algorithmQ1Prime_unfold]
  have h_rhat_letform :
      (let dHi := (n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat
       let dLo := ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
                    (32 : BitVec 6).toNat
       let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu (n4U4 a3 b3) dHi
       let rhat := (n4U4 a3 b3) - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc : Word := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) =
      n4RhatPrime a2 a3 b2 b3 := by
    rw [n4RhatPrime_unfold, algorithmRhatPrime_unfold]
  have h_un21_letform :
      (let dHi := (n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat
       let dLo := ((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
                    (32 : BitVec 6).toNat
       let div_un1 := (n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat
       let q1 := rv64_divu (n4U4 a3 b3) dHi
       let rhat := (n4U4 a3 b3) - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c : Word := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc : Word := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
       let q1' : Word := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095
                        else q1c
       let rhat' : Word := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
       let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
       let cu_q1_dlo := q1' * dLo
       cu_rhat_un1 - cu_q1_dlo) =
      n4Un21 a2 a3 b2 b3 := by
    rw [n4Un21_unfold, algorithmUn21_unfold]
  refine ⟨?_, ?_⟩
  · -- un21 < dHi*2^32 + dLo conjunct (D2b).
    rw [h_un21_letform]
    -- Need to bridge dHi*2^32 + dLo on RHS to n4DHi*2^32 + n4DLo.
    show (n4Un21 a2 a3 b2 b3).toNat <
         ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat).toNat * 2^32 +
         (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
           (32 : BitVec 6).toNat).toNat
    rw [show ((n4B3Prime b2 b3) >>> (32 : BitVec 6).toNat) = n4DHi b2 b3 from
      (n4DHi_unfold b2 b3).symm,
        show (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
              (32 : BitVec 6).toNat) = n4DLo b2 b3 from (n4DLo_unfold b2 b3).symm]
    exact h_un21_lt
  · -- q1' * dLo ≤ (rhat' % 2^32) * 2^32 + div_un1 conjunct (D2/D3).
    rw [h_q1_letform, h_rhat_letform]
    show (n4Q1Prime a2 a3 b2 b3).toNat *
         (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
           (32 : BitVec 6).toNat).toNat ≤
         (n4RhatPrime a2 a3 b2 b3).toNat % 2^32 * 2^32 +
         ((n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat).toNat
    rw [show (((n4B3Prime b2 b3) <<< (32 : BitVec 6).toNat) >>>
              (32 : BitVec 6).toNat) = n4DLo b2 b3 from (n4DLo_unfold b2 b3).symm,
        show ((n4Un3 a2 a3 b3) >>> (32 : BitVec 6).toNat) = n4DivUn1 a2 a3 b3
              from (n4DivUn1_unfold a2 a3 b3).symm]
    exact h_no_wrap

end EvmAsm.Evm64
