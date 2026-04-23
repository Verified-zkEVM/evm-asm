/-
  EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly

  Second half of the top-down Knuth-B analysis for `div128Quot`. Split
  from `Div128QuotientBounds.lean` (issue #61) to keep files under the
  1500-line size cap.

  This file contains the Phase 2 un21 machinery and final output
  assembly:
  - **KB-3f**: `q1' * dLo` no-wraparound under hcall.
  - **KB-3g**: `halfword_combine_mod` — generalized halfword combine.
  - **KB-3h**: `cu_rhat_un1.toNat` formula.
  - **KB-3i**: `un21.toNat` modular formula.
  - **KB-3j**: `un21.toNat` case-split on wraparound.
  - **KB-3k**: `vTop` decomposition utility.
  - **KB-3l/KB-3m**: `un21` abstract-dividend identity (subtractive + additive).
  - **KB-4**: Phase 2a bounds (instantiation of Phase 1a).
  - **KB-5**: Phase 2b bounds (instantiation of Phase 1b).
  - **KB-6a**: `div128Quot.toNat` output formula via `halfword_combine_mod`.
  - **KB-6a strict**: Cleaner form without `% 2^32` (via KB-3e''').

  Phase 1 quotient bounds (KB-1..KB-3e''' + KB-6b Phase 2b strict) live
  in `Div128QuotientBounds.lean`.

  See `memory/project_knuth_theorem_b_plan.md` for the full roadmap.
-/

import EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **KB-3f: No-wraparound for `q1' * dLo`.** Under the call-trial
    precondition, the Word-level product equals the Nat-level product:

    ```
    (q1' * dLo).toNat = q1'.toNat * dLo.toNat
    ```

    Proof: from KB-3e, `q1'.toNat ≤ 2^32 + 1`; `dLo.toNat < 2^32`.  Hence
    `q1'.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) = 2^64 - 1 < 2^64`.
    Word multiplication therefore doesn't wrap, and `BitVec.toNat_mul`
    gives the stated equality.

    This is the key no-wraparound fact for subsequent Phase 2 analysis
    (bounding `un21`, relating it to abstract dividend quantities). -/
theorem div128Quot_q1_prime_dLo_no_wrap (uHi dHi dLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    (q1' * dLo).toNat = q1'.toNat * dLo.toNat := by
  intro q1 hi1 q1c q1'
  have h_q1'_le : q1'.toNat ≤ 2^32 + 1 :=
    div128Quot_q1_prime_le_pow32_plus_one uHi dHi dLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  -- q1'.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) = 2^64 - 1.
  have h_mul_lt : q1'.toNat * dLo.toNat < 2^64 := by
    have : q1'.toNat * dLo.toNat ≤ (2^32 + 1) * (2^32 - 1) := by
      have hdLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
      exact Nat.mul_le_mul h_q1'_le hdLo_le
    have h_eq : (2^32 + 1) * (2^32 - 1) = 2^64 - 1 := by decide
    omega
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h_mul_lt]

/-- **KB-3g: Generalized halfword combine.** Without an upper bound on
    `a`, the shift-left-by-32 + OR construction still has a clean Nat
    formula, truncating `a` modulo `2^32`:

    ```
    (a <<< 32 ||| b).toNat = (a.toNat % 2^32) * 2^32 + b.toNat
    ```

    Generalizes `halfword_combine` (which requires `a.toNat < 2^32`) by
    dropping the upper bound on `a`.  Useful for the Phase 2 `cu_rhat_un1`
    construction, where `rhat'` may exceed `2^32` (current bound:
    `< 3 * dHi`), so the top bits of `rhat'` get truncated by the shift
    and we need a Nat formula that captures this. -/
theorem halfword_combine_mod (a b : Word) (hb : b.toNat < 2^32) :
    (a <<< 32 ||| b).toNat = (a.toNat % 2^32) * 2^32 + b.toNat := by
  -- The shifted `a <<< 32` has its low 32 bits zero, and `b` has its
  -- high 32 bits zero, so their bitwise AND is zero and OR = ADD.
  have h_disjoint : a <<< 32 &&& b = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases hi : (i : Nat) < 32
    · simp [hi]
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and]
      have hbi : b[i] = false := by
        simp only [BitVec.getElem_eq_testBit_toNat]
        apply Nat.testBit_lt_two_pow
        calc b.toNat < 2 ^ 32 := hb
          _ ≤ 2 ^ (i : Nat) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hbi]
  rw [(BitVec.add_eq_or_of_and_eq_zero (a <<< 32) b h_disjoint).symm,
      BitVec.toNat_add_of_and_eq_zero h_disjoint,
      BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  -- Goal: (a.toNat * 2^32) % 2^64 + b.toNat = (a.toNat % 2^32) * 2^32 + b.toNat
  -- Use (a.toNat * 2^32) % 2^64 = (a.toNat % 2^32) * 2^32.
  have h_mod : (a.toNat * 2^32) % 2^64 = (a.toNat % 2^32) * 2^32 := by
    rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide,
        Nat.mul_mod_mul_right]
  rw [h_mod]

/-- Utility: right-shifting a 64-bit Word by 32 produces a value bounded
    by `2^32`. -/
theorem Word_ushiftRight_32_lt_pow32 {x : Word} :
    (x >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
  rw [BitVec.toNat_ushiftRight]
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32, Nat.shiftRight_eq_div_pow]
  have : x.toNat < 2^64 := x.isLt
  have : x.toNat / 2^32 < 2^32 := by
    apply Nat.div_lt_of_lt_mul
    have : (2^32 : Nat) * 2^32 = 2^64 := by decide
    omega
  exact this

/-- **KB-3h: cu_rhat_un1.toNat formula.** For Phase 2's
    `cu_rhat_un1 := (rhat' <<< 32) ||| div_un1` where `div_un1 := uLo >>> 32`,
    the Nat representation is:

    ```
    cu_rhat_un1.toNat = (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    ```

    Direct application of `halfword_combine_mod` (KB-3g) with
    `div_un1 < 2^32` discharged via `Word_ushiftRight_32_lt_pow32`.

    Key step of the Phase 2 un21 identity.  Note that if `rhat' ≥ 2^32`
    (possible under the current `rhat' < 3 * dHi` bound), the formula
    truncates `rhat'` modulo `2^32` — Phase 2 "sees" only the low 32
    bits of rhat'. -/
theorem div128Quot_cu_rhat_un1_toNat (rhat' uLo : Word) :
    ((rhat' <<< (32 : BitVec 6).toNat) ||| (uLo >>> (32 : BitVec 6).toNat)).toNat =
    (rhat'.toNat % 2^32) * 2^32 + (uLo >>> (32 : BitVec 6).toNat).toNat := by
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32]
  apply halfword_combine_mod
  rw [← h32]
  exact Word_ushiftRight_32_lt_pow32

/-- **KB-3i: un21.toNat Nat formula.** Composes KB-3f (q1' * dLo no-wrap
    under hcall) + KB-3h (cu_rhat_un1 formula) + `BitVec.toNat_sub` to
    give an explicit modular-arithmetic formula for `un21.toNat`:

    ```
    un21.toNat =
      ((rhat'.toNat % 2^32) * 2^32 + (uLo >>> 32).toNat + 2^64
         - q1'.toNat * dLo.toNat) % 2^64
    ```

    under the standard hcall preconditions (`dHi ≥ 2^31`, `dLo < 2^32`,
    `uHi < dHi * 2^32 + dLo`).

    The `% 2^64` captures potential BitVec wraparound when `cu_q1_dlo`
    exceeds `cu_rhat_un1` (which happens in the "correction" case of
    Phase 2).  Subsequent lemmas can case-split on the wraparound. -/
theorem div128Quot_un21_toNat (uHi dHi dLo uLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat = ((rhat'.toNat % 2^32) * 2^32 + div_un1.toNat + 2^64 -
                   q1'.toNat * dLo.toNat) % 2^64 := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21
  have h_cu_rhat : cu_rhat_un1.toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat :=
    div128Quot_cu_rhat_un1_toNat rhat' uLo
  have h_cu_q1 : cu_q1_dlo.toNat = q1'.toNat * dLo.toNat :=
    div128Quot_q1_prime_dLo_no_wrap uHi dHi dLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  show (cu_rhat_un1 - cu_q1_dlo).toNat = _
  rw [BitVec.toNat_sub, h_cu_rhat, h_cu_q1]
  -- Reassociation modulo 2^64.
  congr 1
  omega

/-- **KB-3j: un21.toNat case-split on wraparound.** Resolves the
    modular formula from KB-3i into two cases based on whether the
    BitVec subtraction wraps:

    Let `A := (rhat'.toNat % 2^32) * 2^32 + (uLo >>> 32).toNat`
    and `B := q1'.toNat * dLo.toNat`.

    - **No wrap** (`B ≤ A`): `un21.toNat = A - B`.
    - **Wrap** (`A < B`): `un21.toNat = A + 2^64 - B`.

    The "no wrap" case is Knuth's expected flow. The "wrap" case should
    never occur in Knuth's algorithm by the multiplication-check
    invariant (Phase 1b was designed to prevent it), but formalizing
    that takes substantial work, so this lemma exposes both branches
    and leaves the choice to downstream reasoning. -/
theorem div128Quot_un21_toNat_case (uHi dHi dLo uLo rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let A := (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1'.toNat * dLo.toNat
    (B ≤ A → un21.toNat = A - B) ∧
    (A < B → un21.toNat = A + 2^64 - B) := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21 A B
  have h_formula : un21.toNat = (A + 2^64 - B) % 2^64 :=
    div128Quot_un21_toNat uHi dHi dLo uLo rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop
  have h_A_lt : A < 2^64 := by
    show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat < 2^64
    have h_rhat_mod : rhat'.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    have h_divun1_lt : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    nlinarith
  have h_B_lt : B < 2^64 := by
    show q1'.toNat * dLo.toNat < 2^64
    have h_cu : cu_q1_dlo.toNat = q1'.toNat * dLo.toNat :=
      div128Quot_q1_prime_dLo_no_wrap uHi dHi dLo rhatUn1
        hdHi_ge hdLo_lt huHi_lt_vTop
    have := cu_q1_dlo.isLt
    omega
  refine ⟨?_, ?_⟩
  · intro hBA
    rw [h_formula]
    show (A + 2^64 - B) % 2^64 = A - B
    rw [show A + 2^64 - B = (A - B) + 2^64 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : A - B < 2^64)]
  · intro hAB
    rw [h_formula]
    show (A + 2^64 - B) % 2^64 = A + 2^64 - B
    exact Nat.mod_eq_of_lt (by omega)

/-- **KB-3k: vTop decomposition.** The divisor `vTop` decomposes cleanly
    into its high and low 32-bit halves `dHi` and `dLo`:

    ```
    vTop.toNat = dHi.toNat * 2^32 + dLo.toNat
    ```

    where `dHi := vTop >>> 32` and `dLo := (vTop <<< 32) >>> 32`.

    Pure utility: holds unconditionally for any 64-bit `vTop`.  Used to
    connect Phase 2's formula (involving `dHi` and `dLo` separately) with
    abstract dividend quantities that use `vTop` directly. -/
theorem div128Quot_vTop_decomp (vTop : Word) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
  intro dHi dLo
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  have h_dHi : dHi.toNat = vTop.toNat / 2^32 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow]
  have h_dLo : dLo.toNat = vTop.toNat % 2^32 := by
    show ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, h32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq]
    rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide,
        Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide : (0:Nat) < 2^32)]
  rw [h_dHi, h_dLo]
  have := Nat.div_add_mod vTop.toNat (2^32)
  omega

/-- Utility: multiplying a Nat by `2^32` decomposes via Nat.div_add_mod. -/
theorem Nat_mul_pow32_split {x : Nat} :
    x * 2^32 = (x / 2^32) * 2^64 + (x % 2^32) * 2^32 := by
  have hdiv : x = (x / 2^32) * 2^32 + x % 2^32 := by
    have := Nat.div_add_mod x (2^32); linarith
  calc x * 2^32
      = ((x / 2^32) * 2^32 + x % 2^32) * 2^32 := by rw [← hdiv]
    _ = (x / 2^32) * (2^32 * 2^32) + (x % 2^32) * 2^32 := by ring
    _ = (x / 2^32) * 2^64 + (x % 2^32) * 2^32 := by
        rw [show (2^32 * 2^32 : Nat) = 2^64 from by decide]

/-- **KB-3l: un21 connects to the abstract dividend (no-wrap case).**
    Under call-trial preconditions, Phase 1b Euclidean, and no-wrap
    (B ≤ A in KB-3j's notation), plus the semantic ordering
    `q1' * vTop ≤ uHi * 2^32 + div_un1`:

    ```
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 =
      uHi.toNat * 2^32 + (uLo >>> 32).toNat - q1'.toNat * vTop.toNat
    ```

    The `(rhat' / 2^32) * 2^64` correction captures the "lost high bits"
    of `rhat'` truncated by the shift in `cu_rhat_un1`. When `rhat' <
    2^32` (Knuth's tight invariant, currently unproven here), this
    correction is zero and `un21` equals the abstract dividend directly. -/
theorem div128Quot_un21_abstract_dividend
    (uHi dHi dLo uLo vTop rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_dHi_eq : dHi = vTop >>> (32 : BitVec 6).toNat)
    (h_dLo_eq : dLo = (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let A := (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1'.toNat * dLo.toNat
    B ≤ A →
    q1'.toNat * vTop.toNat ≤ uHi.toNat * 2^32 + div_un1.toNat →
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 =
      uHi.toNat * 2^32 + div_un1.toNat - q1'.toNat * vTop.toNat := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21 A B
    hBA habs_ge
  have h_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat = A - B := h_case.1 hBA
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := by
    rw [h_dHi_eq]; exact Word_ushiftRight_32_lt_pow32
  have h_post := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_rhatc_lt := div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt
  have h_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post h_rhatc_lt
  have h_vtop := div128Quot_vTop_decomp vTop
  rw [← h_dHi_eq, ← h_dLo_eq] at h_vtop
  -- Sub-lemma 1: rhat' * 2^32 decomposes.
  have h_rhat_split : rhat'.toNat * 2^32 =
      (rhat'.toNat / 2^32) * 2^64 + (rhat'.toNat % 2^32) * 2^32 :=
    Nat_mul_pow32_split
  -- Sub-lemma 2: rhat' = uHi - q1' * dHi at Nat (from h_eucl).
  have h_rhat_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by omega
  -- Sub-lemma 3: q1' * vTop expanded.
  have h_q1_vtop : q1'.toNat * vTop.toNat =
      q1'.toNat * dHi.toNat * 2^32 + q1'.toNat * dLo.toNat := by
    rw [h_vtop]; ring
  -- Sub-lemma 4: q1' * dHi * 2^32 ≤ uHi * 2^32.
  have h_le : q1'.toNat * dHi.toNat * 2^32 ≤ uHi.toNat * 2^32 := by
    apply Nat.mul_le_mul_right; omega
  -- Sub-lemma 5: rhat' * 2^32 = uHi * 2^32 - q1' * dHi * 2^32.
  have h_rhat_mul : rhat'.toNat * 2^32 =
      uHi.toNat * 2^32 - q1'.toNat * dHi.toNat * 2^32 := by
    rw [h_rhat_eq, Nat.sub_mul]
  -- Final assembly.
  show un21.toNat + (rhat'.toNat / 2^32) * 2^64 = _
  rw [h_un21]
  show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat
    + (rhat'.toNat / 2^32) * 2^64 = _
  -- Key facts for omega:
  -- h_rhat_split: rhat' * 2^32 = (rhat'/2^32) * 2^64 + (rhat'%2^32) * 2^32.
  -- h_rhat_mul: rhat' * 2^32 = uHi * 2^32 - q1' * dHi * 2^32.
  -- h_q1_vtop: q1' * vTop = q1' * dHi * 2^32 + q1' * dLo.
  -- h_le: q1' * dHi * 2^32 ≤ uHi * 2^32.
  -- habs_ge: q1' * vTop ≤ uHi * 2^32 + div_un1.
  -- Goal: (rhat'%2^32) * 2^32 + div_un1 - q1' * dLo + (rhat'/2^32) * 2^64
  --     = uHi * 2^32 + div_un1 - q1' * vTop.
  -- Use hBA to unfold A, B.
  have h_BA_num : q1'.toNat * dLo.toNat ≤
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := hBA
  omega

/-- **KB-3m: un21 additive identity (no-wrap case).** Reformulation of
    KB-3l using addition instead of subtraction, eliminating the need
    for the semantic ordering hypothesis `habs_ge`:

    ```
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat =
      uHi.toNat * 2^32 + (uLo >>> 32).toNat
    ```

    Same underlying math as KB-3l, but Nat addition on both sides is
    well-defined without ordering constraints. Use this form downstream
    when you want to reason about the relation without discharging
    `habs_ge`. -/
theorem div128Quot_un21_additive_identity
    (uHi dHi dLo uLo vTop rhatUn1 : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_dHi_eq : dHi = vTop >>> (32 : BitVec 6).toNat)
    (h_dLo_eq : dLo = (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    let rhat' := if BitVec.ult rhatUn1 (q1c * dLo) then rhatc + dHi else rhatc
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let A := (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
    let B := q1'.toNat * dLo.toNat
    B ≤ A →
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat =
      uHi.toNat * 2^32 + div_un1.toNat := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21 A B hBA
  have h_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  have h_un21 : un21.toNat = A - B := h_case.1 hBA
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have hdHi_lt : dHi.toNat < 2^32 := by
    rw [h_dHi_eq]; exact Word_ushiftRight_32_lt_pow32
  have h_post := div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_rhatc_lt := div128Quot_rhatc_lt_2dHi uHi dHi hdHi_ne hdHi_lt
  have h_eucl : q1'.toNat * dHi.toNat + rhat'.toNat = uHi.toNat :=
    div128Quot_phase1b_post uHi dHi q1c rhatc dLo rhatUn1 hdHi_lt h_post h_rhatc_lt
  have h_vtop := div128Quot_vTop_decomp vTop
  rw [← h_dHi_eq, ← h_dLo_eq] at h_vtop
  have h_rhat_split : rhat'.toNat * 2^32 =
      (rhat'.toNat / 2^32) * 2^64 + (rhat'.toNat % 2^32) * 2^32 :=
    Nat_mul_pow32_split
  have h_rhat_eq : rhat'.toNat = uHi.toNat - q1'.toNat * dHi.toNat := by omega
  have h_rhat_mul : rhat'.toNat * 2^32 =
      uHi.toNat * 2^32 - q1'.toNat * dHi.toNat * 2^32 := by
    rw [h_rhat_eq, Nat.sub_mul]
  have h_q1_vtop : q1'.toNat * vTop.toNat =
      q1'.toNat * dHi.toNat * 2^32 + q1'.toNat * dLo.toNat := by
    rw [h_vtop]; ring
  have h_le : q1'.toNat * dHi.toNat * 2^32 ≤ uHi.toNat * 2^32 := by
    apply Nat.mul_le_mul_right; omega
  show un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat = _
  rw [h_un21]
  show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat
    + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat = _
  have h_BA_num : q1'.toNat * dLo.toNat ≤
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := hBA
  rw [h_q1_vtop]
  omega

-- ============================================================================
-- Piece B: Phase 2a bounds via Phase 1a reuse (KB-4)
-- ============================================================================

/-- **KB-4a: Phase 2a Euclidean.** Direct instantiation of
    `div128Quot_first_round_post` with `uHi := un21`: the Phase 2a
    post-correction quotient `q0c` and remainder `rhat2c` satisfy the
    Euclidean equation against `un21`:

    ```
    q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat
    ```

    Phase 1a lemmas are generic over the dividend — they take any Word
    as `uHi`.  This is the observation documented in the Knuth-B plan
    memo: Phase 2 bounds require no new code beyond thin instantiation
    wrappers. -/
theorem div128Quot_phase2a_euclidean (un21 dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat :=
  div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt

/-- **KB-4b: Phase 2a remainder bound.** Instantiation of
    `div128Quot_rhatc_lt_2dHi`: `rhat2c < 2 * dHi`. -/
theorem div128Quot_phase2a_rhat2c_lt_2dHi (un21 dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    rhat2c.toNat < 2 * dHi.toNat :=
  div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt

/-- **KB-4c: Phase 2a quotient bound.** Instantiation of
    `div128Quot_q1c_lt_pow33`: `q0c < 2^33`. -/
theorem div128Quot_phase2a_q0c_lt_pow33 (un21 dHi : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31) :
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    q0c.toNat < 2^33 :=
  div128Quot_q1c_lt_pow33 un21 dHi hdHi_ge

-- ============================================================================
-- Piece B: Phase 2b bounds via Phase 1b reuse (KB-5)
-- ============================================================================

/-- **KB-5a: Phase 2b Euclidean.** Instantiation of
    `div128Quot_phase1b_post` with `uHi := un21`, `q1c := q0c`,
    `rhatc := rhat2c`: post-Phase-2b (Phase 2b's multiplication-check
    correction), the corrected quotient `q0'` and remainder `rhat2'`
    still satisfy the Euclidean equation against `un21`. -/
theorem div128Quot_phase2b_post (un21 dHi : Word)
    (hdHi_lt : dHi.toNat < 2^32) (q0c rhat2c dLo : Word)
    (h_post : q0c.toNat * dHi.toNat + rhat2c.toNat = un21.toNat)
    (h_rhat2c_lt : rhat2c.toNat < 2 * dHi.toNat) :
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    -- rhat2' mirrors the guard: fires → no check adjustment (rhat2c);
    -- fall-through → the Phase 1b check may have added dHi.
    let rhat2' := if rhat2cHi = 0 then
                    (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    q0'.toNat * dHi.toNat + rhat2'.toNat = un21.toNat := by
  intro rhat2cHi rhat2Un0 q0' rhat2'
  show (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat * dHi.toNat +
       rhat2'.toNat = un21.toNat
  unfold div128Quot_phase2b_q0'
  by_cases h_guard : rhat2cHi = 0
  · show (if rhat2c >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                (q0c * dLo) then q0c + signExtend12 4095 else q0c)
          else q0c).toNat * dHi.toNat + rhat2'.toNat = un21.toNat
    rw [if_pos h_guard]
    show (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
              (q0c * dLo) then q0c + signExtend12 4095 else q0c).toNat *
         dHi.toNat + rhat2'.toNat = un21.toNat
    have hrhat2' : rhat2' = (if BitVec.ult rhat2Un0 (q0c * dLo)
                             then rhat2c + dHi else rhat2c) := by
      show (if rhat2cHi = 0 then
              (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
            else rhat2c) = _
      rw [if_pos h_guard]
    rw [hrhat2']
    exact div128Quot_phase1b_post un21 dHi q0c rhat2c dLo rhat2Un0 hdHi_lt
      h_post h_rhat2c_lt
  · show (if rhat2c >>> (32 : BitVec 6).toNat = 0 then
            (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                (q0c * dLo) then q0c + signExtend12 4095 else q0c)
          else q0c).toNat * dHi.toNat + rhat2'.toNat = un21.toNat
    rw [if_neg h_guard]
    have hrhat2' : rhat2' = rhat2c := by
      show (if rhat2cHi = 0 then
              (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
            else rhat2c) = _
      rw [if_neg h_guard]
    rw [hrhat2']
    exact h_post

/-- **KB-5b: Phase 2b check implies q0c ≥ 1.** Instantiation of
    `div128Quot_phase1b_check_implies_q1c_pos`. -/
theorem div128Quot_phase2b_check_implies_q0c_pos (q0c dLo rhat2Un0 : Word)
    (h_check : BitVec.ult rhat2Un0 (q0c * dLo)) :
    q0c.toNat ≥ 1 :=
  div128Quot_phase1b_check_implies_q1c_pos q0c dLo rhat2Un0 h_check

/-- **KB-5c: Phase 2b quotient bound.** Instantiation of
    `div128Quot_phase1b_quotient_bound` with `uHi := un21`. -/
theorem div128Quot_phase2b_quotient_bound (un21 dHi : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32)
    (dLo : Word) :
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat + 2 ≥ un21.toNat / dHi.toNat ∧
    q0'.toNat ≤ un21.toNat / dHi.toNat := by
  intro q0 hi2 q0c q0'
  show (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat + 2 ≥
         un21.toNat / dHi.toNat ∧
       (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat ≤ un21.toNat / dHi.toNat
  unfold div128Quot_phase2b_q0'
  split
  · -- Guard doesn't fire: helper yields unguarded check.
    exact div128Quot_phase1b_quotient_bound un21 dHi hdHi_ne hdHi_lt dLo
      ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
  · -- Guard fires: helper = q0c. Use KB-1 (phase1a quotient bound).
    have h_kb1 : q0c.toNat ≤ un21.toNat / dHi.toNat ∧
                 un21.toNat / dHi.toNat ≤ q0c.toNat + 1 :=
      div128Quot_phase1a_quotient_bound un21 dHi hdHi_ne hdHi_lt
    exact ⟨by omega, h_kb1.1⟩

/-- **KB-5d: Phase 2b output bound.** Instantiation of
    `div128Quot_q1_prime_lt_pow33` with `uHi := un21`: `q0' < 2^33`. -/
theorem div128Quot_phase2b_q0_prime_lt_pow33 (un21 dHi : Word)
    (hdHi_ge : dHi.toNat ≥ 2^31) (dLo : Word) :
    let q0 := rv64_divu un21 dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^33 := by
  intro q0 hi2 q0c q0'
  show (div128Quot_phase2b_q0' q0c rhat2c dLo div_un0).toNat < 2^33
  unfold div128Quot_phase2b_q0'
  split
  · -- Guard doesn't fire: helper yields unguarded check — use KB-3e for Phase 2.
    show (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
              (q0c * dLo) then q0c + signExtend12 4095 else q0c).toNat < 2^33
    exact div128Quot_q1_prime_lt_pow33 un21 dHi hdHi_ge dLo
      ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
  · -- Guard fires: helper yields q0c. Note q0c < 2^33 via KB-3e' at Phase 2.
    have h_q0c_lt : q0c.toNat < 2^33 :=
      div128Quot_q1c_lt_pow33 un21 dHi hdHi_ge
    exact h_q0c_lt

/-- **KB-6a: div128Quot output Nat formula.** Unfolds `div128Quot` and
    applies `halfword_combine_mod` to yield the output's Nat value:

    ```
    (div128Quot uHi uLo vTop).toNat = (q1'.toNat % 2^32) * 2^32 + q0'.toNat
    ```

    when `q0'.toNat < 2^32`.

    The `% 2^32` on `q1'` captures the top bits truncated by the final
    `<<< 32` shift — Phase 1b's `q1'` may exceed `2^32` (current bound
    `≤ 2^32 + 1` under hcall from KB-3e), so those high bits are lost
    in the output assembly. That loss is benign because the Knuth-B
    quotient bound only cares about the value modulo `2^64`, and
    `q_true * vTop ≤ uHi * 2^64 + uLo < 2^64 * vTop` guarantees
    `q_true < 2^64`.

    First step of the final-assembly chain (KB-6). Uses only
    `halfword_combine_mod` (KB-3g) and no Phase 2 infrastructure, so
    lives on the main path of the call-trial bounds. -/
theorem div128Quot_toNat_eq (uHi uLo vTop : Word) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^32 →
    (div128Quot uHi uLo vTop).toNat = (q1'.toNat % 2^32) * 2^32 + q0'.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' hq0
  show ((q1' <<< (32 : BitVec 6).toNat) ||| q0').toNat =
    (q1'.toNat % 2^32) * 2^32 + q0'.toNat
  have h32 : (32 : BitVec 6).toNat = 32 := by decide
  rw [h32]
  exact halfword_combine_mod q1' q0' hq0

/-- **KB-6a strict: div128Quot output Nat formula without mod.** Composes
    KB-6a (`div128Quot_toNat_eq`) with KB-3e''' (`div128Quot_q1_prime_lt_pow32`)
    to drop the `% 2^32` on `q1'` in KB-6a:

    ```
    (div128Quot uHi uLo vTop).toNat = q1'.toNat * 2^32 + q0'.toNat
    ```

    Under the same hcall preconditions as KB-3e''' plus `q0' < 2^32`
    (from KB-6b when `un21 < vTop`). Cleaner form for downstream KB-6c/d
    assembly. -/
theorem div128Quot_toNat_eq_strict (uHi uLo vTop : Word)
    (hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31)
    (hdHi_lt : (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32)
    (hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                 (32 : BitVec 6).toNat).toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^32 →
    (div128Quot uHi uLo vTop).toNat = q1'.toNat * 2^32 + q0'.toNat := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0' hq0
  have h_kb6a := div128Quot_toNat_eq uHi uLo vTop hq0
  have h_q1'_lt : q1'.toNat < 2^32 :=
    div128Quot_q1_prime_lt_pow32 uHi dHi dLo uLo
      hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop
  rw [h_kb6a, Nat.mod_eq_of_lt h_q1'_lt]


end EvmAsm.Evm64
