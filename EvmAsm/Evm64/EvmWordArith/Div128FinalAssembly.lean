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
open EvmAsm.Rv64.AddrNorm (bv6_toNat_32)

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
    have : (2^32 + 1) * (2^32 - 1) = 2^64 - 1 := by decide
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
  rw [bv6_toNat_32, Nat.shiftRight_eq_div_pow]
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
  rw [bv6_toNat_32]
  apply halfword_combine_mod
  rw [← bv6_toNat_32]
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
  have : A < 2^64 := by
    show (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat < 2^64
    have : rhat'.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    have : div_un1.toNat < 2^32 := Word_ushiftRight_32_lt_pow32
    nlinarith
  have : B < 2^64 := by
    show q1'.toNat * dLo.toNat < 2^64
    have : cu_q1_dlo.toNat = q1'.toNat * dLo.toNat :=
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
  have h_dHi : dHi.toNat = vTop.toNat / 2^32 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
  have h_dLo : dLo.toNat = vTop.toNat % 2^32 := by
    show ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat = _
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
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

/-- **KB-3m-uncond: wrap-aware additive identity (NEW, CLOSED).**

    Unconditional form of KB-3m. Where KB-3m requires `B ≤ A` (no-wrap),
    this version handles both wrap and no-wrap via an explicit
    boolean indicator `w ∈ {0, 1}`:

    ```
    un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat
      = uHi.toNat * 2^32 + div_un1.toNat + w * 2^64
    ```

    where `w = 0` in the no-wrap case (`B ≤ A`) and `w = 1` in the
    wrap case (`A < B`). Composes KB-3j (un21 case-split) with the
    same Phase 1b Euclidean + vTop decomposition algebra as KB-3m.

    Useful when the no-wrap precondition cannot be discharged
    locally — pushes the case-split deeper into the user. -/
theorem div128Quot_un21_additive_identity_uncond
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
    ∃ w : Nat, w ≤ 1 ∧
      un21.toNat + (rhat'.toNat / 2^32) * 2^64 + q1'.toNat * vTop.toNat =
        uHi.toNat * 2^32 + div_un1.toNat + w * 2^64 := by
  intro q1 rhat hi1 q1c rhatc q1' rhat' div_un1 cu_rhat_un1 cu_q1_dlo un21
  have h_case := div128Quot_un21_toNat_case uHi dHi dLo uLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop
  simp only [] at h_case
  -- h_case : (B ≤ A → un21 = A - B) ∧ (A < B → un21 = A + 2^64 - B)
  -- where A = (rhat' % 2^32) * 2^32 + div_un1, B = q1' * dLo.
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
  -- B := q1' * dLo. From cu_q1_dlo's bound, B < 2^64.
  have h_B_lt : q1'.toNat * dLo.toNat < 2^64 := by
    have h_no_wrap : cu_q1_dlo.toNat = q1'.toNat * dLo.toNat :=
      div128Quot_q1_prime_dLo_no_wrap uHi dHi dLo rhatUn1
        hdHi_ge hdLo_lt huHi_lt_vTop
    have := cu_q1_dlo.isLt; omega
  -- Case-split on B ≤ A vs A < B.
  by_cases hBA : q1'.toNat * dLo.toNat ≤
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat
  · -- No-wrap: w = 0.
    refine ⟨0, by omega, ?_⟩
    have h_un21 : un21.toNat =
        (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat - q1'.toNat * dLo.toNat :=
      h_case.1 hBA
    rw [h_un21, h_q1_vtop]; omega
  · -- Wrap: w = 1.
    push Not at hBA
    refine ⟨1, by omega, ?_⟩
    have h_un21 : un21.toNat =
        (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat + 2^64 -
          q1'.toNat * dLo.toNat :=
      h_case.2 hBA
    rw [h_un21, h_q1_vtop]; omega

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
  rw [bv6_toNat_32]
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

/-- **Phase 1 no-wrap invariant for `div128Quot`.**

    Captures the Knuth-C tightening assumption that the Phase 2
    running remainder `un21` is less than `vTop` AND no BitVec
    subtraction wrap occurred. Both follow from the same Knuth-C
    invariant (`q1' ≤ q_true_1` strictly).

    **Important**: this invariant CAN FAIL under just `vTop ≥ 2^63`
    + `hcall` — see `project_kb6d_false_counterexample.md` for a
    concrete numerical example where Phase 1b yields
    `q1' = q_true_1 + 1` (Knuth-C textbook tight case), causing the
    BitVec subtraction to wrap.

    Used as an explicit hypothesis on KB-6c
    (`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`) and KB-6d
    (`div128Quot_le_q_true_plus_two`), making them CONDITIONAL
    theorems. Callers must discharge this from runtime invariants of
    the surrounding algorithm (e.g., the addback machinery that
    follows the bare `div128Quot` trial computation provides the
    needed guarantee for our specific call patterns).

    Tracked in issue #1337 for an unconditional formulation
    (Knuth's D6 addback step would be one path). -/
def Div128PhaseNoWrapInv (uHi uLo vTop : Word) : Prop :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un1 := uLo >>> (32 : BitVec 6).toNat
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
  un21.toNat < dHi.toNat * 2^32 + dLo.toNat ∧
  q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat

/-- **KB-6c-aux1: pure-Nat assembly identity for Phase 2b + KB-3m.**

    Pure Nat algebra. Composes Phase 2b post
    `q0'*dHi + rhat2' = un21` with KB-3m additive identity
    `un21 + r1*2^64 + q1'*vTop = uHi*2^32 + div_un1` and the
    decompositions `vTop = dHi*2^32 + dLo`, `uLo = div_un1*2^32 + div_un0`.

    Multiplying KB-3m by 2^32 and substituting Phase 2b post yields:
    ```
    (q1'*2^32 + q0')*vTop + rhat2'*2^32 + r1*2^96 + div_un0
      = uHi*2^64 + uLo + q0'*dLo
    ```

    Used in KB-6c to relate `(q1'*2^32 + q0')*vTop` to `(uHi*2^64 + uLo)`
    modulo a bounded correction. Note: Phase 1b post (`q1'*dHi + rhat' = uHi`)
    is NOT needed here since `rhat'` cancels out via the identity — `r1`
    plays the role of the wrap-around `rhat'/2^32` directly. -/
theorem div128Quot_kb6c_assembly_identity
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * vTop + rhat2' * 2^32 + r1 * 2^96 + div_un0 =
      uHi * 2^64 + uLo + q0' * dLo := by
  subst h_vTop h_uLo
  -- Substitute h_phase2b: un21 = q0'*dHi + rhat2'.
  rw [show un21 = q0' * dHi + rhat2' from h_phase2b.symm] at h_kb3m
  -- h_kb3m: q0'*dHi + rhat2' + r1*2^64 + q1'*(dHi*2^32+dLo) = uHi*2^32 + div_un1.
  -- Multiply by 2^32 and rearrange.
  have h_kb3m_scaled :
      (q0' * dHi + rhat2' + r1 * 2^64 + q1' * (dHi * 2^32 + dLo)) * 2^32 =
      (uHi * 2^32 + div_un1) * 2^32 := by
    rw [h_kb3m]
  -- Pure ring arithmetic from here; the LHS_goal - RHS_goal = 2^32 * (h_kb3m_scaled).
  have h_pow : (2^32 : Nat) * 2^32 = 2^64 := by decide
  have h_pow2 : (2^32 : Nat) * 2^64 = 2^96 := by decide
  have h_pow3 : (2^32 : Nat) * 2^32 * 2^32 = 2^96 := by decide
  -- Expand both sides via ring lemmas, then linarith for cancellation.
  nlinarith [h_kb3m_scaled, sq_nonneg (q1' : Nat), sq_nonneg (q0' : Nat),
             Nat.zero_le rhat2', Nat.zero_le r1, Nat.zero_le div_un0,
             Nat.zero_le dHi, Nat.zero_le dLo, Nat.zero_le div_un1]

/-- **KB-6c-aux2: drop non-negative correction terms from KB-6c-aux1.**

    From the KB-6c assembly identity, dropping the non-negative
    correction terms `rhat2'*2^32 + r1*2^96 + div_un0` yields the
    inequality:
    ```
    (q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo + q0'*dLo
    ```

    Pure Nat algebra; trivial from KB-6c-aux1 + `Nat.le.intro`. -/
theorem div128Quot_kb6c_assembly_inequality
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0) :
    (q1' * 2^32 + q0') * vTop ≤ uHi * 2^64 + uLo + q0' * dLo := by
  have h_id := div128Quot_kb6c_assembly_identity q1' q0' rhat2' un21 uHi uLo
    vTop dHi dLo div_un1 div_un0 r1 h_phase2b h_kb3m h_vTop h_uLo
  omega

/-- **KB-6c-aux3: from `X*v ≤ Y + 2*v` derive `X ≤ Y/v + 2`.**

    Pure Nat division lemma. Used to convert the KB-6c-aux2 inequality
    (after bounding `q0'*dLo ≤ 2*vTop`) into the final
    `q1'*2^32 + q0' ≤ q_true + 2` form. -/
theorem Nat_le_div_add_two_of_mul_le
    (X Y v : Nat) (hv : 0 < v)
    (h : X * v ≤ Y + 2 * v) :
    X ≤ Y / v + 2 := by
  by_cases hX : X ≤ 2
  · have h1 : 0 ≤ Y / v := Nat.zero_le _
    omega
  · push Not at hX
    -- X ≥ 3, so X - 2 ≥ 1. Subtract 2*v from both sides of h.
    have hX_sub : (X - 2) * v ≤ Y := by
      have h_eq : X = (X - 2) + 2 := by omega
      have h_split : X * v = (X - 2) * v + 2 * v := by
        conv_lhs => rw [h_eq]
        rw [Nat.add_mul]
      linarith
    have h_div : X - 2 ≤ Y / v := (Nat.le_div_iff_mul_le hv).mpr hX_sub
    omega

/-- **KB-6c-aux4: `q0' * dLo ≤ 2 * vTop` under normalization.**

    Pure Nat arithmetic. Under the standard div128Quot preconditions:
    - `q0' < 2^32` (KB-6b under un21 < vTop).
    - `dLo < 2^32` (definition).
    - `vTop ≥ 2^63` (normalization).

    We have `q0' * dLo < 2^32 * 2^32 = 2^64 ≤ 2 * 2^63 ≤ 2 * vTop`.
    Used in KB-6c to convert `(q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo
    + q0'*dLo` into the form needed for `Nat_le_div_add_two_of_mul_le`. -/
theorem div128Quot_kb6c_q0_dLo_bound
    (q0' dLo vTop : Nat)
    (hq0' : q0' < 2^32)
    (hdLo : dLo < 2^32)
    (hvTop : vTop ≥ 2^63) :
    q0' * dLo ≤ 2 * vTop := by
  have h1 : q0' * dLo ≤ (2^32 - 1) * (2^32 - 1) := by
    apply Nat.mul_le_mul <;> omega
  have h2 : (2^32 - 1) * (2^32 - 1) ≤ 2 * 2^63 := by decide
  have h3 : 2 * 2^63 ≤ 2 * vTop := by omega
  omega

/-- **KB-6c-pure-nat: pure-Nat KB-6c quotient assembly bound.**

    Composes KB-6c-aux1 (assembly identity), KB-6c-aux2 (drop
    corrections), KB-6c-aux4 (q0'*dLo ≤ 2*vTop), and the
    Nat division step (`Nat_le_div_add_two_of_mul_le`):

    ```
    q1' * 2^32 + q0' ≤ (uHi * 2^64 + uLo) / vTop + 2
    ```

    All hypotheses are pure-Nat. The algorithm-level KB-6c
    (`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`) becomes a
    one-step application of this lemma, after extracting the relevant
    Nat values from the algorithm's let-chain and discharging
    h_phase2b/h_kb3m/h_vTop/h_uLo/hq0' from the existing infrastructure
    (Phase 2b post, KB-3m, KB-3k, uLo decomposition, KB-6b). -/
theorem div128Quot_kb6c_pure_nat
    (q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1 : Nat)
    (h_phase2b : q0' * dHi + rhat2' = un21)
    (h_kb3m : un21 + r1 * 2^64 + q1' * vTop = uHi * 2^32 + div_un1)
    (h_vTop : vTop = dHi * 2^32 + dLo)
    (h_uLo : uLo = div_un1 * 2^32 + div_un0)
    (hq0' : q0' < 2^32)
    (hdLo : dLo < 2^32)
    (hvTopNorm : vTop ≥ 2^63) :
    q1' * 2^32 + q0' ≤ (uHi * 2^64 + uLo) / vTop + 2 := by
  have h_ineq := div128Quot_kb6c_assembly_inequality
    q1' q0' rhat2' un21 uHi uLo vTop dHi dLo div_un1 div_un0 r1
    h_phase2b h_kb3m h_vTop h_uLo
  have h_q0_dLo := div128Quot_kb6c_q0_dLo_bound q0' dLo vTop hq0' hdLo hvTopNorm
  have h_combined :
      (q1' * 2^32 + q0') * vTop ≤ uHi * 2^64 + uLo + 2 * vTop := by omega
  have hvTop_pos : 0 < vTop := by omega
  exact Nat_le_div_add_two_of_mul_le _ _ _ hvTop_pos h_combined

/-- **KB-6c: Quotient assembly upper bound (STUB).**

    The Nat-level composition of Phase 1b and Phase 2b quotient bounds:

    ```
    q1'.toNat * 2^32 + q0'.toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2
    ```

    **Proof outline** (sub-decomposition):
    - **`div128Quot_kb6c_assembly_identity`** (CLOSED, pure Nat): the
      algebraic identity `(q1'*2^32 + q0')*vTop + correction =
      uHi*2^64 + uLo + q0'*dLo` from the three Euclideans + decomps.
    - From this, derive `(q1'*2^32 + q0')*vTop ≤ uHi*2^64 + uLo + q0'*dLo`
      (drop non-negative correction terms).
    - Bound `q0'*dLo ≤ 2*vTop` via Knuth-B: q0' ≤ 2^32 (KB-6b), dLo < 2^32,
      so q0'*dLo < 2^64 ≤ 2*vTop (under vTop ≥ 2^63).
    - Use Nat-division: from `X*vTop ≤ Y + 2*vTop`, get `X ≤ Y/vTop + 2`.

    Equivalent to **Knuth Theorem B for the assembled 64-bit quotient**,
    instantiated to our algorithm's specific control flow. Tracked in
    issue #1337. -/
theorem div128Quot_q1_prime_q0_prime_le_q_true_plus_two
    (uHi uLo vTop : Word)
    (hvTop_norm : vTop.toNat ≥ 2^63)
    (hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64)
    (h_inv : Div128PhaseNoWrapInv uHi uLo vTop) :
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
    q1'.toNat * 2^32 + q0'.toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2 := by
  intro dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
        cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0'
  -- (Mirror KB-6d's preconditions derivation.)
  have h_vtop := div128Quot_vTop_decomp vTop
  simp only [] at h_vtop
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : vTop.toNat ≥ 2^63 := hvTop_norm
    have : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have hdHi_lt : dHi.toNat < 2^32 := by
    show (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h := vTop.isLt; omega
  have hdLo_lt : dLo.toNat < 2^32 := by
    show ((vTop <<< (32 : BitVec 6).toNat) >>>
          (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    have h_mod : (vTop.toNat * 2^(32 : BitVec 6).toNat) % 2^64 < 2^64 :=
      Nat.mod_lt _ (by norm_num)
    omega
  have h_uHi_lt_vTop_raw : uHi.toNat < vTop.toNat := by
    by_contra h; push Not at h
    have : vTop.toNat * 2^64 ≤ uHi.toNat * 2^64 := Nat.mul_le_mul_right _ h
    have huLo := uLo.isLt
    have : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := hcall
    omega
  have huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vtop]; exact h_uHi_lt_vTop_raw
  -- Apply Knuth-C invariant (now an EXPLICIT HYPOTHESIS h_inv).
  simp only [Div128PhaseNoWrapInv] at h_inv
  obtain ⟨h_un21_lt, h_no_wrap⟩ := h_inv
  -- Discharge h_kb3m via KB-3m + no-wrap conjunct.
  have h_kb3m_partial :=
    div128Quot_un21_additive_identity uHi dHi dLo uLo vTop rhatUn1
      hdHi_ge hdLo_lt huHi_lt_vTop rfl rfl
  simp only [] at h_kb3m_partial
  have h_kb3m : un21.toNat + (rhat'.toNat / 2^32) * 2^64 +
      q1'.toNat * vTop.toNat = uHi.toNat * 2^32 + div_un1.toNat :=
    h_kb3m_partial h_no_wrap
  -- Discharge h_phase2b via Phase 2b post.
  have hdHi_ne : dHi ≠ 0 := by
    intro heq; rw [heq] at hdHi_ge; simp at hdHi_ge
  have h_post_phase2a :=
    div128Quot_first_round_post un21 dHi hdHi_ne hdHi_lt
  simp only [] at h_post_phase2a
  have h_rhat2c_bound :=
    div128Quot_rhatc_lt_2dHi un21 dHi hdHi_ne hdHi_lt
  simp only [] at h_rhat2c_bound
  have h_phase2b_full :=
    @div128Quot_phase2b_post div_un0 un21 dHi hdHi_lt q0c rhat2c dLo
      h_post_phase2a h_rhat2c_bound
  simp only [] at h_phase2b_full
  -- h_phase2b_full conclusion uses an `if`-guarded rhat2'; need just q0' part.
  -- The Euclidean form `q0'*dHi + rhat2'_some = un21` for some rhat2'.
  -- Set rhat2'_used as the if-guarded value from h_phase2b_full's let.
  set rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat with hrhat2cHi_def
  set rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0 with hrhat2Un0_def
  let rhat2'_used : Word :=
    if rhat2cHi = 0 then
      (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
    else rhat2c
  have h_phase2b : q0'.toNat * dHi.toNat + rhat2'_used.toNat = un21.toNat :=
    h_phase2b_full
  -- Discharge hq0' < 2^32 via KB-6b.
  have h_q0'_lt :=
    div128Quot_q0_prime_lt_pow32 _ _ _ uLo hdHi_ge hdHi_lt hdLo_lt h_un21_lt
  simp only [] at h_q0'_lt
  -- uLo decomposition.
  have h_uLo : uLo.toNat = div_un1.toNat * 2^32 + div_un0.toNat := by
    show uLo.toNat = (uLo >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
        BitVec.toNat_shiftLeft, bv6_toNat_32]
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have h_lo : uLo.toNat * 2^32 % 2^64 / 2^32 = uLo.toNat % 2^32 := by
      have := uLo.isLt; omega
    rw [h_lo]
    have := Nat.div_add_mod uLo.toNat (2^32)
    omega
  -- Apply pure-Nat KB-6c.
  exact div128Quot_kb6c_pure_nat
    q1'.toNat q0'.toNat rhat2'_used.toNat un21.toNat
    uHi.toNat uLo.toNat vTop.toNat dHi.toNat dLo.toNat
    div_un1.toNat div_un0.toNat (rhat'.toNat / 2^32)
    h_phase2b h_kb3m h_vtop h_uLo h_q0'_lt hdLo_lt hvTop_norm

/-- **KB-6d: `div128Quot` upper bound (Knuth Theorem B at div128Quot level).**

    The user-facing closing theorem of Knuth Theorem B for `div128Quot`:

    ```
    (div128Quot uHi uLo vTop).toNat ≤ (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2
    ```

    under standard preconditions:
    - `vTop.toNat ≥ 2^63` (normalized divisor — top bit set).
    - `uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64` (no-overflow / call-path:
      the dividend fits in a single 64-bit quotient digit's range times `2^64`).

    This is the bound that downstream call-trial DIV/MOD stack specs need
    to reason about the at-most-2-addback correction chain.

    **Composition** (sub-stubs separated for tractable proof attempts):
    1. **`div128Quot_un21_lt_vTop`** (STUB, Knuth-C): `un21 < vTop`.
    2. **`div128Quot_q0_prime_lt_pow32`** (KB-6b, CLOSED): under `un21 < vTop`,
       `q0' < 2^32`.
    3. **`div128Quot_toNat_eq_strict`** (KB-6a strict, CLOSED): under `q0' < 2^32`,
       `div128Quot.toNat = q1'.toNat * 2^32 + q0'.toNat`.
    4. **`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`** (KB-6c, STUB):
       `q1' * 2^32 + q0' ≤ q_true + 2`.

    The composition itself is a mechanical chain of `have`s once the
    two stubs above are filled. The hard math is isolated in those two
    stubs:
    - **`div128Quot_un21_lt_vTop`** (Knuth-C, ~300-400 lines).
    - **`div128Quot_q1_prime_q0_prime_le_q_true_plus_two`** (KB-6c Nat
      assembly, ~80-150 lines).

    Tracked in issue #1337. -/
theorem div128Quot_le_q_true_plus_two (uHi uLo vTop : Word)
    (hvTop_norm : vTop.toNat ≥ 2^63)
    (hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64)
    (h_inv : Div128PhaseNoWrapInv uHi uLo vTop) :
    (div128Quot uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 2 := by
  -- Step 0: derive intermediate preconditions from hvTop_norm + hcall.
  -- vTop = dHi * 2^32 + dLo  (KB-3k, unconditional).
  have h_vtop := div128Quot_vTop_decomp vTop
  simp only [] at h_vtop
  -- hdHi_ge: dHi ≥ 2^31  (from vTop ≥ 2^63 + decomp + dLo < 2^32).
  have hdHi_ge : (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h1 : vTop.toNat ≥ 2^63 := hvTop_norm
    have h2 : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  -- hdHi_lt: dHi < 2^32  (from vTop < 2^64).
  have hdHi_lt : (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h := vTop.isLt
    omega
  -- hdLo_lt: dLo < 2^32  (mod-2^32 of a Nat).
  have hdLo_lt : ((vTop <<< (32 : BitVec 6).toNat) >>>
                  (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, bv6_toNat_32, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_shiftLeft]
    have h_mod : (vTop.toNat * 2^(32 : BitVec 6).toNat) % 2^64 < 2^64 :=
      Nat.mod_lt _ (by norm_num)
    omega
  -- huHi_lt_vTop: uHi < vTop  (from hcall + uLo ≥ 0; written via dHi*2^32+dLo).
  have h_uHi_lt_vTop_raw : uHi.toNat < vTop.toNat := by
    by_contra h
    push Not at h
    have : vTop.toNat * 2^64 ≤ uHi.toNat * 2^64 := Nat.mul_le_mul_right _ h
    have huLo := uLo.isLt
    have : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := hcall
    omega
  have huHi_lt_vTop : uHi.toNat <
      (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_vtop]; exact h_uHi_lt_vTop_raw
  -- Step 1: extract un21 < vTop ∧ no-wrap from explicit hypothesis.
  have h_inv_unfolded := h_inv
  simp only [Div128PhaseNoWrapInv] at h_inv_unfolded
  have h_un21_lt := h_inv_unfolded.1
  -- Step 2: q0' < 2^32  (KB-6b, CLOSED, requires un21 < vTop).
  have h_q0'_lt :=
    div128Quot_q0_prime_lt_pow32 _ _ _ uLo hdHi_ge hdHi_lt hdLo_lt h_un21_lt
  simp only [] at h_q0'_lt
  -- Step 3: div128Quot.toNat = q1'.toNat * 2^32 + q0'.toNat  (KB-6a strict, CLOSED).
  have h_eq :=
    div128Quot_toNat_eq_strict uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop
  simp only [] at h_eq
  -- Step 4: q1'.toNat * 2^32 + q0'.toNat ≤ q_true + 2  (KB-6c, conditional).
  have h_assemble :=
    div128Quot_q1_prime_q0_prime_le_q_true_plus_two uHi uLo vTop
      hvTop_norm hcall h_inv
  simp only [] at h_assemble
  -- Step 5: combine.
  rw [h_eq h_q0'_lt]
  exact h_assemble

end EvmAsm.Evm64
