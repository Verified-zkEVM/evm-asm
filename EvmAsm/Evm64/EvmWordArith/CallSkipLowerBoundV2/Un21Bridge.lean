/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Un21Bridge

  The Word↔Nat bridge for `algorithmUn21` — the un21 sub-case decomposition
  (`_of_tight`, `_plus_one`, `_eq_r1_math_of_tight`) and the wrapper
  `algorithmUn21_ge_r1_math` used by §A2.S1. Extracted from
  `CallSkipLowerBoundV2.lean` for file-size hygiene.

  ## Contents

  - **Layer 1 (Word→Nat formulas)**:
      - `algorithmUn21_L1a_cu_rhat_un1_toNat`
      - `algorithmUn21_L1b_q1_prime_dLo_no_wrap`
      - `algorithmUn21_L1c_un21_toNat_case_simple`
  - **Layer 2 (Phase 1b invariants)**:
      - `algorithmUn21_L2a_phase1b_euclidean_at_u4`
  - **Layer 3 (pure-Nat Euclidean)**:
      - `algorithmUn21_L3a_u_decomp_via_vTop`
      - `algorithmUn21_L3b_q_true_1_V_le_u`
  - **`_of_tight` cases (L5)**:
      - `algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1`  (sorry — Layer 4 algebra)
      - `algorithmUn21_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one`  (sorry)
  - **Bridge sub-B** (algebraic consequence): `algorithmUn21_eq_r1_math_of_tight`
  - **Wrapper for §A2.S1**: `algorithmUn21_ge_r1_math`

  See `memory/project_of_tight_decomp_plan.md` for the layered decomposition plan.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.QuotientBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **_of_tight sub-case "exact" L1.a**: cu_rhat_un1.toNat formula via
    halfword_combine_mod. ~10 lines. -/
theorem algorithmUn21_L1a_cu_rhat_un1_toNat
    (u4 u3 b3' : Word) :
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := by
  intro dHi div_un1 q1 rhat hi1 q1c rhatc dLo qDlo rhatUn1 q1' rhat'
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
  exact halfword_combine_mod _ _ h_div_un1_lt

/-- **_of_tight sub-case "exact" L1.b**: q1' * dLo no-wrap. Wraps
    `div128Quot_q1_prime_dLo_no_wrap`. ~10 lines. -/
theorem algorithmUn21_L1b_q1_prime_dLo_no_wrap
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat) :
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
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    (q1' * dLo).toNat = q1'.toNat * dLo.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1'
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    show ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_v_eq : b3'.toNat = dHi.toNat * 2^32 + dLo.toNat :=
    div128Quot_vTop_decomp b3'
  have h_uHi_lt_vTop : u4.toNat < dHi.toNat * 2^32 + dLo.toNat := h_v_eq ▸ hu4_lt_b3'
  exact div128Quot_q1_prime_dLo_no_wrap u4 dHi dLo rhatUn1 h_dHi_ge h_dLo_lt h_uHi_lt_vTop

/-- **_of_tight sub-case "exact" L3.a**: pure-Nat Euclidean decomposition for
    `u4*2^32 + div_un1` divided by `V` (= `b3'.toNat`). Direct from
    `Nat.div_add_mod`. ~3 lines. -/
theorem algorithmUn21_L3a_u_decomp_via_vTop
    (u : Nat) (V : Nat) :
    (u / V) * V + u % V = u := by
  rw [Nat.mul_comm]; exact Nat.div_add_mod u V

/-- **_of_tight sub-case "exact" L3.b**: `q_true_1 * V ≤ u`. Trivial from
    L3.a. ~3 lines. -/
theorem algorithmUn21_L3b_q_true_1_V_le_u
    (u : Nat) (V : Nat) :
    (u / V) * V ≤ u := by
  exact Nat.div_mul_le_self u V

/-- **L4 helper**: pure-Nat algebraic identity for halfword decomposition.
    `(rhat % 2^32) * 2^32 + (rhat / 2^32) * 2^64 = rhat * 2^32`. -/
theorem algorithmUn21_L4_halfword_combine (rhat : Nat) :
    (rhat % 2^32) * 2^32 + (rhat / 2^32) * 2^64 = rhat * 2^32 := by
  have h_decomp : (rhat / 2^32) * 2^32 + rhat % 2^32 = rhat := by
    have := Nat.div_add_mod rhat (2^32); omega
  have h_pow_eq : (rhat / 2^32) * 2^64 = (rhat / 2^32) * 2^32 * 2^32 := by
    have h64 : (2^64 : Nat) = 2^32 * 2^32 := by decide
    rw [h64]; ring
  rw [h_pow_eq]
  rw [show (rhat % 2^32) * 2^32 + (rhat / 2^32) * 2^32 * 2^32 =
      ((rhat / 2^32) * 2^32 + rhat % 2^32) * 2^32 from by ring]
  rw [h_decomp]

/-- **_of_tight sub-case "exact" L4** (pure-Nat modular identity): the core
    arithmetic claim used by L5. Given the standard preconditions
    (u = u4*2^32 + div_un1, V = dHi*2^32 + dLo, q*dHi + rhat = u4, etc.),
    the modular subtraction `(2^64 - q*dLo + (rhat % 2^32)*2^32 + div_un1) % 2^64`
    equals `u % V`.

    **Why this works** (without needing rhat < 2^32):
    - Let r := u % V = u - q*V = (u4 - q*dHi)*2^32 + div_un1 - q*dLo = rhat*2^32 + div_un1 - q*dLo.
    - When rhat ≥ 2^32: rhat % 2^32 = rhat - (rhat/2^32) * 2^32, so
      `(rhat % 2^32) * 2^32 = rhat * 2^32 - (rhat/2^32) * 2^64`.
      The `(rhat/2^32) * 2^64` term cancels modulo 2^64 with the `2^64`
      offset, leaving `r mod 2^64 = r` (since r < V < 2^64).
    - When rhat < 2^32: identity is direct.

    Now also requires `rhat < 2^33` which is satisfied in our usage by
    `div128Quot_rhat_prime_lt_3dHi` + narrow-u4 (rhat' < 2 * 2^32 in case
    (ii); = rhatc < 2^32 in case (i)). This bound restricts `rhat / 2^32`
    to {0, 1}, the two cases needed for the modular identity.

    **Proof outline** (~60 lines, in progress):
    1. Decompose: rhat = (rhat / 2^32) * 2^32 + rhat % 2^32 with quotient ≤ 1.
    2. Establish q is the integer quotient: r := u % V = u - q*V is well-defined.
    3. Rewrite r = rhat*2^32 + div_un1 - q*dLo (via h_eucl).
    4. Case-split on rhat / 2^32:
       - h = 0: LHS = (2^64 + r) % 2^64 = r.
       - h = 1: rhat*2^32 ≥ 2^64, LHS = r % 2^64 = r.
    -/
theorem algorithmUn21_L4_modular_identity
    (u4 div_un1 dHi dLo q rhat : Nat)
    (hdiv_un1_lt : div_un1 < 2^32)
    (hdLo_lt : dLo < 2^32)
    (hrhat_lt : rhat < 2^33)
    (hV_lt : dHi * 2^32 + dLo < 2^64)
    (h_eucl : q * dHi + rhat = u4)
    (h_q_dLo_no_wrap : q * dLo < 2^64)
    (h_q_V_le : q * (dHi * 2^32 + dLo) ≤ u4 * 2^32 + div_un1)
    (h_r_lt_V : (u4 * 2^32 + div_un1) - q * (dHi * 2^32 + dLo) < dHi * 2^32 + dLo) :
    (2^64 - q * dLo + (rhat % 2^32) * 2^32 + div_un1) % 2^64 =
      (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) := by
  -- Proof attempt encountered maxRecDepth on omega/linarith with large constants
  -- (2^32, 2^64). Need to decompose into smaller helper lemmas with `set` aliases
  -- for the powers to keep terms small. See PR #1289 commit history.
  sorry

/-- **_of_tight sub-case "exact" L2.a**: Phase 1b Euclidean invariant at u4.
    Wraps `div128Quot_phase1b_post`. After Phase 1b, the corrected pair
    `(q1', rhat')` satisfies `q1'.toNat * dHi.toNat + rhat'.toNat = u4.toNat`. -/
theorem algorithmUn21_L2a_phase1b_euclidean_at_u4
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63) :
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
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    q1'.toNat * dHi.toNat + rhat'.toNat = u4.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat'
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_dHi_ne : dHi ≠ 0 := by
    intro heq
    have h : (b3' >>> (32 : BitVec 6).toNat).toNat = 0 := by
      change dHi.toNat = 0; rw [heq]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h
    have : b3'.toNat ≥ 2^63 := hb3'_ge
    omega
  have h_post : q1c.toNat * dHi.toNat + rhatc.toNat = u4.toNat :=
    div128Quot_first_round_post u4 dHi h_dHi_ne h_dHi_lt
  have h_rhatc_lt : rhatc.toNat < 2 * dHi.toNat :=
    div128Quot_rhatc_lt_2dHi u4 dHi h_dHi_ne h_dHi_lt
  exact div128Quot_phase1b_post u4 dHi q1c rhatc dLo rhatUn1 h_dHi_lt h_post h_rhatc_lt

/-- **_of_tight sub-case "exact" L1.c**: word-level subtraction unfolds via
    `BitVec.toNat_sub`. `algorithmUn21 = cu_rhat_un1 - cu_q1_dlo` directly,
    so `un21.toNat = (2^64 - cu_q1_dlo.toNat + cu_rhat_un1.toNat) % 2^64`. -/
theorem algorithmUn21_L1c_un21_toNat_case_simple (u4 u3 b3' : Word) :
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
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    (algorithmUn21 u4 u3 b3').toNat =
      (2^64 - cu_q1_dlo.toNat + cu_rhat_un1.toNat) % 2^64 := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo
  rw [algorithmUn21_unfold]
  exact BitVec.toNat_sub _ _

/-- **_of_tight sub-case "exact"**: when `q1' = q_true_1` (Phase 1b exactly
    tight), the algorithm's un21 equals the mathematical remainder r1_math.

    **Decomposition** (per `project_of_tight_decomp_plan.md`): 5 layers
    L1 (Word-Nat formulas), L2 (Phase 1b invariants), L3 (quotient
    relationships), L4 (no-wrap), L5 (compose). Layer 1 stubs above. -/
theorem algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_prime_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat) :
    (algorithmUn21 u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  -- Setup standard preconditions.
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  -- Apply KB-3m (un21 additive identity) with rhatUn1 as the actual one.
  -- We need: un21 + (rhat'/2^32) * 2^64 + q1' * vTop = u4*2^32 + div_un1
  -- under no-wrap B ≤ A.
  -- Strategy: show no-wrap via contradiction (if wrap, Word bound violated).
  -- This requires considerable Word analysis; deferred.
  sorry

/-- **_of_tight sub-case "off-by-one"**: when `q1' = q_true_1 + 1` (Phase 1b
    false-alarms once), the algorithm's un21 = r1_math + (2^64 - V), which is
    ≥ r1_math.

    **TODO** (~40 lines): from Phase 1b Euclidean + Word wrap analysis. -/
theorem algorithmUn21_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_prime_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1) :
    (algorithmUn21 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  sorry

/-- **Bridge sub-B** (algebraic consequence): given `q1' ≤ q_true_1 + 1` and
    `un21 < dHi*2^32`, the algorithm's un21 cannot be less than `r1_math`. -/
theorem algorithmUn21_eq_r1_math_of_tight
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_tight :
      (algorithmUn21 u4 u3 b3').toNat <
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat) :
    False := by
  -- Derive q1' ∈ {q_true_1, q_true_1 + 1}.
  have h_q1_le := algorithmQ1Prime_le_q_true_1_plus_one u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  -- Lower bound: q1' ≥ q_true_1 (wrapped form). Need to establish.
  have h_q1_ge : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
      ≤ (algorithmQ1Prime u4 u3 b3').toNat := by
    -- Use algorithmQ1Prime_ge_q_true_1 (already proven) + dHi bounds derivation.
    have h_dHi_ge : (b3' >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
    have h_dHi_lt : (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : b3'.toNat < 2^64 := b3'.isLt
      exact Nat.div_lt_of_lt_mul (by omega)
    have h_dLo_lt :
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
        (b3' <<< (32 : BitVec 6).toNat : Word).isLt
      exact Nat.div_lt_of_lt_mul (by omega)
    have h_v_eq := div128Quot_vTop_decomp b3'
    have h_u4_lt_vTop : u4.toNat <
        (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
      h_v_eq ▸ hu4_lt_b3'
    have h := algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
      h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt_dHi_pow32 h_u4_lt_vTop
    rw [← h_v_eq] at h; exact h
  -- q1' is q_true_1 or q_true_1 + 1.
  set q_true_1 := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat
  have h_q1'_or : (algorithmQ1Prime u4 u3 b3').toNat = q_true_1 ∨
                  (algorithmQ1Prime u4 u3 b3').toNat = q_true_1 + 1 := by
    omega
  rcases h_q1'_or with h_eq | h_eq_plus_one
  · -- Case q1' = q_true_1: un21 = r1_math. Contradicts h_tight.
    have h_un21_eq := algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1 u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_eq
    omega
  · -- Case q1' = q_true_1 + 1: un21 ≥ r1_math. Contradicts h_tight.
    have h_un21_ge := algorithmUn21_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_eq_plus_one
    omega

/-- **Bridge**: under standard hcall + `un21 < dHi*2^32`, the algorithm's un21
    is at least the mathematical remainder `(u4*2^32 + div_un1) % b3'`.

    Composes via `by_contra` + the `algorithmUn21_eq_r1_math_of_tight`
    structural impossibility of un21 < r1_math (under hcall + un21 < dHi*2^32,
    Phase 1b's ult correction guarantees un21 ≥ r1_math — if
    un21 < r1_math held, Phase 1b would have undercorrected, contradicting
    its design).

    **TODO** (~80 lines in the sub-lemma): formalize via KB-3j (un21 wrap
    case split) + Phase 1b ult-check semantics. -/
theorem algorithmUn21_ge_r1_math
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_lt_dHi_pow32 :
      (algorithmUn21 u4 u3 b3').toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (algorithmUn21 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  by_contra h_lt
  push Not at h_lt
  exact algorithmUn21_eq_r1_math_of_tight u4 u3 b3' hb3'_ge hu4_lt_b3'
    hu4_lt_dHi_pow32 h_un21_lt_dHi_pow32 h_lt


end EvmAsm.Evm64
