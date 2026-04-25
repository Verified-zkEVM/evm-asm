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
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    ((rhat' <<< (32 : BitVec 6).toNat) ||| div_un1).toNat =
      (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := by
  intro dHi div_un1 q1 rhat hi1 q1c rhatc dLo qDlo rhatUn1 rhat'
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

/-- **L5_plus_one helper**: pure-Nat — for q := u/V with V > 0, we have
    `(q+1) * V > u`. Used to discharge the L4_plus_one h_q_V_gt hypothesis in
    the off-by-one composition (omega alone can't see this distributivity). -/
theorem algorithmUn21_L5_succ_mul_div_gt (u V : Nat) (hV_pos : 0 < V) :
    (u / V + 1) * V > u := by
  have h_dam := Nat.div_add_mod u V
  have h_mod_lt := Nat.mod_lt u hV_pos
  have h_expand : (u / V + 1) * V = V * (u / V) + V := by ring
  linarith

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

/-- **L4 helper**: pure-Nat — under the standard preconditions, `q*dLo` is
    bounded by `rhat*2^32 + div_un1`. This is the no-wrap precondition for
    the `2^64 - q*dLo` subtraction in L4's LHS to be meaningful Nat-wise.

    Direct from h_q_V_le + h_eucl. -/
theorem algorithmUn21_L4_qdLo_le_rhat_div_un1
    (u4 div_un1 dHi dLo q rhat : Nat)
    (h_eucl : q * dHi + rhat = u4)
    (h_q_V_le : q * (dHi * 2^32 + dLo) ≤ u4 * 2^32 + div_un1) :
    q * dLo ≤ rhat * 2^32 + div_un1 := by
  have h_u_mul : u4 * 2^32 = q * dHi * 2^32 + rhat * 2^32 := by
    have h1 : (q * dHi + rhat) * 2^32 = u4 * 2^32 := by rw [h_eucl]
    linarith [h1, Nat.add_mul (q * dHi) rhat (2^32)]
  have h_qV_expand : q * (dHi * 2^32 + dLo) = q * dHi * 2^32 + q * dLo := by ring
  linarith [h_q_V_le, h_qV_expand, h_u_mul]

/-- **L4_plus_one helper**: pure-Nat algebraic identity for the off-by-one case.
    When q is one more than the true quotient (so q*V > u, but (q-1)*V ≤ u),
    the relation `q*dLo = rhat*2^32 + div_un1 + V - r` holds, where
    `V = dHi*2^32 + dLo`, `r = u%V`, and `rhat` satisfies `q*dHi + rhat = u4`.

    This is the analog of L4_qdLo_le for the overshoot case. Used to compute
    `2^64 - q*dLo` in the L4_plus_one body. -/
theorem algorithmUn21_L4_qdLo_eq_plus_V_minus_r
    (u4 div_un1 dHi dLo q rhat : Nat)
    (hq_pos : q ≥ 1)
    (hV_pos : dHi * 2^32 + dLo ≥ 1)
    (h_eucl : q * dHi + rhat = u4)
    (h_q_V_gt : q * (dHi * 2^32 + dLo) > u4 * 2^32 + div_un1)
    (h_qm1_V_le : (q - 1) * (dHi * 2^32 + dLo) ≤ u4 * 2^32 + div_un1) :
    q * dLo + (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) =
      rhat * 2^32 + div_un1 + (dHi * 2^32 + dLo) := by
  -- Set V := dHi*2^32 + dLo, u := u4*2^32 + div_un1, r := u % V.
  -- Strategy: from h_eucl, u = q*dHi*2^32 + rhat*2^32 + div_un1.
  -- And q*V = q*dHi*2^32 + q*dLo. So q*V - u = q*dLo - rhat*2^32 - div_un1.
  -- Also r = u - (q-1)*V (from h_qm1_V_le being the unique quotient bound).
  -- So q*V = (q-1)*V + V = u - r + V, giving q*V - u = V - r.
  -- Combining: q*dLo - rhat*2^32 - div_un1 = V - r.
  -- Equivalently: q*dLo + r = rhat*2^32 + div_un1 + V.
  have h_qV : q * (dHi * 2^32 + dLo) = q * dHi * 2^32 + q * dLo := by ring
  have h_u_decomp : u4 * 2^32 + div_un1 = q * dHi * 2^32 + rhat * 2^32 + div_un1 := by
    have h1 : (q * dHi + rhat) * 2^32 = u4 * 2^32 := by rw [h_eucl]
    linarith [h1, Nat.add_mul (q * dHi) rhat (2^32)]
  have h_qm1_eq_div : q - 1 = (u4 * 2^32 + div_un1) / (dHi * 2^32 + dLo) := by
    have h_lt : (u4 * 2^32 + div_un1) / (dHi * 2^32 + dLo) < q :=
      (Nat.div_lt_iff_lt_mul (by linarith [hV_pos])).mpr h_q_V_gt
    have h_le : q - 1 ≤ (u4 * 2^32 + div_un1) / (dHi * 2^32 + dLo) :=
      (Nat.le_div_iff_mul_le (by linarith [hV_pos])).mpr h_qm1_V_le
    omega
  have hr_value : u4 * 2^32 + div_un1 =
      (q - 1) * (dHi * 2^32 + dLo) + (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) := by
    rw [h_qm1_eq_div]
    have h_mod := Nat.div_add_mod (u4 * 2^32 + div_un1) (dHi * 2^32 + dLo)
    linarith [h_mod, Nat.mul_comm (dHi * 2^32 + dLo)
      ((u4 * 2^32 + div_un1) / (dHi * 2^32 + dLo))]
  have h_q_eq_qm1_plus_1 : q = (q - 1) + 1 := by omega
  have h_qV_eq : q * (dHi * 2^32 + dLo) = (q - 1) * (dHi * 2^32 + dLo) + (dHi * 2^32 + dLo) := by
    conv_lhs => rw [h_q_eq_qm1_plus_1]; rw [Nat.add_mul, Nat.one_mul]
  -- From h_qV_eq + hr_value: q*V = u + V - r.
  -- From h_qV: q*V = q*dHi*2^32 + q*dLo.
  -- So q*dHi*2^32 + q*dLo = u + V - r.
  -- And u = q*dHi*2^32 + rhat*2^32 + div_un1.
  -- So q*dHi*2^32 + q*dLo = q*dHi*2^32 + rhat*2^32 + div_un1 + V - r.
  -- Cancel q*dHi*2^32: q*dLo = rhat*2^32 + div_un1 + V - r.
  -- Equivalently: q*dLo + r = rhat*2^32 + div_un1 + V.
  have h_r_lt_V : (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) < dHi * 2^32 + dLo :=
    Nat.mod_lt _ (by linarith [hV_pos])
  linarith [h_qV, h_u_decomp, hr_value, h_qV_eq]

/-- **L4 helper**: pure-Nat — under the standard preconditions,
    `(u4*2^32 + div_un1) % V = rhat*2^32 + div_un1 - q*dLo`.

    Established by showing `u = q*V + (rhat*2^32 + div_un1 - q*dLo)` (a
    direct consequence of h_eucl + the q*dLo no-wrap of L4_qdLo_le helper),
    plus the upper bound `r < V` (= h_r_lt_V hypothesis). -/
theorem algorithmUn21_L4_quotient_remainder
    (u4 div_un1 dHi dLo q rhat : Nat)
    (h_eucl : q * dHi + rhat = u4)
    (h_q_V_le : q * (dHi * 2^32 + dLo) ≤ u4 * 2^32 + div_un1)
    (h_r_lt_V : (u4 * 2^32 + div_un1) - q * (dHi * 2^32 + dLo) < dHi * 2^32 + dLo) :
    (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) = rhat * 2^32 + div_un1 - q * dLo := by
  have h_qdLo_le := algorithmUn21_L4_qdLo_le_rhat_div_un1 u4 div_un1 dHi dLo q rhat
    h_eucl h_q_V_le
  have h_u_mul : u4 * 2^32 = q * dHi * 2^32 + rhat * 2^32 := by
    have h1 : (q * dHi + rhat) * 2^32 = u4 * 2^32 := by rw [h_eucl]
    linarith [h1, Nat.add_mul (q * dHi) rhat (2^32)]
  have h_qV : q * (dHi * 2^32 + dLo) = q * dHi * 2^32 + q * dLo := by ring
  have h_cancel : q * dLo + (rhat * 2^32 + div_un1 - q * dLo) =
      rhat * 2^32 + div_un1 := Nat.add_sub_cancel' h_qdLo_le
  have h_u_decomp : u4 * 2^32 + div_un1 =
      q * (dHi * 2^32 + dLo) + (rhat * 2^32 + div_un1 - q * dLo) := by
    linarith [h_u_mul, h_qV, h_cancel]
  have h_r_lt_V' : rhat * 2^32 + div_un1 - q * dLo < dHi * 2^32 + dLo := by
    have h0 : (u4 * 2^32 + div_un1) - q * (dHi * 2^32 + dLo) < dHi * 2^32 + dLo := h_r_lt_V
    rw [h_u_decomp, Nat.add_sub_cancel_left] at h0
    exact h0
  rw [h_u_decomp]
  rw [show q * (dHi * 2^32 + dLo) + (rhat * 2^32 + div_un1 - q * dLo) =
      (rhat * 2^32 + div_un1 - q * dLo) + (dHi * 2^32 + dLo) * q from by ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h_r_lt_V'

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
    (hV_lt : dHi * 2^32 + dLo < 2^64)
    (h_eucl : q * dHi + rhat = u4)
    (h_q_dLo_no_wrap : q * dLo < 2^64)
    (h_q_V_le : q * (dHi * 2^32 + dLo) ≤ u4 * 2^32 + div_un1)
    (h_r_lt_V : (u4 * 2^32 + div_un1) - q * (dHi * 2^32 + dLo) < dHi * 2^32 + dLo) :
    (2^64 - q * dLo + (rhat % 2^32) * 2^32 + div_un1) % 2^64 =
      (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) := by
  -- Compose three closed L4 helpers to keep the kernel-checked proof small.
  have h_qdLo_le := algorithmUn21_L4_qdLo_le_rhat_div_un1 u4 div_un1 dHi dLo q rhat
    h_eucl h_q_V_le
  have h_r_eq := algorithmUn21_L4_quotient_remainder u4 div_un1 dHi dLo q rhat
    h_eucl h_q_V_le h_r_lt_V
  have h_combine := algorithmUn21_L4_halfword_combine rhat
  -- Define r explicitly.
  rw [h_r_eq]
  -- r < V < 2^64.
  have h_r_lt_V_actual : rhat * 2^32 + div_un1 - q * dLo < dHi * 2^32 + dLo := by
    rw [← h_r_eq]; exact Nat.mod_lt _ (by linarith [hV_lt])
  have h_r_lt_pow : rhat * 2^32 + div_un1 - q * dLo < 2^64 := by linarith
  -- LHS_pre + (rhat/2^32)*2^64 = 2^64 + r.
  have h_lhs_plus_h64 :
      2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1 + (rhat / 2^32) * 2^64 =
      2^64 + (rhat * 2^32 + div_un1 - q * dLo) := by
    have h_reorder :
        2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1 + (rhat / 2^32) * 2^64 =
        2^64 - q * dLo + (rhat % 2^32 * 2^32 + (rhat / 2^32) * 2^64) + div_un1 := by linarith
    rw [h_reorder, h_combine]
    have hq_le_64 : q * dLo ≤ 2^64 := le_of_lt h_q_dLo_no_wrap
    omega
  -- (LHS_pre + (rhat/2^32)*2^64) % 2^64 = LHS_pre % 2^64.
  have h_mod_eq :
      (2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1) % 2^64 =
      (2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1 + (rhat / 2^32) * 2^64) % 2^64 :=
    (Nat.add_mul_mod_self_right _ _ _).symm
  rw [h_mod_eq, h_lhs_plus_h64]
  rw [show 2^64 + (rhat * 2^32 + div_un1 - q * dLo) =
      (rhat * 2^32 + div_un1 - q * dLo) + 2^64 from by ring]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h_r_lt_pow

/-- **_plus_one case L4** (pure-Nat, off-by-one variant): when `q = q_true + 1`
    (so q*V > u), the algorithmUn21-style modular subtraction wraps around
    and yields `2^64 + r - V` instead of `r`.

    Concretely: under the same shape preconditions as L4 except
    - `q*V > u4*2^32 + div_un1` (overshoot, NOT the standard `q*V ≤ u`),
    - `(q-1)*V ≤ u4*2^32 + div_un1` (so `q-1` is the true quotient),

    we have:
    `(2^64 - q*dLo + (rhat%2^32)*2^32 + div_un1) % 2^64 = 2^64 + r - V`
    where `r := (u4*2^32 + div_un1) % V` and `V := dHi*2^32 + dLo`.

    From this, `algorithmUn21.toNat = 2^64 + r - V ≥ r` (since 2^64 ≥ V),
    which is what `_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one` needs.

    Stubbed for now; the proof structure parallels L4 but with sign-flipped
    case analysis (cu_rhat_un1 < cu_q1_dlo, Word-wrap occurs). -/
theorem algorithmUn21_L4_modular_identity_plus_one
    (u4 div_un1 dHi dLo q rhat : Nat)
    (hV_lt : dHi * 2^32 + dLo < 2^64)
    (hq_pos : q ≥ 1)
    (hV_pos : dHi * 2^32 + dLo ≥ 1)
    (h_eucl : q * dHi + rhat = u4)
    (h_q_dLo_no_wrap : q * dLo < 2^64)
    (h_q_V_gt : q * (dHi * 2^32 + dLo) > u4 * 2^32 + div_un1)
    (h_qm1_V_le : (q - 1) * (dHi * 2^32 + dLo) ≤ u4 * 2^32 + div_un1) :
    (2^64 - q * dLo + (rhat % 2^32) * 2^32 + div_un1) % 2^64 =
      2^64 + (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) - (dHi * 2^32 + dLo) := by
  -- Compose with the q*dLo identity helper.
  have h_qdLo := algorithmUn21_L4_qdLo_eq_plus_V_minus_r u4 div_un1 dHi dLo q rhat
    hq_pos hV_pos h_eucl h_q_V_gt h_qm1_V_le
  have h_combine := algorithmUn21_L4_halfword_combine rhat
  -- r := u % V, with r < V.
  have h_r_lt_V : (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) < dHi * 2^32 + dLo :=
    Nat.mod_lt _ (by omega)
  have hq_le_64 : q * dLo ≤ 2^64 := le_of_lt h_q_dLo_no_wrap
  -- Add (rhat/2^32)*2^64 to LHS_pre — preserves mod 2^64.
  -- Algebraic result: LHS_pre + h*2^64 = 2^64 + r - V (which is < 2^64 since r < V).
  have h_lhs_plus_h64 :
      2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1 + (rhat / 2^32) * 2^64 =
      2^64 + (u4 * 2^32 + div_un1) % (dHi * 2^32 + dLo) - (dHi * 2^32 + dLo) := by
    have h_reorder :
        2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1 + (rhat / 2^32) * 2^64 =
        2^64 - q * dLo + (rhat % 2^32 * 2^32 + (rhat / 2^32) * 2^64) + div_un1 := by omega
    rw [h_reorder, h_combine]
    -- Goal: 2^64 - q*dLo + rhat*2^32 + div_un1 = 2^64 + r - V
    -- From h_qdLo: q*dLo + r = rhat*2^32 + div_un1 + V
    -- So rhat*2^32 + div_un1 = q*dLo + r - V (Nat-safe since q*dLo + r ≥ V from h_qdLo).
    -- Then 2^64 - q*dLo + rhat*2^32 + div_un1 = 2^64 - q*dLo + (q*dLo + r - V) = 2^64 + r - V.
    omega
  -- (LHS_pre + (rhat/2^32)*2^64) % 2^64 = LHS_pre % 2^64.
  have h_mod_eq :
      (2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1) % 2^64 =
      (2^64 - q * dLo + rhat % 2^32 * 2^32 + div_un1 + (rhat / 2^32) * 2^64) % 2^64 :=
    (Nat.add_mul_mod_self_right _ _ _).symm
  rw [h_mod_eq, h_lhs_plus_h64]
  -- Goal: (2^64 + r - V) % 2^64 = 2^64 + r - V
  -- Since 2^64 + r - V < 2^64 (r < V), mod is identity.
  apply Nat.mod_eq_of_lt
  omega

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

/-- **_of_tight sub-case "exact" L2.a-wrapped**: rewrites L2.a using the
    irreducible `algorithmQ1Prime` wrapper so the lemma can compose with
    `h_q1_prime_eq : (algorithmQ1Prime u4 u3 b3').toNat = q_true_1`. -/
theorem algorithmUn21_L2a_wrapped
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
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    (algorithmQ1Prime u4 u3 b3').toNat * dHi.toNat + rhat'.toNat = u4.toNat := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 rhat'
  have h_unfold := algorithmQ1Prime_unfold u4 u3 b3'
  have h_l2a := algorithmUn21_L2a_phase1b_euclidean_at_u4 u4 u3 b3' hb3'_ge
  simp only [] at h_l2a
  -- The unfolded q1' Word IS the let-bound q1' in h_l2a.
  show (algorithmQ1Prime u4 u3 b3').toNat * dHi.toNat + rhat'.toNat = u4.toNat
  rw [h_unfold]
  simp only []
  exact h_l2a

/-- **_of_tight sub-case "exact" L2.b**: under narrow-u4, the post-Phase-1b
    rhat' is bounded by 2^33. Composes step4 (rhatc < 2^32) with the Phase 1b
    correction structure (rhat' ∈ {rhatc, rhatc + dHi}). -/
theorem algorithmUn21_L2b_rhat_prime_lt_pow33
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
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
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    rhat'.toNat < 2^33 := by
  intro dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo rhatUn1 rhat'
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    algorithmQ1Prime_step4_rhatc_lt_pow32 u4 b3' hb3'_ge hu4_lt_dHi_pow32
  have h_dHi_lt : dHi.toNat < 2^32 := by
    show (b3' >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : b3'.toNat < 2^64 := b3'.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  by_cases h_check : BitVec.ult rhatUn1 qDlo = true
  · show (if BitVec.ult rhatUn1 qDlo = true then rhatc + dHi else rhatc).toNat < 2^33
    rw [if_pos h_check]
    rw [BitVec.toNat_add]
    have h_no_wrap : rhatc.toNat + dHi.toNat < 2^64 := by omega
    rw [Nat.mod_eq_of_lt h_no_wrap]
    omega
  · show (if BitVec.ult rhatUn1 qDlo = true then rhatc + dHi else rhatc).toNat < 2^33
    rw [if_neg h_check]
    omega

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
  -- Establish all sub-facts before rewrites to keep the chain intact.
  have h_l1c := algorithmUn21_L1c_un21_toNat_case_simple u4 u3 b3'
  have h_l1a := algorithmUn21_L1a_cu_rhat_un1_toNat u4 u3 b3'
  have h_l1b := algorithmUn21_L1b_q1_prime_dLo_no_wrap u4 u3 b3' hb3'_ge hu4_lt_b3'
  have h_l2a_w := algorithmUn21_L2a_wrapped u4 u3 b3' hb3'_ge
  have h_l2b := algorithmUn21_L2b_rhat_prime_lt_pow33 u4 u3 b3' hb3'_ge hu4_lt_dHi_pow32
  simp only [] at h_l1c h_l1a h_l1b h_l2a_w h_l2b
  -- Substitute h_q1_prime_eq into L2.a-wrapped.
  rw [h_q1_prime_eq] at h_l2a_w
  -- h_l2a_w : q_true_1 * dHi.toNat + rhat'.toNat = u4.toNat
  -- Apply L1.c, L1.a, L1.b to the goal.
  rw [h_l1c, h_l1a, h_l1b]
  -- Goal: (2^64 - q1'.toNat * dLo.toNat + (rhat'.toNat % 2^32)*2^32 + div_un1.toNat) % 2^64
  --       = (u4.toNat * 2^32 + div_un1.toNat) % b3'.toNat
  -- Use algorithmQ1Prime_unfold to transform q1' (let-bound) into algorithmQ1Prime.
  have h_q1_unfold := (algorithmQ1Prime_unfold u4 u3 b3').symm
  simp only [] at h_q1_unfold
  rw [h_q1_unfold]
  -- Now goal has algorithmQ1Prime in it. Substitute via h_q1_prime_eq.
  rw [h_q1_prime_eq]
  -- Set q := q_true_1 for L4.
  set q := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat with hq_def
  -- L4 hypotheses:
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_V_lt : (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^64 := by
    rw [← h_v_eq]; exact b3'.isLt
  have h_b3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  -- q*dLo < 2^64 (no-wrap).
  have h_q_le : q ≤ 2^32 := by
    rw [hq_def]
    apply Nat.div_le_of_le_mul
    have hb_b3'_ge : b3'.toNat ≥ 2^63 := hb3'_ge
    have h_div_un1_v : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := h_div_un1_lt
    have hu4 : u4.toNat < b3'.toNat := hu4_lt_b3'
    nlinarith
  have h_qdLo_no_wrap :
      q * ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^64 := by
    have h_dLo_le_pow : ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
        ≤ 2^32 - 1 := by have := h_dLo_lt; omega
    nlinarith
  have h_q_V_le :
      q * ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
            ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
      u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq, hq_def]; exact Nat.div_mul_le_self _ _
  have h_r_lt_V :
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) -
        q * ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
             ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq]
    have h_mod := Nat.mod_lt (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) h_b3'_pos
    have h_div_mod : q * b3'.toNat + (u4.toNat * 2^32 +
        (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat =
        u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat := by
      rw [hq_def, Nat.mul_comm]; exact Nat.div_add_mod _ _
    omega
  -- Match the goal's RHS to L4's RHS via h_v_eq.
  rw [h_v_eq]
  -- Reassociate to match L4's exact LHS shape (left-assoc instead of right-assoc).
  rw [show ∀ a b c d : Nat, (a + (b + c)) % d = (a + b + c) % d from
      fun a b c d => by rw [Nat.add_assoc]]
  -- Apply L4!
  exact algorithmUn21_L4_modular_identity u4.toNat (u3 >>> (32 : BitVec 6).toNat).toNat
    (b3' >>> (32 : BitVec 6).toNat).toNat
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat q _
    h_V_lt h_l2a_w h_qdLo_no_wrap h_q_V_le h_r_lt_V

/-- **_of_tight sub-case "off-by-one"**: when `q1' = q_true_1 + 1` (Phase 1b
    false-alarms once), the algorithm's un21 = r1_math + (2^64 - V), which is
    ≥ r1_math.

    Composition: same structure as L5 (the exact case), but using L4_plus_one
    (the sign-flipped modular identity) instead of L4. Yields
    algorithmUn21.toNat = 2^64 + r - V (≥ r since V ≤ 2^64). -/
theorem algorithmUn21_ge_r1_math_of_q1_prime_eq_q_true_1_plus_one
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_q1_prime_eq : (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1) :
    (algorithmUn21 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_dLo_lt :
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : (b3' <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
      (b3' <<< (32 : BitVec 6).toNat : Word).isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_b3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  -- Establish all sub-facts.
  have h_l1c := algorithmUn21_L1c_un21_toNat_case_simple u4 u3 b3'
  have h_l1a := algorithmUn21_L1a_cu_rhat_un1_toNat u4 u3 b3'
  have h_l1b := algorithmUn21_L1b_q1_prime_dLo_no_wrap u4 u3 b3' hb3'_ge hu4_lt_b3'
  have h_l2a_w := algorithmUn21_L2a_wrapped u4 u3 b3' hb3'_ge
  have h_l2b := algorithmUn21_L2b_rhat_prime_lt_pow33 u4 u3 b3' hb3'_ge hu4_lt_dHi_pow32
  simp only [] at h_l1c h_l1a h_l1b h_l2a_w h_l2b
  rw [h_q1_prime_eq] at h_l2a_w
  rw [h_l1c, h_l1a, h_l1b]
  have h_q1_unfold := (algorithmQ1Prime_unfold u4 u3 b3').symm
  simp only [] at h_q1_unfold
  rw [h_q1_unfold]
  rw [h_q1_prime_eq]
  set q := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat with hq_def
  have h_div_un1_lt : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : u3.toNat < 2^64 := u3.isLt
    exact Nat.div_lt_of_lt_mul (by omega)
  have h_V_lt : (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^64 := by
    rw [← h_v_eq]; exact b3'.isLt
  have h_V_pos : (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat ≥ 1 := by
    rw [← h_v_eq]; omega
  have h_q_le : q ≤ 2^32 := by
    rw [hq_def]
    apply Nat.div_le_of_le_mul
    have : u4.toNat < b3'.toNat := hu4_lt_b3'
    have : (u3 >>> (32 : BitVec 6).toNat).toNat < 2^32 := h_div_un1_lt
    nlinarith
  have h_qp1_dLo_no_wrap :
      (q + 1) * ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^64 := by
    have h_q_plus_1_le : q + 1 ≤ 2^32 + 1 := by omega
    have h_dLo_le_pow : ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat
        ≤ 2^32 - 1 := by have := h_dLo_lt; omega
    have h_prod_le : (q + 1) * ((b3' <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat ≤ (2^32 + 1) * (2^32 - 1) :=
      Nat.mul_le_mul h_q_plus_1_le h_dLo_le_pow
    have h_eq : (2^32 + 1) * (2^32 - 1 : Nat) = 2^64 - 1 := by decide
    omega
  have h_qp1_V_gt :
      (q + 1) * ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) >
      u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat := by
    rw [← h_v_eq, hq_def]
    exact algorithmUn21_L5_succ_mul_div_gt _ _ h_b3'_pos
  have h_qp1m1_V_le :
      (q + 1 - 1) * ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) ≤
      u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat := by
    have h_simp : q + 1 - 1 = q := Nat.add_sub_cancel q 1
    rw [h_simp, ← h_v_eq, hq_def]
    exact Nat.div_mul_le_self _ _
  have h_qp1_pos : q + 1 ≥ 1 := Nat.le_add_left 1 q
  rw [h_v_eq]
  -- Reassociate and apply L4_plus_one.
  rw [show ∀ a b c d e : Nat, (a + (b + c)) % d ≥ e ↔ (a + b + c) % d ≥ e from
      fun a b c d e => by rw [Nat.add_assoc]]
  rw [algorithmUn21_L4_modular_identity_plus_one u4.toNat
    (u3 >>> (32 : BitVec 6).toNat).toNat
    (b3' >>> (32 : BitVec 6).toNat).toNat
    ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat (q + 1) _
    h_V_lt h_qp1_pos h_V_pos h_l2a_w h_qp1_dLo_no_wrap
    h_qp1_V_gt h_qp1m1_V_le]
  -- Goal: 2^64 + r - V ≥ r. Since V ≤ 2^64 (h_V_lt), this holds.
  have h_r_lt_V : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) %
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
       ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) <
      ((b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
       ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat) :=
    Nat.mod_lt _ (by linarith [h_V_pos])
  omega

/-- **Bridge sub-B** (algebraic consequence): given `q1' ≤ q_true_1 + 1` and
    `un21 < dHi*2^32`, the algorithm's un21 cannot be less than `r1_math`. -/
theorem algorithmUn21_eq_r1_math_of_tight
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
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
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32) :
    (algorithmUn21 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) % b3'.toNat := by
  by_contra h_lt
  push Not at h_lt
  exact algorithmUn21_eq_r1_math_of_tight u4 u3 b3' hb3'_ge hu4_lt_b3'
    hu4_lt_dHi_pow32 h_lt

/-- **Contrapositive of L5 exact case**: when the algorithm's un21 is at
    least as large as V (i.e., un21 ≥ b3'), Phase 1 must have false-alarmed
    (q1' = q_true_1 + 1).

    Direct contrapositive of `algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1`:
    if q1' = q_true_1, then un21 = r1_math < V. So un21 ≥ V implies q1' ≠ q_true_1.
    Combined with the upper bound q1' ≤ q_true_1 + 1, we get q1' = q_true_1 + 1. -/
theorem algorithmQ1Prime_eq_q_true_1_plus_one_of_un21_ge_vTop
    (u4 u3 b3' : Word)
    (hb3'_ge : b3'.toNat ≥ 2^63)
    (hu4_lt_b3' : u4.toNat < b3'.toNat)
    (hu4_lt_dHi_pow32 : u4.toNat < (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32)
    (h_un21_ge_vTop : (algorithmUn21 u4 u3 b3').toNat ≥ b3'.toNat) :
    (algorithmQ1Prime u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat + 1 := by
  -- Get the upper bound q1' ≤ q_true + 1 from QuotientBounds.
  have h_q1_le := algorithmQ1Prime_le_q_true_1_plus_one u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32
  set q_true := (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) / b3'.toNat with hq_true_def
  -- Show q1' ≠ q_true via contradiction (using L5 exact case).
  by_contra h_neq
  -- Either q1' < q_true or q1' = q_true (since q1' ≤ q_true + 1).
  have h_cases : (algorithmQ1Prime u4 u3 b3').toNat ≤ q_true := by
    -- q1' ≤ q_true + 1 and q1' ≠ q_true + 1, so q1' ≤ q_true.
    omega
  -- We also need q1' ≥ q_true (Phase 1 tight).
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
  have h_v_eq : b3'.toNat =
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    div128Quot_vTop_decomp b3'
  have h_u4_lt_vTop : u4.toNat <
      (b3' >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      ((b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat :=
    h_v_eq ▸ hu4_lt_b3'
  have h_q1_ge := algorithmQ1Prime_ge_q_true_1 u4 u3 b3'
    h_dHi_ge h_dHi_lt h_dLo_lt hu4_lt_dHi_pow32 h_u4_lt_vTop
  rw [← h_v_eq] at h_q1_ge
  -- So q1' = q_true (since both ≤ and ≥).
  have h_q1_eq : (algorithmQ1Prime u4 u3 b3').toNat = q_true := by omega
  -- But L5 exact case says un21 = r1_math < V — contradiction with un21 ≥ V.
  have h_un21_eq := algorithmUn21_eq_r1_math_of_q1_prime_eq_q_true_1 u4 u3 b3'
    hb3'_ge hu4_lt_b3' hu4_lt_dHi_pow32 h_q1_eq
  have h_b3'_pos : 0 < b3'.toNat := by have : b3'.toNat ≥ 2^63 := hb3'_ge; omega
  have h_r1_lt : (u4.toNat * 2^32 + (u3 >>> (32 : BitVec 6).toNat).toNat) %
      b3'.toNat < b3'.toNat := Nat.mod_lt _ h_b3'_pos
  -- un21 ≥ V but un21 = r1_math < V — contradiction.
  rw [h_un21_eq] at h_un21_ge_vTop
  exact absurd h_un21_ge_vTop (Nat.not_le_of_gt h_r1_lt)

end EvmAsm.Evm64
