/-
  EvmAsm.Crypto.Fermat

  The Fermat / quadratic-residue facts (bead evm-asm-4ch8f.11.12,
  crypto-strategy §6 label `.11.8`, §4 divergence lemmas 1 & 3) — **the
  one mathlib-heavy file** (crypto-strategy §2): Euler's totient theorem
  enters here through `Nat.ModEq.pow_totient`
  (`Mathlib.FieldTheory.Finite.Basic`) and NOWHERE else; every statement
  is over the `Nat`-modular vocabulary the accelerator seam and the
  SpecRef corpus use, so consumers never see `ZMod`.

  Contents (all general — `p.Prime` is a hypothesis; the per-prime
  primality certificates for the five concrete field/scalar primes are
  the Opus instances of this bead, expected via `lucas_primality`-style
  witnesses):

  * `powModAux_eq_pow` / `powMod_eq_pow` — the kernel-reducible
    `Accel.powMod` square-and-multiply agrees with `Nat.pow` mod `m`
    (any `m`, exponents below the `2^512` fuel bound).  Everything the
    guest computes via ladders reduces to `Nat.pow` through this.
  * `fermat_little` — `a^(p−1) ≡ 1 (mod p)` for `a ≢ 0`.
  * `fermat_inv_pow` / `fermat_invMod` — Fermat inversion: for prime
    `p` and `0 < a < p`, `a · a^(p−2) ≡ 1`, i.e. `Accel.invMod a p` IS
    the modular inverse (crypto-strategy §4 divergence lemma 1: kernels
    and EL specs compute `x⁻¹` as `x^(p−2)`; where the spec-side
    semantics demands "the inverse", this lemma discharges it).
  * `qr_sqrt_pow` / `qr_sqrt_powMod` — the `p ≡ 3 (mod 4)` square root:
    if `a` is a quadratic residue (witness `y² ≡ a`), then
    `(a^((p+1)/4))² ≡ a` — the verify-by-squaring acceptance
    (`decompressR`'s `y₀·y₀ ≟ rhs` gate) is COMPLETE on residues.
    (Soundness of the gate is the gate itself; no lemma needed.)
  * The secp256k1 sqrt **skip-bit ladder** facts (crypto-strategy §4
    divergence lemma 3, the `.11.2` fix — previously grep-audited, now
    kernel-proved): `secpSqrtExpBytes` (the guest's documented
    `secp256k1_sqrt_exp_be` constant) has value `(p+1)/4`; its zero
    bits are EXACTLY the hardcoded skip set `{255,254,30,7,6,5,4,1,0}`
    of `secfSqrtModP_prog`'s `LI/BEQ` chain; and the resulting
    square-and-multiply ladder computes `a^((p+1)/4) mod p`
    (`secp_sqrt_ladder_correct`).  These need no primality.

  Consumers: every inversion and square root in `.38` (secp256k1
  recovery: `secf_inv_mod_p/n`, `secf_sqrt_mod_p`) and `.58`
  (P256VERIFY, BN254/BLS12 field towers, MODEXP-adjacent Fermat
  ladders).  `.38.1`'s `Secp256k1.sqrtCand a = Accel.powMod a ((p+1)/4) p`
  is definitionally the `qr_sqrt_powMod` subject.
-/

import Mathlib.FieldTheory.Finite.Basic
import EvmAsm.Crypto.PowLadder

namespace EvmAsm.Crypto

open EvmAsm.Rv64

-- ============================================================================
-- Accel.powMod agrees with Nat.pow
-- ============================================================================

/-- The fuel-indexed square-and-multiply core computes `b^e mod m`
    (any modulus, exponent below the fuel bound). -/
theorem powModAux_eq_pow (m : Nat) :
    ∀ (fuel b e : Nat), e < 2 ^ fuel →
      Accel.powModAux m fuel b e = b ^ e % m
  | 0, b, e, he => by
      obtain rfl : e = 0 := by omega
      rfl
  | fuel + 1, b, e, he => by
      show (if e = 0 then 1 % m
        else
          let h := Accel.powModAux m fuel (b * b % m) (e / 2)
          if e % 2 = 1 then h * (b % m) % m else h) = b ^ e % m
      by_cases he0 : e = 0
      · subst he0
        rw [if_pos rfl, Nat.pow_zero]
      · rw [if_neg he0]
        have hhalf : e / 2 < 2 ^ fuel := by
          have h2 : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ ..
          omega
        have hrec := powModAux_eq_pow m fuel (b * b % m) (e / 2) hhalf
        have hsq : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
          rw [← Nat.pow_mod, show b * b = b ^ 2 from (Nat.pow_two b).symm,
            ← Nat.pow_mul]
        show (if e % 2 = 1 then
            Accel.powModAux m fuel (b * b % m) (e / 2) * (b % m) % m
          else Accel.powModAux m fuel (b * b % m) (e / 2)) = b ^ e % m
        rcases Nat.mod_two_eq_zero_or_one e with hpar | hpar
        · rw [if_neg (by omega), hrec, hsq,
            show 2 * (e / 2) = e from by omega]
        · rw [if_pos hpar, hrec, hsq, Nat.mod_mul_mod, Nat.mul_mod_mod,
            ← Nat.pow_succ]
          have hsucc : (2 * (e / 2)).succ = e := by omega
          rw [hsucc]

/-- `Accel.powMod b e m = b^e mod m` for every exponent below the
    `2^512` fuel bound (all field/scalar exponents in scope are below
    `2^384`). -/
theorem powMod_eq_pow {b e m : Nat} (he : e < 2 ^ 512) :
    Accel.powMod b e m = b ^ e % m := by
  show Accel.powModAux m 512 (b % m) e = b ^ e % m
  rw [powModAux_eq_pow m 512 (b % m) e he, ← Nat.pow_mod]

-- ============================================================================
-- Fermat's little theorem and Fermat inversion (over Nat)
-- ============================================================================

/-- **Fermat's little theorem**, `Nat`-modular form: for prime `p` and
    `a ≢ 0 (mod p)`, `a^(p−1) mod p = 1`.  Proved via Euler's totient
    theorem (`Nat.ModEq.pow_totient`) — the single mathlib-oracle
    crossing of this file. -/
theorem fermat_little {p a : Nat} (hp : p.Prime) (ha : a % p ≠ 0) :
    a ^ (p - 1) % p = 1 := by
  have hcop : a.Coprime p := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun hdvd => ha (Nat.dvd_iff_mod_eq_zero.mp hdvd))
  have heuler := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp] at heuler
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
  rw [Nat.ModEq] at heuler
  rw [heuler, h1]

/-- **Fermat inversion**, pow form: for prime `p` and `0 < a < p`,
    `a · a^(p−2) ≡ 1 (mod p)` — the exponent-`(p−2)` power is a true
    modular inverse. -/
theorem fermat_inv_pow {p a : Nat} (hp : p.Prime) (h0 : 0 < a)
    (ha : a < p) :
    a * a ^ (p - 2) % p = 1 := by
  have h2 := hp.two_le
  have hpow : a * a ^ (p - 2) = a ^ (p - 1) := by
    rw [show p - 1 = (p - 2) + 1 from by omega, Nat.pow_succ,
      Nat.mul_comm]
  rw [hpow]
  exact fermat_little hp (by rw [Nat.mod_eq_of_lt ha]; omega)

/-- **Fermat inversion**, seam form: `Accel.invMod a p` IS the modular
    inverse of `a` for prime `p` and reduced nonzero `a` (the fuel-bound
    hypothesis holds for every prime in scope — they are all below
    `2^384`, let alone `2^512 + 2`). -/
theorem fermat_invMod {p a : Nat} (hp : p.Prime) (hpf : p - 2 < 2 ^ 512)
    (h0 : 0 < a) (ha : a < p) :
    a * Accel.invMod a p % p = 1 := by
  show a * Accel.powMod a (p - 2) p % p = 1
  rw [powMod_eq_pow hpf, Nat.mul_mod_mod]
  exact fermat_inv_pow hp h0 ha

-- ============================================================================
-- The p ≡ 3 (mod 4) square root (quadratic residues)
-- ============================================================================

/-- **The `p ≡ 3 (mod 4)` square-root exponent**, pow form: if `a` is a
    quadratic residue mod prime `p` (witness `y² ≡ a`), then the
    candidate `a^((p+1)/4)` squares back to `a` — the verify-by-squaring
    acceptance is complete on residues.  (On non-residues the candidate
    squares to `−a`; the kernels and `decompressR` REJECT by the same
    squaring gate, which needs no lemma.) -/
theorem qr_sqrt_pow {p a y : Nat} (hp : p.Prime) (hmod : p % 4 = 3)
    (hy : y * y % p = a % p) :
    (a ^ ((p + 1) / 4)) ^ 2 % p = a % p := by
  have h2 := hp.two_le
  -- (a^((p+1)/4))² = a^((p+1)/2), since 4 ∣ p + 1
  have hexp : (a ^ ((p + 1) / 4)) ^ 2 = a ^ ((p + 1) / 2) := by
    rw [← Nat.pow_mul]
    congr 1
    omega
  rw [hexp]
  -- transport along the witness: a^((p+1)/2) ≡ (y²)^((p+1)/2) = y^(p+1)
  have hwit : a ^ ((p + 1) / 2) % p = y ^ (p + 1) % p := by
    rw [Nat.pow_mod, ← hy, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul,
      show 2 * ((p + 1) / 2) = p + 1 from by omega]
  rw [hwit]
  by_cases hy0 : y % p = 0
  · -- a ≡ y² ≡ 0 and y^(p+1) ≡ 0
    rw [Nat.pow_mod, hy0, Nat.zero_pow (by omega), Nat.zero_mod, ← hy,
      Nat.mul_mod, hy0, Nat.mul_zero, Nat.zero_mod]
  · -- y^(p+1) = y² · y^(p−1) ≡ y² ≡ a
    have hsplit : y ^ (p + 1) = y * y * y ^ (p - 1) := by
      rw [← Nat.pow_two, ← Nat.pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_mod, fermat_little hp hy0, Nat.mul_one,
      Nat.mod_mod_of_dvd _ (Nat.dvd_refl p), hy]

/-- **The `p ≡ 3 (mod 4)` square-root exponent**, seam form: the
    kernel-side candidate `Accel.powMod a ((p+1)/4) p` (exactly
    `.38.1`'s `Secp256k1.sqrtCand` shape) squares back to `a` on
    quadratic residues. -/
theorem qr_sqrt_powMod {p a y : Nat} (hp : p.Prime) (hmod : p % 4 = 3)
    (hexp : (p + 1) / 4 < 2 ^ 512)
    (hy : y * y % p = a % p) :
    Accel.powMod a ((p + 1) / 4) p * Accel.powMod a ((p + 1) / 4) p % p
      = a % p := by
  rw [powMod_eq_pow hexp, Nat.mod_mul_mod, Nat.mul_mod_mod,
    ← Nat.pow_two]
  exact qr_sqrt_pow hp hmod hy

-- ============================================================================
-- The secp256k1 sqrt skip-bit ladder (crypto-strategy §4 item 3)
-- ============================================================================

/-- The guest's hardcoded multiply-skip bit positions in
    `secfSqrtModP_prog` (`Codegen/Programs/Secp256k1Field.lean`): bits
    `{255,254,30,7,6,5,4,1}` from the `LI x5,k; BEQ x19,x5` chain plus
    bit `0` from the separate `BEQ x19,x0`. -/
def secpSqrtSkipBits : List Nat := [255, 254, 30, 7, 6, 5, 4, 1, 0]

/-- The guest's `secp256k1_sqrt_exp_be` constant (the `.11.2`-corrected
    32 big-endian bytes), byte-for-byte. -/
def secpSqrtExpBytes : List (BitVec 8) :=
  [0x3f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xbf, 0xff, 0xff, 0x0c]

/-- `p ≡ 3 (mod 4)` for the secp256k1 base field — the square-root
    exponent shape applies (previously stated only in `.38.1` prose;
    kernel-pinned here). -/
theorem secpP_mod_four : Accel.secpP % 4 = 3 := by decide +kernel

/-- The documented exponent constant has value `(p+1)/4` (the `.11.2`
    fix, kernel-pinned: the pre-fix bytes fail this). -/
theorem secpSqrtExp_value :
    beBytesToNat secpSqrtExpBytes = (Accel.secpP + 1) / 4 := by
  decide +kernel

/-- **The skip-bit audit, proved**: bit `i` of `(p+1)/4` is zero exactly
    at the hardcoded skip positions — the guest's `LI/BEQ` skip chain
    multiplies precisely at the exponent's set bits. -/
theorem secpSqrt_skip_bits :
    ∀ i, i < 256 →
      ((Accel.secpP + 1) / 4).testBit i = !(secpSqrtSkipBits.contains i) := by
  decide +kernel

/-- The MSB-first view of the skip set (what the ladder loop consults at
    iteration `i`): the fetched bit is set iff `255 − i` is not
    skipped. -/
theorem secpSqrt_beBit :
    ∀ i, i < 256 →
      beBit secpSqrtExpBytes i = !(secpSqrtSkipBits.contains (255 - i)) := by
  decide +kernel

/-- **The secp sqrt ladder is `a^((p+1)/4) mod p`** (crypto-strategy §4
    divergence lemma 3): a square-and-multiply ladder driven by the
    `secpSqrtExpBytes` bit schedule — equivalently, by the skip-bit set,
    via `secpSqrt_beBit` — computes exactly the `p ≡ 3 (mod 4)`
    square-root candidate that `qr_sqrt_pow`/`qr_sqrt_powMod` certify.
    No primality needed. -/
theorem secp_sqrt_ladder_correct (a : Nat) :
    ladder Accel.secpP a secpSqrtExpBytes 256
      = a ^ ((Accel.secpP + 1) / 4) % Accel.secpP := by
  have h := ladder_correct Accel.secpP a (by decide +kernel) secpSqrtExpBytes
  rw [show 8 * secpSqrtExpBytes.length = 256 from rfl] at h
  rw [h, secpSqrtExp_value]

-- ============================================================================
-- Kernel-checked shape guards
-- ============================================================================

/-- `powMod` really is `Nat.pow` (guards `powMod_eq_pow`'s shape on a
    concrete instance). -/
example : Accel.powMod 7 0x123 1009 = 7 ^ 0x123 % 1009 := by decide +kernel

/-- Fermat inversion on a concrete prime (guards the statement shape:
    `3 · 3^1007 ≡ 1 (mod 1009)`). -/
example : 3 * Accel.invMod 3 1009 % 1009 = 1 := by decide +kernel

/-- The `p ≡ 3 (mod 4)` sqrt on a concrete prime: `2² = 4` is a residue
    mod `1019 ≡ 3 (mod 4)`, and the candidate squares back to it. -/
example :
    Accel.powMod 4 ((1019 + 1) / 4) 1019
      * Accel.powMod 4 ((1019 + 1) / 4) 1019 % 1019 = 4 := by
  decide +kernel

end EvmAsm.Crypto
