/-
  EvmAsm.Stateless.SpecRef.Secp256k1Recover

  The project-side secp256k1 ECDSA public-key recovery reference spec
  (bead evm-asm-4ch8f.38.1) — the trusted-base Lean math that the guest
  crypto triples are proven against:
  * `.38c` — `secp256k1_recover_r` / `secp256k1_recover_pubkey_staged`
    (`EvmAsm/Codegen/Programs/Secp256k1Recover.lean`, `TxPubkey.lean`),
  * `.39`  — transaction-sender verification
    (`verify_public_keys_match_senders`),
  * `.40`  — EIP-7702 authority recovery.

  WHY PROJECT-SIDE: execution-specs (`tests-zkevm@v0.4.0`,
  `src/ethereum/crypto/elliptic_curve.py`) has no pure-Python
  `secp256k1_recover` — after an Euler-criterion pre-check it delegates to
  native `coincurve` (libsecp256k1). There is nothing to port, so the
  reference is defined here, over the `Nat`-modular vocabulary
  (crypto-strategy §4), reusing the kernel-reducible field/curve primitives
  of `EvmAsm.Rv64.Accel` (`powMod`, `invMod`, `curveAdd`, `curveDbl`) and
  the SpecRef `keccak256`. Every equation is pinned to TWO independent
  authorities, cited inline; the KATs at the bottom are cross-derived from
  the probe vectors and an independently computed set, and kernel-checked
  with `decide +kernel` (no `native_decide`, no `maxRecDepth`/heartbeat
  overrides).

  SUBSTRATE DECISION (first deliverable of the bead, recorded also as a
  crypto-strategy §4 amendment): values live in `Nat` (mod p / mod n), NOT
  `ZMod p` and NOT mathlib's `WeierstrassCurve` points. Grounds: (1) the
  kernel↔spec value seam is `Nat`/`BitVec`-limb — the guest computes field
  values through Arith256Mod, whose semantics (`Accel.arith256Mod`) is a
  `Nat` function, so a `Nat`-valued reference composes with the seam
  without a `ZMod.val` transport at every field operation; (2) the KATs
  below must reduce in the Lean kernel (`decide`), which concrete-`Nat`
  code does out of the box, while mathlib's affine `Point.add` carries
  nonsingularity proofs and the `EllipticCurve` import tree is heavy.
  Mathlib remains available as a justification ORACLE inside future named
  divergence lemmas (Fermat/QR facts, bead .11.8 / `Crypto/Fermat.lean`),
  stated over `Nat` and proven via `ZMod` where convenient — the
  *interfaces* here stay `Nat`.

  ALGORITHM-FAITHFUL SCOPE (crypto-strategy §4): this file defines a
  deterministic recovery *function* mirroring what libsecp256k1's
  `secp256k1_ecdsa_recover` computes on the domain the guest exercises.
  Group associativity, hash security, and "the" square-root existence are
  out of scope; number theory enters only at the named kernel↔spec
  divergence lemmas (Fermat inversion `x⁻¹ = x^(m−2)`, the sqrt exponent
  `(p+1)/4`, the guest's sqrt skip-bit ladder — beads .11.8 and
  crypto-strategy §4 item 3, which discharge against the definitions
  below).

  FAILURE TAXONOMY (explicit `Except`, mapped to the guest status codes):
  * `.rOutOfRange` / `.sOutOfRange` — `r`/`s` not in `(0, n)`
    (execution-specs `ecrecover.py` gates; also subsumes the guest's
    `secf_inv_mod_n` non-invertibility failure, since `n` is prime).
  * `.xOutOfRange` — candidate `x = r + j·n ≥ p`
    (guest `secp256k1_recover_r` status 2).
  * `.xNotSquare` — `x³ + 7` has no square root mod `p`
    (guest `secp256k1_recover_r` status 1).
  * `.atInfinity` — the recovered point is the identity
    (guest `secp256k1_recover_pubkey_staged` status 60).

  RECORDED AUTHORITY DIVERGENCE (the one corner where the two sources
  disagree; unreachable, and guarded by a kernel-checked fact below):
  execution-specs pre-checks `pow(x³+7, (p−1)/2, p) == 1` (Euler), which
  REJECTS `x³+7 ≡ 0`; the SEC1-style check used here and by the guest
  (`y_candidate² ≟ x³+7`) would ACCEPT it (with `y = 0`). The two agree on
  every other input, and the disagreeing class is empty: `x³ + 7 ≡ 0
  (mod p)` has no solution because `−7` is not a cube mod `p` (`p ≡ 1
  (mod 3)`, and `(p−7)^((p−1)/3) ≠ 1 (mod p)` — kernel-checked as
  `neg7_not_cube` below; a solution `x` would force that power to be
  `x^(p−1) = 1` by Fermat). Equivalently: secp256k1 has prime, odd group
  order, so it has no point of order 2, i.e. no point with `y = 0`.
-/

import EvmAsm.Stateless.SpecRef.Crypto

-- `Except` equality is decidable componentwise (core provides `BEq`
-- only); the recovery KATs below state `recover … = .ok/.error …` as
-- kernel-`decide`d propositions.
deriving instance DecidableEq for Except

namespace EvmAsm.Stateless.SpecRef.Secp256k1

open EvmAsm.Rv64

/-! ## Curve domain parameters

Sources (two independent authorities):
1. SEC 2 v2.0, §2.4.1 "Recommended Parameters secp256k1" (Certicom,
   2010): `p = 2²⁵⁶ − 2³² − 977`, curve `y² = x³ + 7`, base point `G`,
   prime group order `n`, cofactor `h = 1`.
2. execution-specs `tests-zkevm@v0.4.0`,
   `src/ethereum/crypto/elliptic_curve.py` (`SECP256K1P`, `SECP256K1N`,
   `SECP256K1B`) and Ethereum Yellow Paper, Appendix F ("secp256k1n").
   The generator coordinates additionally match the guest's
   `secp256k1_generator` table
   (`EvmAsm/Codegen/Programs/Secp256k1Curve.lean`). -/

/-- The base-field prime `p` (shared with the accelerator semantics —
    `Accel.secpP` is the modulus `csrsWrite` uses for the
    Secp256k1Add/Dbl ids, so the seam and this spec pin the SAME
    constant). -/
abbrev p : Nat := Accel.secpP

/-- The (prime) group order `n`. -/
def n : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- The curve constant `b` in `y² = x³ + b`. -/
def b : Nat := 7

/-- Base point `G`, x-coordinate. -/
def gx : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- Base point `G`, y-coordinate. -/
def gy : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-! ## The affine group operation

An affine point is a pair of reduced coordinates; `Option` adjoins the
identity `𝒪` (`none`), exactly the software convention of the guest's
`secp256k1_point_add`/`_double`/`_scalar_mul`
(`EvmAsm/Codegen/Programs/Secp256k1Curve.lean`: the ziskemu accelerators
compute the generic chord/tangent case, the special cases — identity
operand, `x₁ = x₂`, `y = 0` — stay in software).

Sources for the case split:
1. SEC 1 v2.0, §2.2.1 (group law over `F_p`, `p > 3`): `𝒪` is the
   identity; `(x, y) + (x, −y) = 𝒪`; distinct-`x` chord rule; tangent
   rule for doubling.
2. Nethermind EVMYulLean's executable cross-reference
   (`EvmYul/EllipticCurvesPy/elliptic_curve.py`, class `Point`:
   `__add__`/`double`), and this repo's kernel-checked
   `Accel.curveAdd`/`Accel.curveDbl` (`EvmAsm/Rv64/ZiskAccel.lean`, with
   generator KATs `secp_curveAdd_kat`/`secp_curveDbl_kat`) for the
   chord/tangent formulas themselves.

Note `x₁ = x₂` on-curve forces `y₂ ∈ {y₁, p − y₁}`; the `(y₁ + y₂) % p =
0` test therefore selects `𝒪` exactly for the inverse case AND for the
`y₁ = y₂ = 0` self-inverse doubling (2-torsion) case, and doubling
otherwise — matching `Point.double`'s `y == 0` guard. Off-curve operand
pairs with `x₁ = x₂`, `y₁ ≠ ±y₂` are outside every authority's domain;
the definition is total on them (it doubles `(x₁, y₁)`) purely so the
spec stays a deterministic function — recovery only ever adds points
constructed on-curve. -/

/-- An affine point (coordinates mod `p`). -/
abbrev Point := Nat × Nat

/-- Group addition on `Option Point` (`none` = the identity `𝒪`). -/
def pointAdd : Option Point → Option Point → Option Point
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
      if x1 = x2 then
        if (y1 + y2) % p = 0 then none
        else some (Accel.curveDbl p x1 y1)
      else some (Accel.curveAdd p x1 y1 x2 y2)

/-- LSB-first double-and-add, structural on the fuel so the kernel can
    reduce it (`decide` KATs). `scalarMulAux fuel k P acc` computes
    `acc + k·P` for `k < 2^fuel`.

    Sources: double-and-add is Handbook of Applied Cryptography
    (Menezes–van Oorschot–Vanstone, 1997) Algorithm 14.76 (right-to-left
    binary exponentiation, written additively), and the guest's
    `secp256k1_scalar_mul` (MSB-first double-and-add over the same
    `pointAdd` case split — same fold value, bead .11.9's
    `scalarMul_correct` bridges the bit orders). -/
def scalarMulAux : Nat → Nat → Option Point → Option Point → Option Point
  | 0, _, _, acc => acc
  | fuel + 1, k, pt, acc =>
      if k = 0 then acc
      else
        scalarMulAux fuel (k / 2) (pointAdd pt pt)
          (if k % 2 = 1 then pointAdd acc pt else acc)

/-- `k·P` for `k < 2²⁵⁶` (recovery only uses scalars reduced mod `n`,
    and `n < 2²⁵⁶`). -/
def scalarMul (k : Nat) (pt : Option Point) : Option Point :=
  scalarMulAux 256 k pt none

/-- `y² % p = (x³ + b) % p` — the curve membership predicate
    (SEC 1 v2.0 §2.2.1; execution-specs `is_on_curve`,
    `src/ethereum/crypto/elliptic_curve.py` companions in py_ecc). -/
def onCurve (pt : Point) : Bool :=
  decide (pt.2 * pt.2 % p = (pt.1 * pt.1 % p * pt.1 + b) % p)

/-! ## Point decompression and recovery -/

/-- The square-root candidate `a^((p+1)/4) mod p` (citations at
    `decompressR`; `Accel.powMod` is the kernel-reducible
    square-and-multiply shared with the accelerator semantics, fuel
    512 ≥ 256 bits, and its `1 < m` pow-ladder precondition — the
    `.11.5` corner class — is met by `p > 1`). -/
def sqrtCand (a : Nat) : Nat := Accel.powMod a ((p + 1) / 4) p

/-- The failure taxonomy of ECDSA recovery (module docstring maps each
    constructor to its guest status code and its authority). -/
inductive RecoverError where
  /-- `r ∉ (0, n)` — execution-specs `ecrecover.py` `0 < r < SECP256K1N`
      gate / Yellow Paper App. F; also covers `r` non-invertible mod the
      prime `n` (the guest's `secf_inv_mod_n` failure arm). -/
  | rOutOfRange
  /-- `s ∉ (0, n)` — execution-specs `ecrecover.py` `0 < s < SECP256K1N`
      gate / Yellow Paper App. F. (Transaction-sender validation — the
      `.39` consumer — additionally caps `s ≤ n/2` per EIP-2; that
      stricter gate lives with the caller, as it does in the guest.) -/
  | sOutOfRange
  /-- Candidate `x = r + j·n ≥ p` — SEC 1 §4.1.6 step 1.2/1.3 (the
      candidate must be a valid field element) / libsecp256k1
      `secp256k1_ecdsa_recover` overflow check; guest
      `secp256k1_recover_r` status 2. -/
  | xOutOfRange
  /-- `x³ + 7` is not a square mod `p`, so no point has this
      x-coordinate — SEC 1 §2.3.4 step 2.4.1 (decompression fails) /
      execution-specs `secp256k1_recover` `is_square` gate; guest
      `secp256k1_recover_r` status 1. -/
  | xNotSquare
  /-- The recovered point is `𝒪` — libsecp256k1
      `secp256k1_ecdsa_sig_recover` returns failure on infinity /
      execution-specs: "If the recovery algorithm returns the point at
      infinity, the signature is considered invalid"; guest
      `secp256k1_recover_pubkey_staged` status 60. -/
  | atInfinity
  deriving Repr, DecidableEq

/-- Decompress the ephemeral point `R = (x, y)` from a signature `r`
    value and recovery id `recid`.

    Equations, each pinned by two authorities:
    * candidate `x = r + j·n` with `j` = recid bit 1: SEC 1 v2.0 §4.1.6
      step 1.1 (`x = r + j·n`, `j ∈ {0, …, h}`, `h = 1` for secp256k1);
      libsecp256k1 `recovery/main_impl.h` (`recid & 2` selects the
      `+ n` candidate). Rejected when `x ≥ p` (see `.xOutOfRange`).
    * `y` candidate `= (x³ + 7)^((p+1)/4) mod p`: square roots mod a
      prime `p ≡ 3 (mod 4)` — SEC 1 v2.0 §2.3.4 note + Handbook of
      Applied Cryptography Algorithm 3.36; verified by squaring (the
      `y² ≟ x³ + 7` check), which is the same acceptance condition
      libsecp256k1's `secp256k1_ge_set_xquad`/`fe_sqrt` enforces. The
      guest computes the same exponent by a hard-coded skip-bit ladder;
      its `(p+1)/4`-correctness is the named divergence lemma of
      crypto-strategy §4 item 3 (its zero-bit set was verified in the
      #9731 review) and discharges against `sqrtCand` below.
    * parity selection, recid bit 0 = parity of `R.y`: Yellow Paper
      App. F (`v ∈ {27, 28}` encodes "parity of the curve point's
      y-value"); libsecp256k1 `recovery/main_impl.h` (`recid & 1` →
      conditional negation `y ← p − y`). The `(p − y₀) % p` form matches
      the probe reference (`scripts/codegen-zisk-secp256k1-recover-check.sh`)
      including at the unreachable `y₀ = 0` corner (module docstring).

    `recid` is read exactly as the guest's `ANDI recid, 1` / `ANDI
    recid, 2` do: bit 0 = `recid % 2`, bit 1 = `recid / 2 % 2`. The
    Ethereum-visible domain is `recid ∈ {0, 1}` (from `v − 27`); the
    `x ≥ p` reject also subsumes the guest's `u256_add_be` carry-out
    arm, since `r + n ≥ 2²⁵⁶ > p` whenever the 256-bit add overflows. -/
def decompressR (r recid : Nat) : Except RecoverError Point :=
  let x := r + (if recid / 2 % 2 = 1 then n else 0)
  if p ≤ x then .error .xOutOfRange
  else
    let rhs := (x * x % p * x + b) % p
    let y0 := sqrtCand rhs
    if y0 * y0 % p ≠ rhs then .error .xNotSquare
    else .ok (x, if y0 % 2 = recid % 2 then y0 else (p - y0) % p)

/-- ECDSA public-key recovery: from the message-hash value `e`, the
    signature scalars `(r, s)` and the recovery id `recid`, recover the
    public key `Q`, or fail (every failure explicit — see
    `RecoverError`).

    Equations, each pinned by two authorities:
    * range gates `0 < r < n`, `0 < s < n`: execution-specs
      `vm/precompiled_contracts/ecrecover.py`
      (`U256(0) >= r or r >= SECP256K1N`, same for `s`); Yellow Paper
      App. F (`0 < r < secp256k1n ∧ 0 < s < secp256k1n`). They make the
      Fermat inversion below well-defined (`n` prime, `r % n ≠ 0`).
    * `e` reduced mod `n`: SEC 1 v2.0 §4.1.6 step 1.5 keeps the integer
      `e` and every use below is mod `n`; libsecp256k1 reduces on load
      (`secp256k1_scalar_set_b32`). The guest's single conditional
      subtract (`secf_reduce_once_n`) is a full reduction because
      `e < 2²⁵⁶ < 2n` — `reduce_once_eq_mod` below.
    * `u₁ = −e·r⁻¹ mod n`, `u₂ = s·r⁻¹ mod n`, `Q = u₁·G + u₂·R`
      (equivalently `Q = r⁻¹(s·R − e·G)`): SEC 1 v2.0 §4.1.6 step 1.6.1;
      libsecp256k1 `secp256k1_ecdsa_sig_recover` (`rn = r⁻¹; u1 =
      −(rn·m); u2 = rn·s; Q = u1·G + u2·R`). `r⁻¹ = r^(n−2) mod n` is
      Fermat inversion (`Accel.invMod`); that this IS the inverse is the
      named `.11.8` divergence lemma (`Crypto/Fermat.lean` plan,
      crypto-strategy §2), referenced — not re-proved — here.
    * `Q = 𝒪` is a failure: see `RecoverError.atInfinity`.

    The `(n - e % n) % n` negation agrees with the guest's
    `secf_is_zero32`-guarded `n − e` (which writes 0 when `e ≡ 0`):
    both equal `(−e) mod n`. -/
def recover (e r s recid : Nat) : Except RecoverError Point :=
  if r = 0 ∨ n ≤ r then .error .rOutOfRange
  else if s = 0 ∨ n ≤ s then .error .sOutOfRange
  else
    match decompressR r recid with
    | .error err => .error err
    | .ok rPt =>
        let rinv := Accel.invMod r n
        let u1 := (n - e % n) % n * rinv % n
        let u2 := s % n * rinv % n
        match pointAdd (scalarMul u1 (some (gx, gy)))
            (scalarMul u2 (some rPt)) with
        | none => .error .atInfinity
        | some q => .ok q

/-! ## Address derivation -/

/-- `address = keccak256(x ‖ y)[12:32]` over the 64-byte uncompressed
    public key (32-byte big-endian coordinates, no `0x04` prefix).

    Sources: Yellow Paper §4.1 eq. (324)-family `A(pr) =
    𝔅₉₆..₂₅₅(KEC(ECDSAPUBKEY(pr)))`; execution-specs `ecrecover.py`
    (`address = keccak256(public_key)[12:32]`) and
    `transactions.py` `recover_sender`. The 64-byte layout is the
    delegated library's wire format: `coincurve.PublicKey.format
    (compressed=False)[1:]` (execution-specs `secp256k1_recover`), which
    is SEC 1 §2.3.3 uncompressed encoding minus the `0x04` octet — and
    the guest's `tpr_*` output convention (BE `x ‖ y`,
    `EvmAsm/Codegen/Programs/TxPubkey.lean`).

    `keccak256` is the existing SpecRef sponge over the concrete ZisK
    permutation (`EvmAsm/Stateless/SpecRef/Crypto.lean`) — not
    re-implemented here. The precompile's left-zero-padding of the
    20-byte address to a 32-byte word is dispatch-layer framing
    (`EvmAsm/EL/Secp256k1EcrecoverResultBridge.lean`) and stays out of
    this reference. -/
def addressOfPoint (q : Point) : Bytes :=
  (keccak256 (natToBytesBE 32 q.1 ++ natToBytesBE 32 q.2)).drop 12

/-- ECRECOVER-precompile-level recovery: the `v ∈ {27, 28}` gate and
    `recid = v − 27`, then `recover` + address derivation. `none` =
    empty return data.

    Sources: execution-specs `vm/precompiled_contracts/ecrecover.py`
    (`if v != U256(27) and v != U256(28): return`, then
    `secp256k1_recover(r, s, v - U256(27), msg_hash)`); Yellow Paper
    App. F (`v ∈ {27, 28}`). The `.39`/`.40` tx-signature consumers
    apply their own `v`/`y_parity` decoding (EIP-155/EIP-2930 forms) and
    the EIP-2 low-`s` cap before calling `recover` — those gates are
    caller-side there exactly as they are in the guest. -/
def ecrecoverAddress (h v r s : Nat) : Option Bytes :=
  if v = 27 ∨ v = 28 then
    match recover h r s (v - 27) with
    | .ok q => some (addressOfPoint q)
    | .error _ => none
  else none

/-! ## Named seam lemmas -/

/-- The guest's `secf_reduce_once_n` (one conditional subtract) is a
    full reduction mod `n` on the 256-bit hash domain: for `e < 2n`,
    `(if e < n then e else e − n) = e % n`. (`2n > 2²⁵⁶` — see
    `two_n_large` below — so every 32-byte hash value qualifies.) -/
theorem reduce_once_eq_mod (e : Nat) (h : e < 2 * n) :
    (if e < n then e else e - n) = e % n := by
  by_cases hlt : e < n
  · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt, Nat.mod_eq_sub_mod (Nat.le_of_not_lt hlt),
      Nat.mod_eq_of_lt (by omega)]

/-- Every 32-byte big-endian hash value is below `2n` (kernel fact
    backing `reduce_once_eq_mod`'s hypothesis at the seam). -/
theorem two_n_large : 2 ^ 256 < 2 * n := by decide +kernel

/-! ## Known-answer tests (kernel-checked)

Provenance — two independent derivation paths per vector (recorded in
the bead and the PR):
* Path A (probe / library side): the static EEST vector embedded in
  `scripts/codegen-zisk-ecrecover-precompile-check.sh`
  (`valid_signature_1`, from `docs/eest-precompile-frontier.md`); the
  decompression cases of `scripts/codegen-zisk-secp256k1-recover-check.sh`
  (generator r for both parities, smallest non-residue r, `x = r + n ≥ p`);
  the `coincurve`/libsecp256k1 RFC 6979 signature of the
  `codegen-zisk-secp256k1-ecrecover-real-backend-probe-check.sh` message
  (`priv = 1`, `msg = sha256("evm-asm real ecrecover backend probe")`).
* Path B (independent): a from-scratch pure-Python textbook
  implementation (plain `int` + `pow`; affine chord/tangent; SEC 1
  §4.1.6 recovery; RFC 6979 §3.2 nonce for the probe vector) written for
  this bead, agreeing with Path A on every vector — including
  reproducing coincurve's RFC 6979 `(r, s, recid)` bit-for-bit — plus a
  fresh vector (`priv = 0xC0FFEE…4979`, fixed `k`) recovered by BOTH
  implementations.

All checks are `decide +kernel`: the Lean kernel (GMP-backed `Nat`)
evaluates the full 256-bit computation; no `native_decide`, no
elaborator `maxRecDepth`/heartbeat overrides. -/

/-- The generator is on the curve. -/
theorem gen_onCurve : onCurve (gx, gy) = true := by decide +kernel

/-- `n·G = 𝒪` (the ladder + case-split reach the identity where the
    group order says they must — negative-space check on `pointAdd`). -/
theorem scalarMul_order : scalarMul n (some (gx, gy)) = none := by
  decide +kernel

/-- Decompression, generator vector, even parity (probe
    `generator_parity0`): `r = Gx, recid = 0` yields `G` itself. -/
theorem decompress_gen_parity0 :
    decompressR gx 0 = .ok (gx, gy) := by decide +kernel

/-- Decompression, generator vector, odd parity (probe
    `generator_parity1`): `r = Gx, recid = 1` yields the conjugate
    `(Gx, p − Gy)`. -/
theorem decompress_gen_parity1 :
    decompressR gx 1
      = .ok (gx,
          0xB7C52588D95C3B9AA25B0403F1EEF75702E84BB7597AABE663B82F6F04EF2777)
    := by decide +kernel

/-- Decompression failure, non-residue (probe `non_residue`): `r = 5` is
    the smallest `r` with `r³ + 7` a quadratic non-residue mod `p`. -/
theorem decompress_non_residue :
    decompressR 5 0 = .error .xNotSquare := by decide +kernel

/-- Decompression failure, out of range (probe `out_of_range`):
    `r = p − 1` with recid bit 1 gives `x = r + n ≥ p`. -/
theorem decompress_out_of_range :
    decompressR (p - 1) 2 = .error .xOutOfRange := by decide +kernel

/-- `−7` is not a cube mod `p`: `(p − 7)^((p−1)/3) ≠ 1`. This pins the
    recorded execution-specs divergence (module docstring) to an empty
    input class: no `x` has `x³ + 7 ≡ 0 (mod p)`, i.e. the curve has no
    `y = 0` point, so the Euler-criterion gate and the `y² ≟ rhs` gate
    accept exactly the same inputs. -/
theorem neg7_not_cube :
    Accel.powMod (p - 7) ((p - 1) / 3) p ≠ 1 := by decide +kernel

/-- Full recovery, EEST `valid_signature_1` (probe path A:
    `codegen-zisk-ecrecover-precompile-check.sh`; path B: textbook +
    coincurve recompute — pubkey below is the shared result). `v = 28`,
    so `recid = 1`. -/
theorem recover_eest_valid_signature_1 :
    recover
      0x18C547E4F7B0F325AD1E56F57E26C745B09A3E503D86E00E5255FF7F715D3D1C
      0x73B1693892219D736CABA55BDB67216E485557EA6B6AF75F37096C9AA6A5A75F
      0xEEB940B1D03B21E36B0E47E79769F095FE2AB855BD91E3A38756B7D75A9C4549
      1
    = .ok (0x3A514176466FA815ED481FFAD09110A2D344F6C9B78C1D14AFC351C3A51BE33D,
           0x8072E77939DC03BA44790779B7A1025BAF3003F6732430E20CD9B76D953391B3)
    := by decide +kernel

/-- Address of the `valid_signature_1` pubkey — the probe's expected
    ECRECOVER output `a94f5374fce5edbc8e2a8697c15331677e6ebf0b`. -/
theorem address_eest_valid_signature_1 :
    bytesBEtoNat (addressOfPoint
      (0x3A514176466FA815ED481FFAD09110A2D344F6C9B78C1D14AFC351C3A51BE33D,
       0x8072E77939DC03BA44790779B7A1025BAF3003F6732430E20CD9B76D953391B3))
    = 0xA94F5374FCE5EDBC8E2A8697C15331677E6EBF0B := by decide +kernel

/-- Full recovery, real-backend probe vector (path A: coincurve RFC 6979
    signature of `sha256("evm-asm real ecrecover backend probe")` under
    `priv = 1`, per
    `codegen-zisk-secp256k1-ecrecover-real-backend-probe-check.sh`;
    path B: from-scratch RFC 6979 + textbook signing reproduced the same
    `(r, s, recid)`). `priv = 1` means the recovered key is `G`. -/
theorem recover_real_backend_probe :
    recover
      0x8268970637E7EC5E5732A57C1516B9BC08E10C97C69B43573EE8FCB5DB289440
      0x0F5D436BB1EE6278117F772990A5671A75E0A179467ED1D8C612FEC86BFE7FF8
      0x3F447738ECD57BC8B22B54E23AFCF109DB1D86CA8D17F60AD45E98F4526E71AF
      0
    = .ok (gx, gy) := by decide +kernel

/-- Full recovery, independent vector (path B generated: `priv =
    0xC0FFEE254729296A45A3885639AC7E10F9D54979`, `e =
    sha256("evm-asm 4ch8f.38.1 independent KAT")`, `k =
    0x1234…CDEF`; path A cross-check: coincurve recovers the same
    pubkey). -/
theorem recover_independent_vector :
    recover
      0x11231FE21C44D87DD72EE6456267066DF8226784CA912B1D3020C7348E851959
      0xBB50E2D89A4ED70663D080659FE0AD4B9BC3E06C17A227433966CB59CEEE020D
      0x5AA713217EAFF6BF62AFEA8B901AB3C6B77BC5FF1A466AF565A4D6250ED8C586
      0
    = .ok (0xC03457AEBB04B5343EE14B08F89A57BD842A7F6F1D39EC63A8CACC95CDEEA779,
           0x9BCD9CA350448E320E418C2F44B64087CE652A86004586E9A2D6C9661E74DF60)
    := by decide +kernel

/-- Recovery hits the identity: with `R = G` (`r = Gx`, even parity) and
    `s ≡ e (mod n)`, `Q = (−e·r⁻¹)·G + (e·r⁻¹)·G = 𝒪` — the
    `.atInfinity` failure is reachable and reported (the crafted
    "wrong-but-decodable" corner the reviewer checklist calls out). -/
theorem recover_at_infinity :
    recover 1 gx 1 0 = .error .atInfinity := by decide +kernel

/-- Precompile-level gate KATs (probe cases `invalid_v_29` / `zero_r`,
    plus the remaining execution-specs gates; all short-circuit before
    any curve math). -/
theorem ecrecover_gates :
    (ecrecoverAddress 0 29 1 1 = none)
      ∧ (ecrecoverAddress 0 28 0 1 = none)
      ∧ (ecrecoverAddress 0 28 n 1 = none)
      ∧ (ecrecoverAddress 0 28 1 0 = none)
      ∧ (ecrecoverAddress 0 28 1 n = none)
      ∧ (ecrecoverAddress 0 0 1 1 = none) := by decide +kernel

/-- End-to-end ECRECOVER on `valid_signature_1`: input words to 20-byte
    address (the exact probe check, `v = 28`). -/
theorem ecrecover_eest_valid_signature_1 :
    (ecrecoverAddress
      0x18C547E4F7B0F325AD1E56F57E26C745B09A3E503D86E00E5255FF7F715D3D1C
      28
      0x73B1693892219D736CABA55BDB67216E485557EA6B6AF75F37096C9AA6A5A75F
      0xEEB940B1D03B21E36B0E47E79769F095FE2AB855BD91E3A38756B7D75A9C4549).map
        bytesBEtoNat
    = some 0xA94F5374FCE5EDBC8E2A8697C15331677E6EBF0B := by decide +kernel

end EvmAsm.Stateless.SpecRef.Secp256k1
