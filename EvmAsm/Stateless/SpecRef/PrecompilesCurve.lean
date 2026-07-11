/-
  EvmAsm.Stateless.SpecRef.PrecompilesCurve

  Curve precompiles of
  `execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) whose math fits affine
  short-Weierstrass arithmetic:

  * `alt_bn128.py` — functions `bytes_to_g1`, `alt_bn128_add`,
    `alt_bn128_mul` (Python delegates the curve ops to
    `py_ecc.optimized_bn128`); the pairing check (`alt_bn128_pairing_check`)
    needs the Fp12 tower and stays on the unimplemented list.
  * `p256verify.py` — function `p256verify`, with
    `ethereum/crypto/elliptic_curve.py` `SECP256R1*` /
    `is_on_curve_secp256r1` / `secp256r1_verify`
    (`execution-specs/src/ethereum/crypto/elliptic_curve.py`, function
    `secp256r1_verify` — Python delegates to the `cryptography`
    library; the ECDSA verification equation is implemented here
    directly, `#guard`-pinned to a generated vector).

  Generic affine Weierstrass helpers (`y² = x³ + ax + b` over a prime
  field) serve both curves; scalar multiplication is fueled by the
  256-bit scalar width (structural, kernel-reducible).
-/

import EvmAsm.Stateless.SpecRef.PrecompilesHash

namespace EvmAsm.Stateless.SpecRef

/-! ## Generic affine short-Weierstrass arithmetic -/

namespace Weier

/-- Affine point; `none` = the point at infinity. -/
abbrev Pt := Option (Nat × Nat)

/-- Point doubling over `p` with curve parameter `a` (`a` given mod `p`). -/
def double (p a : Nat) : Pt → Pt
  | none => none
  | some (x, y) =>
      if y == 0 then none
      else
        let l := (3 * x * x + a) % p * EvmAsm.Rv64.Accel.invMod (2 * y % p) p % p
        let x' := (l * l + 2 * p * p - 2 * x) % p
        let y' := (l * (x + p - x') + p * p - y) % p
        some (x', y')

/-- Point addition. -/
def add (p a : Nat) : Pt → Pt → Pt
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
      if x1 == x2 then
        if (y1 + y2) % p == 0 then none
        else double p a (some (x1, y1))
      else
        let l := (y2 + p - y1) % p * EvmAsm.Rv64.Accel.invMod ((x2 + p - x1) % p) p % p
        let x' := (l * l + 2 * p * p - x1 - x2) % p
        let y' := (l * (x1 + p - x') + p * p - y1) % p
        some (x', y')

/-- Fueled double-and-add scalar multiplication (fuel ≥ bit length of
    `k`; 512 covers every 256-bit scalar with headroom). -/
def mulAux (p a : Nat) : Nat → Nat → Pt → Pt → Pt
  | 0, _, _, acc => acc
  | fuel + 1, k, base, acc =>
      if k == 0 then acc
      else
        let acc := if k % 2 == 1 then add p a acc base else acc
        mulAux p a fuel (k / 2) (double p a base) acc

def mul (p a : Nat) (k : Nat) (pt : Pt) : Pt := mulAux p a 512 k pt none

end Weier

/-! ## `alt_bn128.py` — `bytes_to_g1`, `alt_bn128_add`, `alt_bn128_mul` -/

namespace Bn128

def fieldModulus : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- `bytes_to_g1(data)` — bounds + on-curve (`y² = x³ + 3`) checks;
    `(0, 0)` is the point at infinity. -/
def bytes_to_g1 (data : Bytes) : Except EvmError Weier.Pt := do
  let x := bytesBEtoNat (data.take 32)
  let y := bytesBEtoNat ((data.drop 32).take 32)
  if x ≥ fieldModulus || y ≥ fieldModulus then
    throw (.invalidParameter "Invalid field element")
  if x == 0 && y == 0 then
    pure none
  else if (y * y) % fieldModulus == (x * x * x + 3) % fieldModulus then
    pure (some (x, y))
  else
    throw (.invalidParameter "Point is not on curve")

def ptBytes : Weier.Pt → Bytes
  | none => List.replicate 64 0x00
  | some (x, y) => natToBytesBE 32 x ++ natToBytesBE 32 y

end Bn128

namespace GasCosts
def PRECOMPILE_ECADD : Uint := 150
def PRECOMPILE_ECMUL : Uint := 6000
def PRECOMPILE_P256VERIFY : Uint := 6900
end GasCosts

/-- `alt_bn128_add(evm)`: an `InvalidParameter` becomes `OutOfGasError`. -/
def pAltBn128Add : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  charge_gas GasCosts.PRECOMPILE_ECADD
  let p0 ← match Bn128.bytes_to_g1 (buffer_read data 0 64) with
    | .ok p => pure p | .error _ => throw .outOfGas
  let p1 ← match Bn128.bytes_to_g1 (buffer_read data 64 64) with
    | .ok p => pure p | .error _ => throw .outOfGas
  let p := Weier.add Bn128.fieldModulus 0 p0 p1
  EvmM.modifyEvm (fun e => { e with output := Bn128.ptBytes p })

/-- `alt_bn128_mul(evm)`. -/
def pAltBn128Mul : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  charge_gas GasCosts.PRECOMPILE_ECMUL
  let p0 ← match Bn128.bytes_to_g1 (buffer_read data 0 64) with
    | .ok p => pure p | .error _ => throw .outOfGas
  let n := bytesBEtoNat (buffer_read data 64 32)
  let p := Weier.mul Bn128.fieldModulus 0 n p0
  EvmM.modifyEvm (fun e => { e with output := Bn128.ptBytes p })

/-! ## `p256verify.py` (EIP-7951 / RIP-7212) -/

namespace P256

def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
def n : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
def a : Nat := p - 3
def b : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
def gx : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
def gy : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- `is_on_curve_secp256r1(x, y)`. -/
def is_on_curve (x y : Nat) : Bool :=
  (y * y) % p == (x * x * x + a * x + b) % p

/-- The ECDSA verification equation (`secp256r1_verify` delegates to
    the `cryptography` library; both hash and `n` are 256-bit, so
    `e = int(msg_hash)`): valid iff `R = u₁·G + u₂·Q ≠ ∞` and
    `R.x ≡ r (mod n)`. -/
def verify (r s qx qy : Nat) (msg_hash : Bytes) : Bool :=
  let e := bytesBEtoNat msg_hash
  let sInv := EvmAsm.Rv64.Accel.invMod (s % n) n
  let u1 := e % n * sInv % n
  let u2 := r % n * sInv % n
  match Weier.add p a (Weier.mul p a u1 (some (gx, gy)))
      (Weier.mul p a u2 (some (qx, qy))) with
  | none => false
  | some (x, _) => x % n == r % n

end P256

/-- `p256verify(evm)` (`p256verify.py`, function `p256verify`): 32-byte
    one on success, empty output on any failure. -/
def pP256Verify : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  charge_gas GasCosts.PRECOMPILE_P256VERIFY
  if data.length ≠ 160 then return
  let msg_hash := buffer_read data 0 32
  let r := bytesBEtoNat (buffer_read data 32 32)
  let s := bytesBEtoNat (buffer_read data 64 32)
  let qx := bytesBEtoNat (buffer_read data 96 32)
  let qy := bytesBEtoNat (buffer_read data 128 32)
  if r == 0 || r ≥ P256.n then return
  if s == 0 || s ≥ P256.n then return
  if qx ≥ P256.p || qy ≥ P256.p then return
  if qx == 0 && qy == 0 then return
  if !P256.is_on_curve qx qy then return
  if P256.verify r s qx qy msg_hash then
    EvmM.modifyEvm (fun e => { e with output := natToBytesBE 32 1 })

/-! ## Sanity checks (bn128 vectors from `py_ecc.optimized_bn128`;
p256 vector generated with the `cryptography` library — generator
snippets in the PR description) -/

private def bnG : Weier.Pt := some (1, 2)

-- 2G, 3G = 2G + G, and a large scalar multiple.
#guard Weier.double Bn128.fieldModulus 0 bnG == some
  (0x030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd3,
   0x15ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4)
#guard Weier.add Bn128.fieldModulus 0 (Weier.double Bn128.fieldModulus 0 bnG) bnG == some
  (0x0769bf9ac56bea3ff40232bcb1b6bd159315d84715b8e679f2d355961915abf0,
   0x2ab799bee0489429554fdb7c8d086475319e63b40b9c5b57cdf1ff3dd9fe2261)
#guard Weier.mul Bn128.fieldModulus 0 0xdeadbeefcafe bnG == some
  (0x1efa80afa3d604f773ea51a1f62b49af4726290c8a8e2bb6d40ddced3e49b804,
   0x1b48a4dbd17faaa7ab2de8a0453500adb0ef18aecbe153539201342c4c8326c6)
-- G + (-G) = ∞; k·∞ = ∞; off-curve and out-of-field points reject.
#guard Weier.add Bn128.fieldModulus 0 bnG
  (some (1, Bn128.fieldModulus - 2)) == none
#guard Weier.mul Bn128.fieldModulus 0 5 none == none
#guard match Bn128.bytes_to_g1 (natToBytesBE 32 1 ++ natToBytesBE 32 3) with
  | .error (.invalidParameter _) => true | _ => false
#guard match Bn128.bytes_to_g1 (natToBytesBE 32 Bn128.fieldModulus ++ natToBytesBE 32 2) with
  | .error (.invalidParameter _) => true | _ => false
#guard (Bn128.bytes_to_g1 (List.replicate 64 0x00)).toOption == some none

-- P-256: a signature generated with the `cryptography` library over
-- msg_hash = 00 01 … 1f verifies; a perturbed r does not.
private def p256MsgHash : Bytes := (List.range 32).map (BitVec.ofNat 8)
private def p256R : Nat := 0x1c9e80a037c9efcadb4a621d743d767c4a7a9befb4a3df588bfb56d77bb4feb2
private def p256S : Nat := 0x625588ff92b4979bdfe20a43869d2ae673a2c35bb8b5a0a865a0e037004073c6
private def p256Qx : Nat := 0x9fad84aeae08bbef7f010014d82cef6a09de2b0cf871b5ce0c4f1d13a59a5934
private def p256Qy : Nat := 0x07cb45769f1070e2c2470fe5b1bfe63133c0b0cdc64ea4bf3791a8ec2a07fd4f

#guard P256.is_on_curve P256.gx P256.gy
#guard P256.is_on_curve p256Qx p256Qy
#guard P256.verify p256R p256S p256Qx p256Qy p256MsgHash == true
#guard P256.verify (p256R + 1) p256S p256Qx p256Qy p256MsgHash == false

end EvmAsm.Stateless.SpecRef
