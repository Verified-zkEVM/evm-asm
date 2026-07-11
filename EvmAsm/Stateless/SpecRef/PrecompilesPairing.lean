/-
  EvmAsm.Stateless.SpecRef.PrecompilesPairing

  `alt_bn128_pairing_check` of
  `execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/alt_bn128.py`
  (`@tests-zkevm@v0.5.0`, `bd8c673`, function `alt_bn128_pairing_check`
  with `bytes_to_g2`) — the Python delegates the pairing to
  `py_ecc.optimized_bn128`; this module ports that reference
  implementation faithfully:

  * `FQP` — fixed-degree polynomial extension fields over `F_p`
    (`py_ecc/fields/optimized_field_elements.py`, class `FQP`):
    multiplication with modulus-polynomial reduction, extended-Euclid
    inversion (`inv` / `optimized_poly_rounded_div`), fueled `pow`.
  * projective (`x/z`, `y/z`) curve arithmetic generic over the field
    (`py_ecc/optimized_bn128/optimized_curve.py`: `double`, `add`,
    `multiply`, `eq`, `is_inf`).
  * `twist`, `cast_point_to_fq12`, `linefunc`, `miller_loop` (with the
    64-entry `pseudo_binary_encoding`), `pairing`
    (`py_ecc/optimized_bn128/optimized_pairing.py`).

  Loops are fueled structurally (scalar bits / Euclid degree /
  exponent bits) with strict over-approximations; exhaustion is
  unreachable.  Pairing evaluation is expensive (final exponentiation
  is a ~4500-bit power), so correctness is exercised by the compiled
  EEST run and `#eval` smoke checks rather than kernel `#guard`s;
  the cheap field-algebra identities are `#guard`-pinned below.
-/

import EvmAsm.Stateless.SpecRef.PrecompilesCurve

namespace EvmAsm.Stateless.SpecRef

namespace Bn128

/-! ## Polynomial extension fields (`FQP`) -/

/-- Coefficients mod `p`, lowest degree first, length = the degree. -/
abbrev FQP := List Nat

def bnP : Nat := fieldModulus

/-- `(i, c)` pairs of the nonzero modulus-polynomial coefficients. -/
def fq2MC : List (Nat × Int) := [(0, 1)]
def fq12MC : List (Nat × Int) := [(0, 82), (6, -18)]

private def imod (x : Int) : Nat := ((x % (bnP : Int) + bnP) % (bnP : Int)).toNat

/-- `FQP.__mul__`: schoolbook product then reduction by the modulus
    polynomial (`b[exp+i] -= top * c` walking the top coefficients
    down). -/
def fqpMul (deg : Nat) (mc : List (Nat × Int)) (xs ys : FQP) : FQP := Id.run do
  let mut b : Array Int := .replicate (2 * deg - 1) 0
  for i in [0:deg] do
    let xi : Int := xs.getD i 0
    if xi != 0 then
      for j in [0:deg] do
        b := b.set! (i + j) (b[i + j]! + xi * (ys.getD j 0 : Int))
  for k in [0:deg-1] do
    let exp := deg - 2 - k
    let top := b[b.size - 1]!
    b := b.pop
    for (i, c) in mc do
      b := b.set! (exp + i) (b[exp + i]! - top * c)
  pure ((List.range deg).map (fun i => imod b[i]!))

def fqpAdd (xs ys : FQP) : FQP := xs.zipWith (fun a b => (a + b) % bnP) ys
def fqpSub (deg : Nat) (xs ys : FQP) : FQP :=
  (List.range deg).map (fun i => (xs.getD i 0 + bnP - ys.getD i 0 % bnP) % bnP)
def fqpZero (deg : Nat) : FQP := List.replicate deg 0
def fqpOne (deg : Nat) : FQP := 1 :: List.replicate (deg - 1) 0

/-- Degree of an `Int` polynomial (`deg`). -/
private def polyDeg (l : List Int) : Nat := Id.run do
  let mut d := l.length - 1
  for _ in [0:l.length] do
    if d > 0 && l.getD d 0 == 0 then d := d - 1
  pure d

/-- `optimized_poly_rounded_div(a, b)` over `F_p`. -/
private def polyRoundedDiv (a b : List Int) : List Int := Id.run do
  let dega := polyDeg a
  let degb := polyDeg b
  let bInv : Int := EvmAsm.Rv64.Accel.invMod (imod (b.getD degb 0)) bnP
  let mut temp : Array Int := a.toArray
  let mut o : Array Int := .replicate a.length 0
  for k in [0:dega + 1 - degb] do
    let i := dega - degb - k
    o := o.set! i (o[i]! + temp[degb + i]! * bInv)
    for c in [0:degb + 1] do
      temp := temp.set! (c + i) (temp[c + i]! - o[c]!)
  pure ((List.range (polyDeg o.toList + 1)).map (fun i => (imod o[i]! : Int)))

/-- `FQP.inv`: extended Euclid over `F_p[x]` with py_ecc's quirky
    rounded division, which reduces the degree slowly (empirically 22
    iterations at degree 12); over-fueled at `12·deg + 16` — the loop
    no-ops once `deg(low) = 0`, so extra fuel is harmless, and py_ecc's
    own `while deg(low)` terminates on every input the pairing feeds
    it. -/
def fqpInv (deg : Nat) (mcFull : List Int) (coeffs : FQP) : FQP := Id.run do
  let mut lm : List Int := 1 :: List.replicate deg 0
  let mut hm : List Int := List.replicate (deg + 1) 0
  let mut low : List Int := coeffs.map (fun c => ((c : Nat) : Int)) ++ [0]
  let mut high : List Int := mcFull ++ [1]
  for _ in [0:12 * deg + 16] do
    if polyDeg low != 0 then
      let r0 := polyRoundedDiv high low
      let r := r0 ++ List.replicate (deg + 1 - r0.length) 0
      let mut nm := hm.toArray
      let mut new := high.toArray
      for i in [0:deg + 1] do
        for j in [0:deg + 1 - i] do
          nm := nm.set! (i + j) (nm[i + j]! - lm.getD i 0 * r.getD j 0)
          new := new.set! (i + j) (new[i + j]! - low.getD i 0 * r.getD j 0)
      hm := lm; high := low
      lm := nm.toList.map (fun x => (imod x : Int))
      low := new.toList.map (fun x => (imod x : Int))
  let lowInv : Int := EvmAsm.Rv64.Accel.invMod (imod (low.getD 0 0)) bnP
  pure ((List.range deg).map (fun i => imod (lm.getD i 0 * lowInv)))

/-- Fueled square-and-multiply power (exponents up to ~4600 bits for
    the final exponentiation). -/
def fqpPowAux (deg : Nat) (mc : List (Nat × Int)) :
    Nat → FQP → Nat → FQP → FQP
  | 0, _, _, acc => acc
  | fuel + 1, base, e, acc =>
      if e == 0 then acc
      else
        let acc := if e % 2 == 1 then fqpMul deg mc acc base else acc
        fqpPowAux deg mc fuel (fqpMul deg mc base base) (e / 2) acc

def fqpPow (deg : Nat) (mc : List (Nat × Int)) (base : FQP) (e : Nat) : FQP :=
  fqpPowAux deg mc 4700 base e (fqpOne deg)

/-! ## Generic field record + projective curve arithmetic -/

structure FieldOps (α : Type) where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  inv : α → α
  zero : α
  one : α
  beq : α → α → Bool

def fqOps : FieldOps Nat :=
  { add := fun a b => (a + b) % bnP
    sub := fun a b => (a + bnP - b % bnP) % bnP
    mul := fun a b => a * b % bnP
    inv := fun a => EvmAsm.Rv64.Accel.invMod a bnP
    zero := 0, one := 1
    beq := (· == ·) }

def fqpOps (deg : Nat) (mc : List (Nat × Int)) (mcFull : List Int) : FieldOps FQP :=
  { add := fqpAdd
    sub := fqpSub deg
    mul := fqpMul deg mc
    inv := fqpInv deg mcFull
    zero := fqpZero deg, one := fqpOne deg
    beq := fun a b => (List.range deg).all (fun i => a.getD i 0 == b.getD i 0) }

def fq2Ops : FieldOps FQP := fqpOps 2 fq2MC [1, 0]
def fq12Ops : FieldOps FQP :=
  fqpOps 12 fq12MC [82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0]

/-- Projective point `(x, y, z)` (`z = 0` ⇒ infinity). -/
abbrev Proj (α : Type) := α × α × α

variable {α : Type}

/-- `optimized_curve.double`. -/
def pDouble (F : FieldOps α) (pt : Proj α) : Proj α :=
  let (x, y, z) := pt
  let W := F.mul (F.add x (F.add x x)) x       -- 3x·x
  let S := F.mul y z
  let B := F.mul (F.mul x y) S
  let B8 := F.add (F.add (F.add B B) (F.add B B)) (F.add (F.add B B) (F.add B B))
  let H := F.sub (F.mul W W) B8
  let S2 := F.mul S S
  let newx := F.mul (F.add H H) S
  let B4 := F.add (F.add B B) (F.add B B)
  let y2S2 := F.mul (F.mul y y) S2
  let y2S2_8 := F.add (F.add (F.add y2S2 y2S2) (F.add y2S2 y2S2))
    (F.add (F.add y2S2 y2S2) (F.add y2S2 y2S2))
  let newy := F.sub (F.mul W (F.sub B4 H)) y2S2_8
  let SS2 := F.mul S S2
  let newz := F.add (F.add (F.add SS2 SS2) (F.add SS2 SS2))
    (F.add (F.add SS2 SS2) (F.add SS2 SS2))
  (newx, newy, newz)

/-- `optimized_curve.add`. -/
def pAdd (F : FieldOps α) (p1 p2 : Proj α) : Proj α :=
  if F.beq p1.2.2 F.zero then p2
  else if F.beq p2.2.2 F.zero then p1
  else
    let (x1, y1, z1) := p1
    let (x2, y2, z2) := p2
    let U1 := F.mul y2 z1
    let U2 := F.mul y1 z2
    let V1 := F.mul x2 z1
    let V2 := F.mul x1 z2
    if F.beq V1 V2 && F.beq U1 U2 then pDouble F p1
    else if F.beq V1 V2 then (F.one, F.one, F.zero)
    else
      let U := F.sub U1 U2
      let V := F.sub V1 V2
      let V2sq := F.mul V V
      let V2sqV2 := F.mul V2sq V2
      let V3 := F.mul V V2sq
      let W := F.mul z1 z2
      let A := F.sub (F.sub (F.mul (F.mul U U) W) V3) (F.add V2sqV2 V2sqV2)
      (F.mul V A,
       F.sub (F.mul U (F.sub V2sqV2 A)) (F.mul V3 U2),
       F.mul V3 W)

/-- `optimized_curve.multiply`, fueled by 512 (scalars < 2²⁵⁶). -/
def pMulAux (F : FieldOps α) : Nat → Proj α → Nat → Proj α → Proj α
  | 0, _, _, acc => acc
  | fuel + 1, base, n, acc =>
      if n == 0 then acc
      else
        let acc := if n % 2 == 1 then pAdd F acc base else acc
        pMulAux F fuel (pDouble F base) (n / 2) acc

def pMul (F : FieldOps α) (pt : Proj α) (n : Nat) : Proj α :=
  pMulAux F 512 pt n (F.one, F.one, F.zero)

def pIsInf (F : FieldOps α) (pt : Proj α) : Bool := F.beq pt.2.2 F.zero

/-! ## Twist / cast / line function / Miller loop
(`optimized_pairing.py`) -/

def curveOrder : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- `w = FQ12([0, 1, 0, …])` and its powers used by `twist`. -/
private def w2 : FQP := fqpPow 12 fq12MC (0 :: 1 :: List.replicate 10 0) 2
private def w3 : FQP := fqpPow 12 fq12MC (0 :: 1 :: List.replicate 10 0) 3

/-- `twist(pt)`: `E(FQ2) → E(FQ12)` via the field isomorphism
    `x² + 1 → x² − 18x + 82` embedding. -/
def twist (pt : Proj FQP) : Proj FQP :=
  let emb := fun (c : FQP) =>
    let c0 := c.getD 0 0
    let c1 := c.getD 1 0
    -- coeffs[0] - 9·coeffs[1] at slot 0, coeffs[1] at slot 6
    ((c0 + 9 * (bnP - c1 % bnP)) % bnP) :: List.replicate 5 0
      ++ [c1] ++ List.replicate 5 0
  let (x, y, z) := pt
  (fqpMul 12 fq12MC (emb x) w2, fqpMul 12 fq12MC (emb y) w3, emb z)

/-- `cast_point_to_fq12(pt)`. -/
def castToFq12 (pt : Proj Nat) : Proj FQP :=
  let lift := fun (n : Nat) => n :: List.replicate 11 0
  (lift pt.1, lift pt.2.1, lift pt.2.2)

/-- `linefunc(P1, P2, T)`: `(numerator, denominator)`. -/
def linefunc (F : FieldOps α) (P1 P2 T : Proj α) : α × α :=
  let (x1, y1, z1) := P1
  let (x2, y2, z2) := P2
  let (xt, yt, zt) := T
  let mNum := F.sub (F.mul y2 z1) (F.mul y1 z2)
  let mDen := F.sub (F.mul x2 z1) (F.mul x1 z2)
  if !(F.beq mDen F.zero) then
    (F.sub (F.mul mNum (F.sub (F.mul xt z1) (F.mul x1 zt)))
       (F.mul mDen (F.sub (F.mul yt z1) (F.mul y1 zt))),
     F.mul (F.mul mDen zt) z1)
  else if F.beq mNum F.zero then
    let mNum := F.mul (F.add x1 (F.add x1 x1)) x1
    let mDen := F.mul (F.add y1 y1) z1
    (F.sub (F.mul mNum (F.sub (F.mul xt z1) (F.mul x1 zt)))
       (F.mul mDen (F.sub (F.mul yt z1) (F.mul y1 zt))),
     F.mul (F.mul mDen zt) z1)
  else
    (F.sub (F.mul xt z1) (F.mul x1 zt), F.mul z1 zt)

/-- `pseudo_binary_encoding[63::-1]` — the Miller-loop schedule, most
    significant first (the list literal reversed, last entry dropped). -/
private def millerSchedule : List Int :=
  [0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0,
   0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1,
   1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1,
   1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1].take 64 |>.reverse

/-- `neg(pt)` over FQ12. -/
private def pNeg12 (pt : Proj FQP) : Proj FQP :=
  (pt.1, fqpSub 12 (fqpZero 12) pt.2.1, pt.2.2)

/-- `miller_loop(Q, P, final_exponentiate=True)`. -/
def miller_loop (Q P : Proj FQP) : FQP := Id.run do
  let F := fq12Ops
  let mut R := Q
  let mut fNum := F.one
  let mut fDen := F.one
  for v in millerSchedule do
    let (n, d) := linefunc F R R P
    fNum := F.mul (F.mul fNum fNum) n
    fDen := F.mul (F.mul fDen fDen) d
    R := pDouble F R
    if v == 1 then
      let (n, d) := linefunc F R Q P
      fNum := F.mul fNum n
      fDen := F.mul fDen d
      R := pAdd F R Q
    else if v == -1 then
      let nQ := pNeg12 Q
      let (n, d) := linefunc F R nQ P
      fNum := F.mul fNum n
      fDen := F.mul fDen d
      R := pAdd F R nQ
  let frob := fun (c : FQP) => fqpPow 12 fq12MC c bnP
  let Q1 := (frob Q.1, frob Q.2.1, frob Q.2.2)
  let nQ2 := (frob Q1.1, fqpSub 12 (fqpZero 12) (frob Q1.2.1), frob Q1.2.2)
  let (n1, d1) := linefunc F R Q1 P
  let R' := pAdd F R Q1
  let (n2, d2) := linefunc F R' nQ2 P
  let f := F.mul (F.mul fNum n1) n2
  let g := F.mul (F.mul fDen d1) d2
  let f := F.mul f (F.inv g)
  pure (fqpPow 12 fq12MC f ((bnP^12 - 1) / curveOrder))

/-- `pairing(Q, P)` on already-validated points (the precompile checks
    curve membership before calling); infinities pair to one. -/
def pairing (Q : Proj FQP) (P : Proj Nat) : FQP :=
  if pIsInf fq2Ops Q || pIsInf fqOps P then fqpOne 12
  else miller_loop (twist Q) (castToFq12 P)

/-- `bytes_to_g2(data)` — bounds + on-curve (`y² = x³ + b2`,
    `b2 = 3/(9+i)`) checks over FQ2; big-endian `(x1‖x0‖y1‖y0)` with
    the IMAGINARY part first on the wire. -/
def bytes_to_g2 (data : Bytes) : Except EvmError (Proj FQP) := do
  let x1 := bytesBEtoNat (data.take 32)
  let x0 := bytesBEtoNat ((data.drop 32).take 32)
  let y1 := bytesBEtoNat ((data.drop 64).take 32)
  let y0 := bytesBEtoNat ((data.drop 96).take 32)
  if x0 ≥ bnP || x1 ≥ bnP || y0 ≥ bnP || y1 ≥ bnP then
    throw (.invalidParameter "Invalid field element")
  let x : FQP := [x0, x1]
  let y : FQP := [y0, y1]
  let F := fq2Ops
  if F.beq x F.zero && F.beq y F.zero then
    pure (F.one, F.one, F.zero)
  else
    -- b2 = FQ2([3, 0]) / FQ2([9, 1])
    let b2 := fqpMul 2 fq2MC [3, 0] (fqpInv 2 [1, 0] [9, 1])
    if F.beq (F.mul y y) (F.add (F.mul (F.mul x x) x) b2) then
      pure (x, y, F.one)
    else
      throw (.invalidParameter "Point is not on curve")

end Bn128

namespace GasCosts
def PRECOMPILE_ECPAIRING_BASE : Uint := 45000
def PRECOMPILE_ECPAIRING_PER_POINT : Uint := 34000
end GasCosts

/-- `alt_bn128_pairing_check(evm)`. -/
def pAltBn128PairingCheck : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  charge_gas (GasCosts.PRECOMPILE_ECPAIRING_PER_POINT * (data.length / 192)
    + GasCosts.PRECOMPILE_ECPAIRING_BASE)
  if data.length % 192 ≠ 0 then throw .outOfGas
  let F := Bn128.fq12Ops
  let mut result := F.one
  for i in [0:data.length / 192] do
    let p ← match Bn128.bytes_to_g1 (buffer_read data (192 * i) 64) with
      | .ok (some (x, y)) => pure ((x, y, 1) : Bn128.Proj Nat)
      | .ok none => pure ((1, 1, 0) : Bn128.Proj Nat)
      | .error _ => throw .outOfGas
    let q ← match Bn128.bytes_to_g2 (buffer_read data (192 * i + 64) 128) with
      | .ok q => pure q
      | .error _ => throw .outOfGas
    if !Bn128.pIsInf Bn128.fqOps (Bn128.pMul Bn128.fqOps p Bn128.curveOrder) then
      throw .outOfGas
    if !Bn128.pIsInf Bn128.fq2Ops (Bn128.pMul Bn128.fq2Ops q Bn128.curveOrder) then
      throw .outOfGas
    result := F.mul result (Bn128.pairing q p)
  EvmM.modifyEvm (fun e =>
    { e with output := natToBytesBE 32 (if F.beq result F.one then 1 else 0) })

/-! ## Sanity checks (cheap field algebra; the pairing itself is
exercised by compiled smoke checks + the EEST run) -/

section
open Bn128

-- FQ2: (9 + i)·(9 + i)⁻¹ = 1; i² = −1.
#guard fqpMul 2 fq2MC [9, 1] (fqpInv 2 [1, 0] [9, 1]) == [1, 0]
#guard fqpMul 2 fq2MC [0, 1] [0, 1] == [bnP - 1, 0]

-- FQ12: w·w¹¹ = w¹² = 18w⁶ − 82; x·x⁻¹ = 1 on a nontrivial element.
#guard
  let w : FQP := 0 :: 1 :: List.replicate 10 0
  fqpMul 12 fq12MC w (fqpPow 12 fq12MC w 11)
    == ((bnP - 82) :: List.replicate 5 0) ++ [18] ++ List.replicate 5 0
#guard
  let x : FQP := (List.range 12).map (fun i => i * i + 3)
  fqpMul 12 fq12MC x (fqpInv 12 [82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0] x)
    == fqpOne 12

-- Projective FQ ops agree with the affine ops on 2G / 5G.
#guard
  let g : Proj Nat := (1, 2, 1)
  let d := pDouble fqOps g
  let aff := Weier.double fieldModulus 0 (some (1, 2))
  match aff with
  | some (x, y) => fqOps.beq (fqOps.mul x d.2.2) d.1
      && fqOps.beq (fqOps.mul y d.2.2) d.2.1
  | none => false
#guard
  let g : Proj Nat := (1, 2, 1)
  let m := pMul fqOps g 5
  match Weier.mul fieldModulus 0 5 (some (1, 2)) with
  | some (x, y) => fqOps.beq (fqOps.mul x m.2.2) m.1
      && fqOps.beq (fqOps.mul y m.2.2) m.2.1
  | none => false

end

end EvmAsm.Stateless.SpecRef
