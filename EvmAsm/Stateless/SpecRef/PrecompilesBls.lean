/-
  EvmAsm.Stateless.SpecRef.PrecompilesBls

  The BLS12-381 precompiles (EIP-2537) of
  `execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/bls12_381/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`):

  * `__init__.py` — the decode/encode helpers (`bytes_to_fq`,
    `bytes_to_fq2`, `bytes_to_g1`, `bytes_to_g2`, `g1_to_bytes`,
    `g2_to_bytes`, `decode_g1_scalar_pair`, `decode_g2_scalar_pair`)
    and the MSM discount tables (`G1_K_DISCOUNT`, `G2_K_DISCOUNT`)
  * `bls12_381_g1.py` — functions `bls12_g1_add`, `bls12_g1_msm`
  * `bls12_381_g2.py` — functions `bls12_g2_add`, `bls12_g2_msm`
  * `bls12_381_pairing.py` — function `bls12_pairing`

  The pairing is the `py_ecc.optimized_bls12_381` reference: a plain
  63-entry binary Miller loop with the per-iteration twist (BLS
  M-twist embedding: `x → w¹·/w⁷`, `y → w⁰/w⁶`, `z → w³/w⁹` slots) and
  no Frobenius tail, over the shared generic `FQP`/projective
  machinery of `PrecompilesPairing.lean`.

  `bls12_map_fp_to_g1` / `bls12_map_fp2_to_g2` (SSWU + isogeny) are
  NOT here yet and stay on the unimplemented-fallback list.
-/

import EvmAsm.Stateless.SpecRef.PrecompilesPairing

namespace EvmAsm.Stateless.SpecRef

namespace Bls12

open Bn128 (FQP FieldOps Proj fqpMul fqpInv fqpPow fqpSub fqpZero fqpOne
  fqOpsP fqpOps pDouble pAdd pMul pIsInf linefunc imodP)

/-! ## Field constants -/

def blsP : Nat := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
def blsOrder : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def fq2MC : List (Nat × Int) := [(0, 1)]
def fq12MC : List (Nat × Int) := [(0, 2), (6, -2)]

def fqOps : FieldOps Nat := fqOpsP blsP
def fq2Ops : FieldOps FQP := fqpOps blsP 2 fq2MC [1, 0]
def fq12Ops : FieldOps FQP :=
  fqpOps blsP 12 fq12MC [2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0]

/-! ## MSM gas discount tables (`__init__.py`) -/

def G1_K_DISCOUNT : List Nat :=
  [1000, 949, 848, 797, 764, 750, 738, 728, 719, 712, 705, 698, 692, 687, 682, 677,
   673, 669, 665, 661, 658, 654, 651, 648, 645, 642, 640, 637, 635, 632, 630, 627,
   625, 623, 621, 619, 617, 615, 613, 611, 609, 608, 606, 604, 603, 601, 599, 598,
   596, 595, 593, 592, 591, 589, 588, 586, 585, 584, 582, 581, 580, 579, 577, 576,
   575, 574, 573, 572, 570, 569, 568, 567, 566, 565, 564, 563, 562, 561, 560, 559,
   558, 557, 556, 555, 554, 553, 552, 551, 550, 549, 548, 547, 547, 546, 545, 544,
   543, 542, 541, 540, 540, 539, 538, 537, 536, 536, 535, 534, 533, 532, 532, 531,
   530, 529, 528, 528, 527, 526, 525, 525, 524, 523, 522, 522, 521, 520, 520, 519]
def G2_K_DISCOUNT : List Nat :=
  [1000, 1000, 923, 884, 855, 832, 812, 796, 782, 770, 759, 749, 740, 732, 724, 717,
   711, 704, 699, 693, 688, 683, 679, 674, 670, 666, 663, 659, 655, 652, 649, 646,
   643, 640, 637, 634, 632, 629, 627, 624, 622, 620, 618, 615, 613, 611, 609, 607,
   606, 604, 602, 600, 598, 597, 595, 593, 592, 590, 589, 587, 586, 584, 583, 582,
   580, 579, 578, 576, 575, 574, 573, 571, 570, 569, 568, 567, 566, 565, 563, 562,
   561, 560, 559, 558, 557, 556, 555, 554, 553, 552, 552, 551, 550, 549, 548, 547,
   546, 545, 545, 544, 543, 542, 541, 541, 540, 539, 538, 537, 537, 536, 535, 535,
   534, 533, 532, 532, 531, 530, 530, 529, 528, 528, 527, 526, 526, 525, 524, 524]


def G1_MAX_DISCOUNT : Nat := 519
def G2_MAX_DISCOUNT : Nat := 524
def MULTIPLIER : Nat := 1000
def LENGTH_PER_PAIR_G1 : Nat := 160
def LENGTH_PER_PAIR_G2 : Nat := 288

/-! ## Decode / encode (`__init__.py`) -/

/-- `bytes_to_fq(data)`: 64-byte big-endian, `< p`. -/
def bytes_to_fq (data : Bytes) : Except EvmError Nat := do
  if data.length ≠ 64 then throw (.invalidParameter "FQ should be 64 bytes long")
  let c := bytesBEtoNat data
  if c ≥ blsP then throw (.invalidParameter "Invalid field element")
  pure c

/-- `bytes_to_fq2(data)`: `(c_0 ‖ c_1)`, each 64 bytes. -/
def bytes_to_fq2 (data : Bytes) : Except EvmError FQP := do
  if data.length ≠ 128 then throw (.invalidParameter "FQ2 input should be 128 bytes long")
  let c0 ← bytes_to_fq (data.take 64)
  let c1 ← bytes_to_fq (data.drop 64)
  pure [c0, c1]

/-- `bytes_to_g1(data, subgroup_check)`. -/
def bytes_to_g1 (data : Bytes) (subgroup_check : Bool := false) :
    Except EvmError (Proj Nat) := do
  if data.length ≠ 128 then throw (.invalidParameter "Input should be 128 bytes long")
  let x ← bytes_to_fq (data.take 64)
  let y ← bytes_to_fq (data.drop 64)
  let pt : Proj Nat := if x == 0 && y == 0 then (x, y, 0) else (x, y, 1)
  -- is_on_curve: y²z = x³ + 4z³ (projective; infinity passes)
  if pt.2.2 ≠ 0 && (y * y) % blsP ≠ (x * x * x + 4) % blsP then
    throw (.invalidParameter "G1 point is not on curve")
  if subgroup_check && !pIsInf fqOps (pMul fqOps pt blsOrder) then
    throw (.invalidParameter "Subgroup check failed for G1 point.")
  pure pt

/-- `bytes_to_g2(data, subgroup_check)` (`b2 = [4, 4]`). -/
def bytes_to_g2 (data : Bytes) (subgroup_check : Bool := false) :
    Except EvmError (Proj FQP) := do
  if data.length ≠ 256 then throw (.invalidParameter "G2 should be 256 bytes long")
  let x ← bytes_to_fq2 (data.take 128)
  let y ← bytes_to_fq2 (data.drop 128)
  let F := fq2Ops
  let pt : Proj FQP :=
    if F.beq x F.zero && F.beq y F.zero then (x, y, F.zero) else (x, y, F.one)
  if !(F.beq pt.2.2 F.zero)
      && !(F.beq (F.mul y y) (F.add (F.mul (F.mul x x) x) [4, 4])) then
    throw (.invalidParameter "Point is not on curve")
  if subgroup_check && !pIsInf F (pMul F pt blsOrder) then
    throw (.invalidParameter "Subgroup check failed for G2 point.")
  pure pt

/-- `normalize` + 64-byte big-endian coordinates (an infinity
    normalizes through `inv 0 = 0` to `(0, 0)`, exactly as py_ecc). -/
def g1_to_bytes (pt : Proj Nat) : Bytes :=
  let zi := fqOps.inv pt.2.2
  natToBytesBE 64 (fqOps.mul pt.1 zi) ++ natToBytesBE 64 (fqOps.mul pt.2.1 zi)

def fq2_to_bytes (c : FQP) : Bytes :=
  natToBytesBE 64 (c.getD 0 0) ++ natToBytesBE 64 (c.getD 1 0)

def g2_to_bytes (pt : Proj FQP) : Bytes :=
  let F := fq2Ops
  let zi := F.inv pt.2.2
  fq2_to_bytes (F.mul pt.1 zi) ++ fq2_to_bytes (F.mul pt.2.1 zi)

/-- `decode_g1_scalar_pair(data)` — subgroup-checked point + scalar. -/
def decode_g1_scalar_pair (data : Bytes) : Except EvmError (Proj Nat × Nat) := do
  if data.length ≠ 160 then throw (.invalidParameter "Input should be 160 bytes long")
  let pt ← bytes_to_g1 (data.take 128) (subgroup_check := true)
  pure (pt, bytesBEtoNat (buffer_read data 128 32))

def decode_g2_scalar_pair (data : Bytes) : Except EvmError (Proj FQP × Nat) := do
  if data.length ≠ 288 then throw (.invalidParameter "Input should be 288 bytes long")
  let pt ← bytes_to_g2 (data.take 256) (subgroup_check := true)
  pure (pt, bytesBEtoNat ((data.drop 256).take 32))

/-! ## The BLS pairing (`py_ecc/optimized_bls12_381/optimized_pairing.py`) -/

/-- The BLS M-twist embedding (`optimized_curve.twist`):
    `x` at slots 1/7, `y` at slots 0/6, `z` at slots 3/9, with the
    `c₀ − c₁` isomorphism. -/
def twist (pt : Proj FQP) : Proj FQP :=
  let pair := fun (c : FQP) => ((c.getD 0 0 + blsP - c.getD 1 0 % blsP) % blsP, c.getD 1 0)
  let put := fun (lo : Nat) (v : Nat × Nat) => Id.run do
    let mut l : Array Nat := .replicate 12 0
    l := l.set! lo v.1
    l := l.set! (lo + 6) v.2
    pure l.toList
  let (x, y, z) := pt
  (put 1 (pair x), put 0 (pair y), put 3 (pair z))

def castToFq12 (pt : Proj Nat) : Proj FQP :=
  let lift := fun (n : Nat) => n :: List.replicate 11 0
  (lift pt.1, lift pt.2.1, lift pt.2.2)

/-- `pseudo_binary_encoding[62::-1]` (63 entries, 0/1 only). -/
private def millerSchedule : List Nat :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1] : List Nat).reverse

/-- `miller_loop(Q, P, final_exponentiate=False)` — BLS: R doubles/adds
    over FQ2 and is twisted per-iteration; plain binary schedule; no
    Frobenius tail.  The final exponentiation is applied by the
    callers (`pairing` below; `Kzg.pairing_check` batches it). -/
def miller_loop_raw (Q : Proj FQP) (P : Proj Nat) : FQP := Id.run do
  let F12 := fq12Ops
  let F2 := fq2Ops
  let castP := castToFq12 P
  let twistQ := twist Q
  let mut R := Q
  let mut twistR := twistQ
  let mut fNum := F12.one
  let mut fDen := F12.one
  for v in millerSchedule do
    let (n, d) := linefunc F12 twistR twistR castP
    fNum := F12.mul (F12.mul fNum fNum) n
    fDen := F12.mul (F12.mul fDen fDen) d
    R := pDouble F2 R
    twistR := twist R
    if v == 1 then
      let (n, d) := linefunc F12 twistR twistQ castP
      fNum := F12.mul fNum n
      fDen := F12.mul fDen d
      R := pAdd F2 R Q
      twistR := twist R
  pure (F12.mul fNum (F12.inv fDen))

/-- `final_exponentiate(f)`. -/
def final_exponentiate (f : FQP) : FQP :=
  fqpPow blsP 12 fq12MC f ((blsP^12 - 1) / blsOrder)

/-- `pairing(Q, P)` on validated points; infinities pair to one. -/
def pairing (Q : Proj FQP) (P : Proj Nat) : FQP :=
  if pIsInf fq2Ops Q || pIsInf fqOps P then fqpOne 12
  else final_exponentiate (miller_loop_raw Q P)

end Bls12

/-- Lift a decode-helper result into the machine monad. -/
private def liftE {α : Type} : Except EvmError α → EvmM α
  | .ok a => pure a
  | .error e => throw e

namespace GasCosts
def PRECOMPILE_BLS_G1ADD : Uint := 375
def PRECOMPILE_BLS_G1MUL : Uint := 12000
def PRECOMPILE_BLS_G2ADD : Uint := 600
def PRECOMPILE_BLS_G2MUL : Uint := 22500
end GasCosts

/-! ## The precompiles -/

/-- `bls12_g1_add(evm)`. -/
def pBls12G1Add : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length ≠ 256 then throw (.invalidParameter "Invalid Input Length")
  charge_gas GasCosts.PRECOMPILE_BLS_G1ADD
  let p1 ← liftE (Bls12.bytes_to_g1 (buffer_read data 0 128))
  let p2 ← liftE (Bls12.bytes_to_g1 (buffer_read data 128 128))
  let r := Bn128.pAdd Bls12.fqOps p1 p2
  EvmM.modifyEvm (fun e => { e with output := Bls12.g1_to_bytes r })

/-- `bls12_g1_msm(evm)`. -/
def pBls12G1Msm : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length == 0 || data.length % Bls12.LENGTH_PER_PAIR_G1 ≠ 0 then
    throw (.invalidParameter "Invalid Input Length")
  let k := data.length / Bls12.LENGTH_PER_PAIR_G1
  let discount := if k ≤ 128 then Bls12.G1_K_DISCOUNT.getD (k - 1) 0
    else Bls12.G1_MAX_DISCOUNT
  charge_gas (k * GasCosts.PRECOMPILE_BLS_G1MUL * discount / Bls12.MULTIPLIER)
  let mut result : Bn128.Proj Nat := (1, 1, 0)
  for i in [0:k] do
    let (pt, m) ← liftE (Bls12.decode_g1_scalar_pair
      ((data.drop (i * Bls12.LENGTH_PER_PAIR_G1)).take Bls12.LENGTH_PER_PAIR_G1))
    let product := Bn128.pMul Bls12.fqOps pt m
    result := if i == 0 then product else Bn128.pAdd Bls12.fqOps result product
  EvmM.modifyEvm (fun e => { e with output := Bls12.g1_to_bytes result })

/-- `bls12_g2_add(evm)`. -/
def pBls12G2Add : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length ≠ 512 then throw (.invalidParameter "Invalid Input Length")
  charge_gas GasCosts.PRECOMPILE_BLS_G2ADD
  let p1 ← liftE (Bls12.bytes_to_g2 (buffer_read data 0 256))
  let p2 ← liftE (Bls12.bytes_to_g2 (buffer_read data 256 256))
  let r := Bn128.pAdd Bls12.fq2Ops p1 p2
  EvmM.modifyEvm (fun e => { e with output := Bls12.g2_to_bytes r })

/-- `bls12_g2_msm(evm)`. -/
def pBls12G2Msm : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length == 0 || data.length % Bls12.LENGTH_PER_PAIR_G2 ≠ 0 then
    throw (.invalidParameter "Invalid Input Length")
  let k := data.length / Bls12.LENGTH_PER_PAIR_G2
  let discount := if k ≤ 128 then Bls12.G2_K_DISCOUNT.getD (k - 1) 0
    else Bls12.G2_MAX_DISCOUNT
  charge_gas (k * GasCosts.PRECOMPILE_BLS_G2MUL * discount / Bls12.MULTIPLIER)
  let F := Bls12.fq2Ops
  let mut result : Bn128.Proj Bn128.FQP := (F.one, F.one, F.zero)
  for i in [0:k] do
    let (pt, m) ← liftE (Bls12.decode_g2_scalar_pair
      ((data.drop (i * Bls12.LENGTH_PER_PAIR_G2)).take Bls12.LENGTH_PER_PAIR_G2))
    let product := Bn128.pMul F pt m
    result := if i == 0 then product else Bn128.pAdd F result product
  EvmM.modifyEvm (fun e => { e with output := Bls12.g2_to_bytes result })

/-- `bls12_pairing(evm)`. -/
def pBls12Pairing : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length == 0 || data.length % 384 ≠ 0 then
    throw (.invalidParameter "Invalid Input Length")
  let k := data.length / 384
  charge_gas (32600 * k + 37700)
  let F := Bls12.fq12Ops
  let mut result := F.one
  for i in [0:k] do
    let g1 ← liftE (Bls12.bytes_to_g1
      ((data.drop (384 * i)).take 128))
    if !Bn128.pIsInf Bls12.fqOps (Bn128.pMul Bls12.fqOps g1 Bls12.blsOrder) then
      throw (.invalidParameter "Subgroup check failed for G1 point.")
    let g2 ← liftE (Bls12.bytes_to_g2
      ((data.drop (384 * i + 128)).take 256))
    if !Bn128.pIsInf Bls12.fq2Ops (Bn128.pMul Bls12.fq2Ops g2 Bls12.blsOrder) then
      throw (.invalidParameter "Subgroup check failed for G2 point.")
    result := F.mul result (Bls12.pairing g2 g1)
  EvmM.modifyEvm (fun e =>
    { e with output := natToBytesBE 32 (if F.beq result F.one then 1 else 0) })

end EvmAsm.Stateless.SpecRef
