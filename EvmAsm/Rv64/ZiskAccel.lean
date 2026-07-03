/-
  EvmAsm.Rv64.ZiskAccel

  Concrete semantics of the ZisK accelerator instructions
  (bead evm-asm-4ch8f.1).

  The guest invokes ZisK precompiles via raw `csrs <id>, <reg>` encodings
  (`.4byte` words, e.g. `0x80052073 = csrs 0x800, a0`); the register holds
  a pointer to the operand block.  This module gives those instructions
  *concrete* mathematical semantics — the actual Keccak-f[1600]
  permutation, the actual SHA-256 compression function, exact
  512-bit-intermediate modular arithmetic — rather than an axiomatized
  accelerator contract:

  * evm-asm carries SOFTWARE implementations of several hashes (RIPEMD-160,
    the SHA-256 Merkle–Damgård wrapper, P-256 over Arith256Mod); proofs
    must relate the software and accelerator paths to the SAME function,
    so the function has to exist concretely;
  * the project's trusted base is the three classical axioms — an
    axiomatized accelerator contract would widen it;
  * concrete permutations are testable in-repo: the known-answer theorems
    below are kernel-checked with `decide` against pinned vectors
    (`keccak256("")`, `sha256("")`).

  Modeled accelerators (CSR ids per `ziskos` and the pinned probes in
  `Codegen/Programs/HashProbes.lean` / `Secp256k1Field.lean`):

    0x800  Keccakf      rs1 → 200-byte state, 25 LE u64 lanes, in place
    0x802  Arith256Mod  rs1 → [a*, b*, c*, module*, d*], 4 LE u64 limbs
                        each; d := (a*b + c) mod module (exact 512-bit
                        intermediate; module = 0 traps)
    0x805  Sha256f      rs1 → [state*, input*]; state = 8 u32 (LE-u32
                        packed in u64), input = 16 u32; one compression,
                        in place
    0x80B  Arith384Mod  rs1 → [a*, b*, c*, module*, d*], 6 LE u64 limbs
                        each; d := (a*b + c) mod module (module = 0 traps)
    0x819  Blake2bRound rs1 → [sigmaIdx, state*, input*]; one BLAKE2b
                        round on the 16-word working vector with SIGMA
                        row `sigmaIdx` (must be < 10), in place

  Any other CSR id traps (`step` returns `none`): unmodeled accelerators
  halt the model rather than silently no-op.  Follow-up accelerators
  (Secp256k1Add/Dbl 0x803/0x804, BN254 0x806–0x80A, BLS12-381
  0x80C–0x810) slot into the same `execCsrs`/`csrsValid` dispatch.
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Rv64

namespace Accel

-- ============================================================================
-- Keccak-f[1600]
-- ============================================================================

/-- The 24 Keccak round constants. -/
def keccakRC : List (BitVec 64) :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
   0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
   0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
   0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
   0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
   0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
   0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
   0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rho rotation offsets, indexed `rhoOff x y` for lane (x, y). -/
def rhoOff (x y : Nat) : Nat :=
  ([[0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14]].getD (x % 5) []).getD (y % 5) 0

/-- One Keccak-f round on the 5×5 lane state (lane (x, y) at index
    `x + 5*y`).  The result is MATERIALIZED as a list: composing rounds
    over a functional state would re-evaluate shared lanes exponentially. -/
def keccakRound (rc : BitVec 64) (st : List (BitVec 64)) : List (BitVec 64) :=
  let A : Nat → Nat → BitVec 64 := fun x y => st.getD (x % 5 + 5 * (y % 5)) 0
  let C : Nat → BitVec 64 := fun x => A x 0 ^^^ A x 1 ^^^ A x 2 ^^^ A x 3 ^^^ A x 4
  let D : Nat → BitVec 64 := fun x => C (x + 4) ^^^ (C (x + 1)).rotateLeft 1
  -- theta, then rho+pi: B[X + 5Y] sources lane (X + 3Y, X)
  let B : Nat → Nat → BitVec 64 := fun X Y =>
    let xs := (X + 3 * Y) % 5
    let ys := X % 5
    (A xs ys ^^^ D xs).rotateLeft (rhoOff xs ys)
  let chi : Nat → BitVec 64 := fun j =>
    let X := j % 5
    let Y := j / 5
    B X Y ^^^ ((~~~(B (X + 1) Y)) &&& B (X + 2) Y)
  List.ofFn (n := 25) (fun j => if j.val = 0 then chi 0 ^^^ rc else chi j.val)

/-- Keccak-f[1600]: 24 rounds over the 25-lane state. -/
def keccakF (st : List (BitVec 64)) : List (BitVec 64) :=
  keccakRC.foldl (fun s rc => keccakRound rc s) st

set_option maxRecDepth 40000 in
/-- Known-answer test, kernel-checked: absorbing the padded empty message
    into a zero state (rate 1088: `st[0] ^= 0x01`, `st[16] ^= 0x80 << 56`)
    and permuting yields `keccak256("") =
    c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`
    in the first four LE lanes.

    The `maxRecDepth` bump is NOT proof-search scaling: `decide` here is
    concrete evaluation, and the recursion depth is the intrinsic
    evaluation depth of 24 chained rounds (each round's lanes read the
    previous round's materialized list), not a symptom of a mis-stated
    goal. -/
theorem keccakF_kat_empty :
    (keccakF (List.ofFn (n := 25) (fun j =>
      if j.val = 0 then 0x0000000000000001
      else if j.val = 16 then 0x8000000000000000
      else 0))).take 4
    = [0x3C23F7860146D2C5, 0xC003C7DCB27D7E92,
       0x3B2782CA53B600E5, 0x70A4855D04D8FA7B] := by decide

-- ============================================================================
-- SHA-256 compression
-- ============================================================================

/-- The 64 SHA-256 round constants. -/
def sha256K : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
   0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
   0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
   0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
   0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
   0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
   0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
   0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Message schedule: extend the 16 block words to 64. -/
def sha256W (w : List (BitVec 32)) : List (BitVec 32) :=
  (List.range 64).foldl (fun acc t =>
    if t < 16 then acc ++ [w.getD t 0]
    else
      let s0 := (acc.getD (t - 15) 0).rotateRight 7
        ^^^ (acc.getD (t - 15) 0).rotateRight 18 ^^^ (acc.getD (t - 15) 0 >>> 3)
      let s1 := (acc.getD (t - 2) 0).rotateRight 17
        ^^^ (acc.getD (t - 2) 0).rotateRight 19 ^^^ (acc.getD (t - 2) 0 >>> 10)
      acc ++ [acc.getD (t - 16) 0 + s0 + acc.getD (t - 7) 0 + s1]) []

/-- One SHA-256 compression: 8-word state, 16-word block, new 8-word
    state (Davies–Meyer feed-forward included). -/
def sha256Compress (hs w : List (BitVec 32)) : List (BitVec 32) :=
  let W := sha256W w
  let fin := (List.range 64).foldl (fun st t =>
    let a := st.getD 0 0
    let b := st.getD 1 0
    let c := st.getD 2 0
    let d := st.getD 3 0
    let e := st.getD 4 0
    let f := st.getD 5 0
    let g := st.getD 6 0
    let h := st.getD 7 0
    let S1 := e.rotateRight 6 ^^^ e.rotateRight 11 ^^^ e.rotateRight 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let T1 := h + S1 + ch + sha256K.getD t 0 + W.getD t 0
    let S0 := a.rotateRight 2 ^^^ a.rotateRight 13 ^^^ a.rotateRight 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let T2 := S0 + maj
    [T1 + T2, a, b, c, d + T1, e, f, g]) (hs.take 8)
  List.zipWith (· + ·) (hs.take 8) fin

set_option maxRecDepth 40000 in
/-- Known-answer test, kernel-checked: compressing the padded empty
    message over the initial state yields `sha256("") =
    e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
    (Same intrinsic-evaluation-depth note as `keccakF_kat_empty`.) -/
theorem sha256Compress_kat_empty :
    sha256Compress
      [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
       0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
      [0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    = [0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
       0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855] := by decide

-- ============================================================================
-- Arith256Mod
-- ============================================================================

/-- Interpret a little-endian u64 limb list as a natural number. -/
def leLimbsToNat (ws : List Word) : Nat :=
  ws.foldr (fun w acc => acc * 2 ^ 64 + w.toNat) 0

/-- The low `n` little-endian u64 limbs of a natural number. -/
def natToLeLimbs (n : Nat) (x : Nat) : List Word :=
  (List.range n).map (fun i => BitVec.ofNat 64 (x >>> (64 * i)))

/-- `d = (a*b + c) mod m` with exact intermediate arithmetic (the ZisK
    `Arith256Mod` contract).  Callers guard `m ≠ 0` (`csrsValid`). -/
def arith256Mod (a b c m : Nat) : Nat :=
  (a * b + c) % m

-- ============================================================================
-- BLAKE2b round (RFC 7693)
-- ============================================================================

/-- The BLAKE2b message-schedule permutations (SIGMA), rows 0–9. -/
def blake2Sigma : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
   [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
   [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
   [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
   [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
   [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
   [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
   [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
   [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- The BLAKE2b G mixing function on working-vector indices
    `a b c d` with message words `x y`. -/
def blakeG (v : List (BitVec 64)) (a b c d : Nat) (x y : BitVec 64) :
    List (BitVec 64) :=
  let va := v.getD a 0 + v.getD b 0 + x
  let vd := (v.getD d 0 ^^^ va).rotateRight 32
  let vc := v.getD c 0 + vd
  let vb := (v.getD b 0 ^^^ vc).rotateRight 24
  let va' := va + vb + y
  let vd' := (vd ^^^ va').rotateRight 16
  let vc' := vc + vd'
  let vb' := (vb ^^^ vc').rotateRight 63
  (((v.set a va').set b vb').set c vc').set d vd'

/-- One BLAKE2b round (RFC 7693 §3.2): four column and four diagonal G
    mixes of the 16-word working vector `v` with message words `m`,
    using SIGMA row `idx % 10`.  Exactly the ZisK `Blake2bRound`
    accelerator body (`precompiles/helpers/src/blake2/blake2b/round.rs`);
    the software F loop iterates it `rounds` times. -/
def blake2bRound (idx : Nat) (v m : List (BitVec 64)) : List (BitVec 64) :=
  let s := blake2Sigma.getD (idx % 10) []
  let mi : Nat → BitVec 64 := fun i => m.getD (s.getD i 0) 0
  let v1 := blakeG v 0 4 8 12 (mi 0) (mi 1)
  let v2 := blakeG v1 1 5 9 13 (mi 2) (mi 3)
  let v3 := blakeG v2 2 6 10 14 (mi 4) (mi 5)
  let v4 := blakeG v3 3 7 11 15 (mi 6) (mi 7)
  let v5 := blakeG v4 0 5 10 15 (mi 8) (mi 9)
  let v6 := blakeG v5 1 6 11 12 (mi 10) (mi 11)
  let v7 := blakeG v6 2 7 8 13 (mi 12) (mi 13)
  blakeG v7 3 4 9 14 (mi 14) (mi 15)

set_option maxRecDepth 4000 in
/-- Known-answer test, kernel-checked: the first round of the
    BLAKE2b-512("abc") compression (initial working vector from
    `h₀ = IV₀ ^ 0x01010040`, `t₀ = 3`, final-block flag; message block
    "abc" zero-padded), SIGMA row 0.  Expected vector generated by an
    independent Python implementation validated against
    `hashlib.blake2b` over the full 12 rounds. -/
theorem blake2bRound_kat_abc :
    blake2bRound 0
      [0x6a09e667f2bdc948, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
       0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
       0x1f83d9abfb41bd6b, 0x5be0cd19137e2179, 0x6a09e667f3bcc908,
       0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
       0x510e527fade682d2, 0x9b05688c2b3e6c1f, 0xe07c265404be4294,
       0x5be0cd19137e2179]
      [0x636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    = [0x86b7c1568029bb79, 0xc12cbcc809ff59f3, 0xc6a5214cc0eaca8e,
       0x0c87cd524c14cc5d, 0x44ee6039bd86a9f7, 0xa447c850aa694a7e,
       0xde080f1bb1c0f84b, 0x595cb8a9a1aca66c, 0xbec3ae837eac4887,
       0x6267fc79df9d6ad1, 0xfa87b01273fa6dbe, 0x521a715c63e08d8a,
       0xe02d0975b8d37a83, 0x1c7b754f08b7d193, 0x8f885a76b6e578fe,
       0x2318a24e2140fc64] := by decide

-- ============================================================================
-- u32-in-dword packing (the pinned ziskemu 0.18 Sha256f layout)
-- ============================================================================

/-- Unpack dwords into u32s, low half first (LE-u32-within-u64). -/
def dwordsToU32s (ws : List Word) : List (BitVec 32) :=
  ws.flatMap (fun (w : Word) => [w.setWidth 32, (w >>> 32).setWidth 32])

/-- Pack u32 pairs back into dwords, low half first. -/
def u32sToDwords : List (BitVec 32) → List Word
  | lo :: hi :: rest =>
      ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: u32sToDwords rest
  | _ => []

/-- The SHA-256 state words are big-endian u32s stored as LE u32s in
    memory; as u32 VALUES read from the dwords they are already the
    spec-side words, so the pinned layout round-trips through
    `dwordsToU32s`/`u32sToDwords` with no byte swap. -/
theorem u32sToDwords_dwordsToU32s_pair (w : Word) :
    u32sToDwords (dwordsToU32s [w]) = [w] := by
  show [(((w >>> 32).setWidth 32).setWidth 64 <<< 32)
    ||| (w.setWidth 32).setWidth 64] = [w]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases h32 : i < 32
  · simp [BitVec.getLsbD_setWidth, h32, hi]
  · simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h32, hi,
      show i - 32 < 32 from by omega, show 32 + (i - 32) = i from by omega]
    intro _
    omega

end Accel

-- ============================================================================
-- Machine-level accelerator dispatch
-- ============================================================================

namespace MachineState

/-- Every dword of an `n`-dword operand block is a valid access. -/
def validDwordRange (p : Word) (n : Nat) : Bool :=
  (List.range n).all (fun i => isValidDwordAccess (p + BitVec.ofNat 64 (8 * i)))

/-- Effect of `csrs csr, rs1` on the machine state (validity is checked
    separately by `csrsValid`; `step` traps when it fails).  Unknown CSR
    ids leave the state unchanged here and trap in `step`. -/
def execCsrs (s : MachineState) (csr : BitVec 12) (rs1 : Reg) : MachineState :=
  let p := s.getReg rs1
  if csr = 0x800 then
    -- Keccakf: 25-lane state at p, in place
    s.writeWords p (Accel.keccakF (s.readWords p 25))
  else if csr = 0x802 then
    -- Arith256Mod: parameter block [a*, b*, c*, module*, d*] at p
    let a := Accel.leLimbsToNat (s.readWords (s.getMem p) 4)
    let b := Accel.leLimbsToNat (s.readWords (s.getMem (p + 8)) 4)
    let c := Accel.leLimbsToNat (s.readWords (s.getMem (p + 16)) 4)
    let m := Accel.leLimbsToNat (s.readWords (s.getMem (p + 24)) 4)
    s.writeWords (s.getMem (p + 32)) (Accel.natToLeLimbs 4 (Accel.arith256Mod a b c m))
  else if csr = 0x805 then
    -- Sha256f: parameter block [state*, input*] at p
    let stP := s.getMem p
    let st := Accel.dwordsToU32s (s.readWords stP 4)
    let blk := Accel.dwordsToU32s (s.readWords (s.getMem (p + 8)) 8)
    s.writeWords stP (Accel.u32sToDwords (Accel.sha256Compress st blk))
  else if csr = 0x80B then
    -- Arith384Mod: parameter block [a*, b*, c*, module*, d*] at p,
    -- 6 LE u64 limbs each (the 384-bit sibling of Arith256Mod)
    let a := Accel.leLimbsToNat (s.readWords (s.getMem p) 6)
    let b := Accel.leLimbsToNat (s.readWords (s.getMem (p + 8)) 6)
    let c := Accel.leLimbsToNat (s.readWords (s.getMem (p + 16)) 6)
    let m := Accel.leLimbsToNat (s.readWords (s.getMem (p + 24)) 6)
    s.writeWords (s.getMem (p + 32)) (Accel.natToLeLimbs 6 (Accel.arith256Mod a b c m))
  else if csr = 0x819 then
    -- Blake2bRound: parameter block [sigmaIdx, state*, input*] at p;
    -- one round on the 16-word working vector, in place
    let idx := (s.getMem p).toNat
    let vP := s.getMem (p + 8)
    s.writeWords vP
      (Accel.blake2bRound idx (s.readWords vP 16)
        (s.readWords (s.getMem (p + 16)) 16))
  else
    s

/-- Validity of a `csrs csr, rs1` accelerator call: every operand dword
    (parameter blocks and the blocks they point to) is a valid dword
    access, and `Arith256Mod`'s modulus is nonzero.  `false` for CSR ids
    the model does not cover — `step` TRAPS on those rather than
    no-opping, so unmodeled accelerators cannot be silently skipped. -/
def csrsValid (s : MachineState) (csr : BitVec 12) (rs1 : Reg) : Bool :=
  let p := s.getReg rs1
  if csr = 0x800 then
    validDwordRange p 25
  else if csr = 0x802 then
    validDwordRange p 5 &&
    validDwordRange (s.getMem p) 4 &&
    validDwordRange (s.getMem (p + 8)) 4 &&
    validDwordRange (s.getMem (p + 16)) 4 &&
    validDwordRange (s.getMem (p + 24)) 4 &&
    validDwordRange (s.getMem (p + 32)) 4 &&
    !(Accel.leLimbsToNat (s.readWords (s.getMem (p + 24)) 4) == 0)
  else if csr = 0x805 then
    validDwordRange p 2 &&
    validDwordRange (s.getMem p) 4 &&
    validDwordRange (s.getMem (p + 8)) 8
  else if csr = 0x80B then
    validDwordRange p 5 &&
    validDwordRange (s.getMem p) 6 &&
    validDwordRange (s.getMem (p + 8)) 6 &&
    validDwordRange (s.getMem (p + 16)) 6 &&
    validDwordRange (s.getMem (p + 24)) 6 &&
    validDwordRange (s.getMem (p + 32)) 6 &&
    !(Accel.leLimbsToNat (s.readWords (s.getMem (p + 24)) 6) == 0)
  else if csr = 0x819 then
    validDwordRange p 3 &&
    validDwordRange (s.getMem (p + 8)) 16 &&
    validDwordRange (s.getMem (p + 16)) 16 &&
    decide ((s.getMem p).toNat < 10)
  else
    false

/-- Every `execCsrs` branch is either a `writeWords` or the identity, so
    any field `writeWords` preserves is preserved (branch-count-agnostic:
    new accelerators need no proof edits). -/
local macro "csrs_proj" : tactic =>
  `(tactic| (unfold execCsrs
             repeat first
               | rfl
               | (split
                  · simp)))

@[simp] theorem pc_execCsrs (s : MachineState) (csr : BitVec 12) (rs1 : Reg) :
    (s.execCsrs csr rs1).pc = s.pc := by csrs_proj

@[simp] theorem committed_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).committed = s.committed := by csrs_proj

@[simp] theorem publicValues_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).publicValues = s.publicValues := by
  csrs_proj

@[simp] theorem privateInput_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).privateInput = s.privateInput := by
  csrs_proj

@[simp] theorem inputBufBase_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).inputBufBase = s.inputBufBase := by
  csrs_proj

@[simp] theorem code_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).code = s.code := by csrs_proj

@[simp] theorem getReg_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) (r : Reg) : (s.execCsrs csr rs1).getReg r = s.getReg r := by
  csrs_proj

end MachineState

end EvmAsm.Rv64
