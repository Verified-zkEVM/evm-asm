/-
  EvmAsm.Stateless.SpecRef.PrecompilesHash

  The two hash precompiles of
  `execution-specs/src/ethereum/forks/amsterdam/vm/precompiled_contracts/`
  (`@tests-zkevm@v0.5.0`, `bd8c673`) that need fresh primitive ports
  (Python delegates them to `hashlib` / `ethereum/crypto/blake2.py`):

  * `ripemd160.py` — function `ripemd160`; the RIPEMD-160 primitive is
    implemented here from the algorithm specification (ISO/IEC
    10118-3; Python uses `hashlib.new("ripemd160")`), `#guard`-pinned
    to the standard test vectors.
  * `blake2f.py` — function `blake2f`; the `Blake2b` compression
    (`ethereum/crypto/blake2.py`, class `Blake2` / `Blake2b`,
    `execution-specs/src/ethereum/crypto/blake2.py`) ported directly,
    `#guard`-pinned to the RFC 7693 appendix-A example.
-/

import EvmAsm.Stateless.SpecRef.Precompiles

namespace EvmAsm.Stateless.SpecRef

namespace GasCosts
def PRECOMPILE_RIPEMD160_BASE : Uint := 600
def PRECOMPILE_RIPEMD160_PER_WORD : Uint := 120
def PRECOMPILE_BLAKE2F_PER_ROUND : Uint := 1
end GasCosts

/-! ## RIPEMD-160 primitive -/

namespace Ripemd160

private def M32 : Nat := 2^32

private def rotl (s : Nat) (x : Nat) : Nat :=
  ((x <<< s) ||| (x >>> (32 - s))) % M32

/-- Selection functions f₁…f₅ (per 16-step block `j/16`). -/
private def f (j : Nat) (x y z : Nat) : Nat :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((M32 - 1 - x) &&& z)
  else if j < 48 then (x ||| (M32 - 1 - y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (M32 - 1 - z))
  else x ^^^ (y ||| (M32 - 1 - z))

private def K : List Nat := [0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
private def K' : List Nat := [0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

private def r : List Nat :=
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
   7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
   3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,
   1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
   4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13]

private def r' : List Nat :=
  [5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,
   6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
   15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,
   8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
   12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11]

private def s : List Nat :=
  [11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,
   7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
   11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,
   11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,
   9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6]

private def s' : List Nat :=
  [8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,
   9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
   9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,
   15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
   8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11]

/-- One 512-bit block: 80 steps of the left and right lines, then the
    chaining combination. -/
private def compressBlock (h : List Nat) (X : List Nat) : List Nat := Id.run do
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut a' := a
  let mut b' := b
  let mut c' := c
  let mut d' := d
  let mut e' := e
  for j in [0:80] do
    -- left line
    let t := rotl (s.getD j 0)
      ((a + f j b c d + X.getD (r.getD j 0) 0 + K.getD (j / 16) 0) % M32)
    let t := (t + e) % M32
    a := e; e := d; d := rotl 10 c; c := b; b := t
    -- right line (f with reversed block order)
    let t' := rotl (s'.getD j 0)
      ((a' + f (79 - j) b' c' d' + X.getD (r'.getD j 0) 0 + K'.getD (j / 16) 0) % M32)
    let t' := (t' + e') % M32
    a' := e'; e' := d'; d' := rotl 10 c'; c' := b'; b' := t'
  let h0 := h.getD 0 0
  let h1 := h.getD 1 0
  let h2 := h.getD 2 0
  let h3 := h.getD 3 0
  let h4 := h.getD 4 0
  pure [(h1 + c + d') % M32, (h2 + d + e') % M32, (h3 + e + a') % M32,
        (h4 + a + b') % M32, (h0 + b + c') % M32]

private def leWord (bs : Bytes) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

private def wordLE (n : Nat) : Bytes :=
  (List.range 4).map (fun i => BitVec.ofNat 8 (n >>> (8 * i)))

private def chunksAux (n : Nat) : Nat → Bytes → List Bytes
  | 0, _ => []
  | _, [] => []
  | fuel + 1, bs => bs.take n :: chunksAux n fuel (bs.drop n)

/-- Split into `n`-byte chunks.  Structurally fueled by `bs.length`,
    which bounds the chunk count whenever `n ≥ 1` (each chunk consumes
    at least one byte). -/
private def chunks (n : Nat) (bs : Bytes) : List Bytes :=
  if n == 0 then [] else chunksAux n bs.length bs

/-- RIPEMD-160 of a byte string (MD-style padding, little-endian
    length). -/
def hash (data : Bytes) : Bytes :=
  let bitLen := data.length * 8
  let padLen := (119 - data.length % 64) % 64 + 1  -- to ≡ 56 mod 64
  let padded := data ++ [(0x80 : BitVec 8)]
    ++ List.replicate (padLen - 1) (0x00 : BitVec 8)
    ++ (List.range 8).map (fun i => BitVec.ofNat 8 (bitLen >>> (8 * i)))
  let blocks := chunks 64 padded
  let h0 := [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  let hFinal := blocks.foldl (fun h block =>
    compressBlock h ((chunks 4 block).map leWord)) h0
  hFinal.flatMap wordLE

end Ripemd160

/-- `ripemd160(evm)` (`ripemd160.py`, function `ripemd160`): 32-byte
    left-padded 20-byte digest. -/
def pRipemd160 : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  let word_count := ceil32 data.length / 32
  charge_gas (GasCosts.PRECOMPILE_RIPEMD160_BASE
    + GasCosts.PRECOMPILE_RIPEMD160_PER_WORD * word_count)
  let digest := Ripemd160.hash data
  EvmM.modifyEvm (fun e => { e with output := List.replicate 12 0x00 ++ digest })

/-! ## BLAKE2b compression (`ethereum/crypto/blake2.py`, class `Blake2b`) -/

namespace Blake2b

private def M64 : Nat := 2^64

private def IV : List Nat :=
  [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B,
   0xA54FF53A5F1D36F1, 0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
   0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

private def sigma : List (List Nat) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
   [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
   [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
   [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
   [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
   [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
   [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
   [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
   [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
   [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

private def mixTable : List (Nat × Nat × Nat × Nat) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
   (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

private def rotr (n : Nat) (x : Nat) : Nat :=
  ((x >>> n) ||| (x <<< (64 - n))) % M64

/-- The `G` mixing function (rotations 32/24/16/63). -/
private def G (v : List Nat) (a b c d : Nat) (x y : Nat) : List Nat := Id.run do
  let mut v := v
  v := v.set a ((v.getD a 0 + v.getD b 0 + x) % M64)
  v := v.set d (rotr 32 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 24 (v.getD b 0 ^^^ v.getD c 0))
  v := v.set a ((v.getD a 0 + v.getD b 0 + y) % M64)
  v := v.set d (rotr 16 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 63 (v.getD b 0 ^^^ v.getD c 0))
  pure v

/-- `compress(num_rounds, h, m, t_0, t_1, f)` — 'F Compression' of
    RFC 7693 §3.2. -/
def compress (num_rounds : Nat) (h m : List Nat) (t0 t1 : Nat) (f : Bool) :
    Bytes := Id.run do
  let mut v := h ++ IV
  v := v.set 12 ((v.getD 12 0) ^^^ t0)
  v := v.set 13 ((v.getD 13 0) ^^^ t1)
  if f then
    v := v.set 14 ((v.getD 14 0) ^^^ (M64 - 1))
  for rnd in [0:num_rounds] do
    let sch := sigma.getD (rnd % 10) []
    let mut i := 0
    for (a, b, c, d) in mixTable do
      v := G v a b c d (m.getD (sch.getD (2*i) 0) 0) (m.getD (sch.getD (2*i+1) 0) 0)
      i := i + 1
  let out := (List.range 8).map (fun i => (h.getD i 0) ^^^ (v.getD i 0) ^^^ (v.getD (i+8) 0))
  pure (out.flatMap (fun w => (List.range 8).map (fun i => BitVec.ofNat 8 (w >>> (8*i)))))

/-- `spit_le_to_uint(data, start, num_words)`: 64-bit LE words. -/
def leWords (data : Bytes) (start count : Nat) : List Nat :=
  (List.range count).map (fun i =>
    ((data.drop (start + 8*i)).take 8).foldr (fun b acc => acc * 256 + b.toNat) 0)

end Blake2b

/-- `blake2f(evm)` (`blake2f.py`, function `blake2f`). -/
def pBlake2f : EvmM Unit := do
  let data := (← EvmM.getEvm).message.data
  if data.length ≠ 213 then throw (.invalidParameter "blake2f input length")
  let rounds := bytesBEtoNat (data.take 4)
  let h := Blake2b.leWords data 4 8
  let m := Blake2b.leWords data 68 16
  let t0 := (Blake2b.leWords data 196 1).getD 0 0
  let t1 := (Blake2b.leWords data 204 1).getD 0 0
  let f := bytesBEtoNat (data.drop 212)
  charge_gas (GasCosts.PRECOMPILE_BLAKE2F_PER_ROUND * rounds)
  if f ≠ 0 && f ≠ 1 then throw (.invalidParameter "blake2f final flag")
  EvmM.modifyEvm (fun e =>
    { e with output := Blake2b.compress rounds h m t0 t1 (f == 1) })

/-! ## Sanity checks -/

-- RIPEMD-160 standard vectors: "" and "abc".
#guard bytesBEtoNat (Ripemd160.hash [])
  == 0x9c1185a5c5e9fc54612808977ee8f548b2258d31
#guard bytesBEtoNat (Ripemd160.hash [0x61, 0x62, 0x63])
  == 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc

-- BLAKE2b: RFC 7693 Appendix A — BLAKE2b-512("abc").  h₀ = IV with the
-- parameter-block word (digest length 64, fanout/depth 1) XORed into
-- h[0]; one final block containing "abc", t₀ = 3.
#guard
  let h0 := Blake2b.IV.set 0 ((Blake2b.IV.getD 0 0) ^^^ 0x01010040)
  let m := (List.replicate 16 0).set 0 0x636261
  bytesBEtoNat (Blake2b.compress 12 h0 m 3 0 true)
  == 0xba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923

end EvmAsm.Stateless.SpecRef
