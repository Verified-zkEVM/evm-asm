/-
  EvmAsm.Stateless.SpecRef.Crypto

  Full-message hash functions for the stateless-guest reference port,
  built on the *concrete* ZisK accelerator permutations
  (`EvmAsm.Rv64.Accel.keccakF`, `EvmAsm.Rv64.Accel.sha256Compress`).

  The Python reference (`ethereum.crypto.hash.keccak256`,
  `hashlib.sha256`) is the ground truth; here we wrap the permutations
  with the standard sponge / Merkle–Damgård padding so the SpecRef port
  has an executable, kernel-reducible `keccak256`/`sha256` over arbitrary
  byte strings. No new cryptographic primitive is introduced — the round
  functions are reused verbatim, so the pinned KATs in
  `EvmAsm/Rv64/ZiskAccel.lean` (`keccakF_kat_empty`, `sha256Compress_kat_empty`)
  transitively pin these wrappers, and the `#guard`s at the bottom check the
  empty-string digests end-to-end.

  Bytes are `List (BitVec 8)`, matching `EvmAsm.EL.RLP.Byte`.
-/

import EvmAsm.Rv64.ZiskAccel
import EvmAsm.EL.RLP.Basic

namespace EvmAsm.Stateless.SpecRef

open EvmAsm.Rv64

/-- A byte, matching the repo-wide `EvmAsm.EL.RLP.Byte = BitVec 8`. -/
abbrev Byte := EvmAsm.EL.RLP.Byte

/-- A byte string. -/
abbrev Bytes := List Byte

/-! ## Little/big-endian byte helpers -/

/-- Interpret bytes as a little-endian natural number (first byte least
    significant). -/
def bytesLEtoNat : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesLEtoNat bs

/-- The low `width` bytes of `x`, little-endian (first byte least
    significant). -/
def natToBytesLE (width x : Nat) : Bytes :=
  (List.range width).map (fun i => BitVec.ofNat 8 (x >>> (8 * i)))

@[simp] theorem natToBytesLE_length (width x : Nat) :
    (natToBytesLE width x).length = width := by
  simp [natToBytesLE]

/-- The low `width` bytes of `x`, big-endian (first byte most
    significant). Fixed-width companion to the minimal
    `EvmAsm.EL.RLP.Nat.toBytesBE`. -/
def natToBytesBE (width x : Nat) : Bytes :=
  (List.range width).reverse.map (fun i => BitVec.ofNat 8 (x >>> (8 * i)))

/-- Big-endian bytes → natural number (reuses the RLP model's converter). -/
abbrev bytesBEtoNat : Bytes → Nat := EvmAsm.EL.RLP.Nat.fromBytesBE

/-- Split a byte list into chunks of `n` bytes (last chunk full only when
    the length is a multiple of `n`, which is always the case for padded
    hash inputs). Fuel = input length guarantees termination. -/
def chunkBytesAux : Nat → Nat → Bytes → List Bytes
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, n, bs => bs.take n :: chunkBytesAux fuel n (bs.drop n)

/-- Split `bs` into `n`-byte chunks. -/
def chunkBytes (n : Nat) (bs : Bytes) : List Bytes :=
  chunkBytesAux (bs.length + 1) n bs

/-! ## Keccak-256 (sponge over `Accel.keccakF`) -/

/-- Keccak-256 rate in bytes (1088-bit rate, 512-bit capacity). -/
def keccakRateBytes : Nat := 136

/-- `pad10*1` with the Keccak domain byte `0x01`: append `0x01`, then
    zeros, then set the top bit of the final rate byte (`0x80`). When only
    one pad byte fits, the two collapse to `0x81`. -/
def keccakPad (msg : Bytes) : Bytes :=
  let padLen := keccakRateBytes - (msg.length % keccakRateBytes)
  let pad :=
    if padLen = 1 then [(0x81 : Byte)]
    else (0x01 : Byte) :: List.replicate (padLen - 2) (0 : Byte) ++ [(0x80 : Byte)]
  msg ++ pad

/-- XOR a 136-byte rate block (as 17 little-endian u64 lanes) into the
    25-lane state. -/
def keccakAbsorbBlock (st : List (BitVec 64)) (block : Bytes) : List (BitVec 64) :=
  let lanes : List (BitVec 64) :=
    (List.range 17).map (fun i =>
      BitVec.ofNat 64 (bytesLEtoNat ((block.drop (8 * i)).take 8)))
  let laneVec := lanes ++ List.replicate (25 - lanes.length) (0 : BitVec 64)
  List.zipWith (· ^^^ ·) st laneVec

/-- Absorb all rate blocks, permuting after each. -/
def keccakAbsorb : List (BitVec 64) → List Bytes → List (BitVec 64)
  | st, [] => st
  | st, block :: rest => keccakAbsorb (Accel.keccakF (keccakAbsorbBlock st block)) rest

/-- `keccak256(msg)` — the 32-byte digest (first four state lanes, each
    little-endian). Mirrors `ethereum.crypto.hash.keccak256`. -/
def keccak256 (msg : Bytes) : Bytes :=
  let st0 : List (BitVec 64) := List.replicate 25 (0 : BitVec 64)
  let st := keccakAbsorb st0 (chunkBytes keccakRateBytes (keccakPad msg))
  (st.take 4).flatMap (fun lane => natToBytesLE 8 lane.toNat)

/-- Absorption preserves the 25-lane state shape. -/
theorem keccakAbsorb_length (blocks : List Bytes) (st : List (BitVec 64))
    (hst : st.length = 25) : (keccakAbsorb st blocks).length = 25 := by
  induction blocks generalizing st with
  | nil => exact hst
  | cons b rest ih => exact ih _ (Accel.keccakF_length _)

/-- The digest is always exactly 32 bytes — four 8-byte LE lanes. -/
theorem keccak256_length (msg : Bytes) : (keccak256 msg).length = 32 := by
  unfold keccak256
  have hst : (keccakAbsorb (List.replicate 25 (0 : BitVec 64))
      (chunkBytes keccakRateBytes (keccakPad msg))).length = 25 :=
    keccakAbsorb_length _ _ (by simp)
  rw [List.length_flatMap]
  rw [List.map_congr_left (fun lane _ => natToBytesLE_length 8 lane.toNat)]
  have hrep : ∀ (l : List (BitVec 64)), (l.map (fun _ => (8 : Nat))).sum = 8 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a rest ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons]
      omega
  rw [hrep, List.length_take, hst]
  rfl

/-! ## SHA-256 (Merkle–Damgård over `Accel.sha256Compress`) -/

/-- The SHA-256 initial hash value (eight 32-bit words). -/
def sha256IV : List (BitVec 32) :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- SHA-256 padding: append `0x80`, zero-pad, then the 64-bit big-endian
    bit length, filling to a multiple of 64 bytes. -/
def sha256Pad (msg : Bytes) : Bytes :=
  let l := msg.length
  let zeros := (64 - ((l + 9) % 64)) % 64
  msg ++ [(0x80 : Byte)] ++ List.replicate zeros (0 : Byte)
      ++ natToBytesBE 8 (l * 8)

/-- Interpret a 64-byte block as sixteen 32-bit big-endian words. -/
def sha256BlockWords (block : Bytes) : List (BitVec 32) :=
  (List.range 16).map (fun i =>
    BitVec.ofNat 32 (bytesBEtoNat ((block.drop (4 * i)).take 4)))

/-- Fold the compression function over all 64-byte blocks. -/
def sha256Compress' : List (BitVec 32) → List Bytes → List (BitVec 32)
  | hs, [] => hs
  | hs, block :: rest =>
      sha256Compress' (Accel.sha256Compress hs (sha256BlockWords block)) rest

/-- `sha256(msg)` — the 32-byte digest. Mirrors `hashlib.sha256`. -/
def sha256 (msg : Bytes) : Bytes :=
  let hs := sha256Compress' sha256IV (chunkBytes 64 (sha256Pad msg))
  hs.flatMap (fun w => natToBytesBE 4 w.toNat)

/-- `sha256(a ‖ b)` — the SSZ pair hash used in merkleization. -/
def sha256Pair (a b : Bytes) : Bytes := sha256 (a ++ b)

/-! ## End-to-end known-answer checks -/

-- keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard bytesBEtoNat (keccak256 [])
  = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

-- sha256("") = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
#guard bytesBEtoNat (sha256 [])
  = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

-- sha256("abc") = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
#guard bytesBEtoNat (sha256 [0x61, 0x62, 0x63])
  = 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

-- keccak256("abc") = 4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
#guard bytesBEtoNat (keccak256 [0x61, 0x62, 0x63])
  = 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

end EvmAsm.Stateless.SpecRef
