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

  Any other CSR id traps (`step` returns `none`): unmodeled accelerators
  halt the model rather than silently no-op.  Follow-up accelerators
  (Secp256k1Add/Dbl 0x803/0x804, Blake2bRound 0x819, BN254, BLS12-381)
  slot into the same `execCsrs`/`csrsValid` dispatch.
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
  else
    false

@[simp] theorem pc_execCsrs (s : MachineState) (csr : BitVec 12) (rs1 : Reg) :
    (s.execCsrs csr rs1).pc = s.pc := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

@[simp] theorem committed_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).committed = s.committed := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

@[simp] theorem publicValues_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).publicValues = s.publicValues := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

@[simp] theorem privateInput_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).privateInput = s.privateInput := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

@[simp] theorem inputBufBase_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).inputBufBase = s.inputBufBase := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

@[simp] theorem code_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) : (s.execCsrs csr rs1).code = s.code := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

@[simp] theorem getReg_execCsrs (s : MachineState) (csr : BitVec 12)
    (rs1 : Reg) (r : Reg) : (s.execCsrs csr rs1).getReg r = s.getReg r := by
  unfold execCsrs
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rfl

end MachineState

end EvmAsm.Rv64
