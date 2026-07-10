/-
  EvmAsm.Codegen.Programs.Secp256k1FieldLeToBeSAsm

  Verified SAsm port of the secp256k1 LE→BE field-element converter
  (bead evm-asm-4ch8f.38.2 wave-2, the inverse of `secfBeToLe`):

  - `secfLeToBe` (`secfLeToBe_prog`, Secp256k1Field.lean:205): read four
    LITTLE-ENDIAN u64 limbs (LSB-first) at `a0` and write the 32-byte
    BIG-ENDIAN buffer at `a1`.

  Same nested bottom-test shape as `secfBeToLe` (outer `doWhile` over the 4
  limbs, inner `doWhileS` over the 8 bytes, snapshot-carrying the limb index
  `x5`), but the inner byte loop **disperses** one u64 into 8 bytes
  (`ANDI`/`SB`/`SRLI` at DECREASING destination offsets, LSB first) instead of
  assembling one (`LBU`/`OR`/`SLLI`).  Byte-identical to the bn254 twin
  `bnfLeToBe_prog`.

  Functional post (real, unweakened): the big-endian value of the 32 output
  bytes equals the little-endian decode of the four input u64 limbs —
  `beBytesToNat ws = leLimbsToNat [inLimb0, inLimb1, inLimb2, inLimb3]`.

  Byte-identity kernel-pinned: `<body>.flatten 0 ++ [ret] = secfLeToBe_prog`.
-/

import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.Secp256k1FieldConvSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt EvmAsm.Crypto
open Secp256k1FieldConvSAsm (frameOk)

namespace Secp256k1FieldLeToBeSAsm

/-- The `t`-th little-endian byte of a u64 (byte 0 = LSB). -/
def leByte (v : Word) (t : Nat) : BitVec 8 := BitVec.ofNat 8 (v.toNat >>> (8 * t))

/-- The 8-byte big-endian encoding of a u64 limb (byte at slice-index `s`
    is limb byte `7 - s`, MSB-first) — the layout `secfLeToBe` writes for one
    limb into `dst[24-8k .. 31-8k]`. -/
def beBytesOfLimb (v : Word) : List (BitVec 8) :=
  (List.range 8).map (fun s => leByte v (7 - s))

@[simp] theorem length_beBytesOfLimb (v : Word) : (beBytesOfLimb v).length = 8 := by
  simp [beBytesOfLimb]

/-- Inner byte-dispersal loop invariant, **snapshot-parameterized** by the
    inner loop's entry `(rf₀, ws₀, A₀)`.  At entry: `x5 = k` (limb index,
    carried through the inner loop only via this snapshot), `x28 = limb k`
    (loaded), `x6 = dst + (31 - 8k)` (LSB destination byte, written first),
    `x29 = 8`.  After the `(j+1)`-th body run:
    - `x29 = 7 - j`;
    - `x28 = limb >>> 8*(j+1)` (the still-unwritten high bytes);
    - `x6 = (entry x6) - (j+1)` (advanced toward the MSB / lower addresses);
    - `x5` carried; `x10`, `x11` preserved;
    - the `j+1` bytes at offsets `[(31-8k)-j .. (31-8k)]` of `ws` hold the low
      `j+1` bytes of the limb (LSB at the top offset). -/
def innerInv (src dst : Word) :
    RegFile → List (BitVec 8) → Assertion →
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ ws₀ A₀ j rf ws A =>
    let k := (rf₀.get .x5).toNat
    let limb := rf₀.get .x28
    rf.get .x29 = BitVec.ofNat 64 (7 - j)
    ∧ rf.get .x28 = BitVec.ofNat 64 (limb.toNat >>> (8 * (j + 1)))
    ∧ rf.get .x6 = rf₀.get .x6 - BitVec.ofNat 64 (j + 1)
    ∧ rf.get .x5 = rf₀.get .x5
    ∧ rf.get .x10 = src ∧ rf.get .x11 = dst
    ∧ ws.length = 32 ∧ frameOk src dst
    ∧ (∀ t, t ≤ j → getByteAt ws ((31 - 8 * k) - t) = leByte limb t)
    ∧ (∀ idx, 31 - 8 * k < idx → getByteAt ws idx = getByteAt ws₀ idx)
    ∧ A = A₀

/-- Outer limb loop invariant (plain `doWhile`, counting).  After the
    `(i+1)`-th body run: `x5 = i+1`, `x6 = 4`, pointers preserved, and the
    first `i+1` output limbs are the big-endian encodings of the corresponding
    input limbs — `(ws.drop (24-8m)).take 8 = beBytesOfLimb (inLimb m)` for
    `m ≤ i`, where `inLimb m = wsDword inBytes (8*m)`. -/
def outerInv (src dst : Word) (inBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = BitVec.ofNat 64 (i + 1)
    ∧ rf.get .x6 = (4 : Word)
    ∧ rf.get .x10 = src ∧ rf.get .x11 = dst
    ∧ ws.length = 32 ∧ frameOk src dst
    ∧ (∀ m, m ≤ i →
        (ws.drop (24 - 8 * m)).take 8 = beBytesOfLimb (wsDword inBytes (8 * m)))
    ∧ A = empAssertion

-- ============================================================================
-- The routine body (byte-identical to bnfLeToBe_prog / secfLeToBe_prog)
-- ============================================================================

def secfLeToBeBody (src dst : Word) (inBytes : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word)] ;;;
  .doWhile "outer" (.bne .x5 .x6) 3 (outerInv src dst inBytes)
    ( .block "setup"
        [ .SLLI .x6 .x5 (3 : BitVec 6),
          .ADD .x7 .x10 .x6,
          .LD .x28 .x7 (0 : BitVec 12),
          .LI .x6 (31 : Word),
          .SLLI .x7 .x5 (3 : BitVec 6),
          .SUB .x6 .x6 .x7,
          .ADD .x6 .x11 .x6,
          .LI .x29 (8 : Word) ] ;;;
      .doWhileS "inner" (.bne .x29 .x0) 7 (innerInv src dst)
        (.block "body"
          [ .ANDI .x30 .x28 (255 : BitVec 12),
            .SB .x6 .x30 (0 : BitVec 12),
            .SRLI .x28 .x28 (8 : BitVec 6),
            .ADDI .x6 .x6 (-1 : BitVec 12),
            .ADDI .x29 .x29 (-1 : BitVec 12) ]) ;;;
      .block "bump"
        [ .ADDI .x5 .x5 (1 : BitVec 12),
          .LI .x6 (4 : Word) ] )

def secfLeToBe_verified : Program := (secfLeToBeBody 0 0 []).flatten 0

#guard (secfLeToBe_verified : List Instr).length = 18
#guard (secfLeToBeBody 0 0 []).flatten 0 = (secfLeToBeBody 0 0 []).flatten 0x80000000
-- Byte-identity to the emitted routine: guest bytes do not move.
#guard (secfLeToBeBody 0 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
  = secfLeToBe_prog

-- ============================================================================
-- The function and its spec
-- ============================================================================

def secfLeToBeFn (src dst : Word) (inBytes orig : List (BitVec 8)) : Fn where
  name := "secfLeToBe"
  region := ⟨src, inBytes⟩
  rw := ⟨dst, 32⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧ orig.length = 32 ∧
    inBytes.length = 32 ∧
    src.toNat + 32 < 2 ^ 64 ∧ dst.toNat + 32 < 2 ^ 64 ∧
    (src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat) ∧
    A = empAssertion
  post := fun _ ws A =>
    beBytesToNat ws = Accel.leLimbsToNat
      [wsDword inBytes 0, wsDword inBytes 8, wsDword inBytes 16, wsDword inBytes 24]
    ∧ ws.length = 32 ∧ A = empAssertion
  body := secfLeToBeBody src dst inBytes

-- ============================================================================
-- Byte-list bridge (inverse of `leLimbs_chunks_eq_beBytesToNat`)
-- ============================================================================

/-- Generalized-accumulator unfolding of the `beBytesToNat` foldl (local copy
    of the private `Secp256k1FieldConvSAsm.foldl_be'`). -/
private theorem foldl_be' (bs : List (BitVec 8)) (acc : Nat) :
    List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) acc bs
      = acc * 256 ^ bs.length
        + List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) 0 bs := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (acc * 256 + b.toNat), ih (0 * 256 + b.toNat)]
    have h : acc * 256 * 256 ^ bs.length = acc * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    omega

/-- Big-endian value of a concatenation. -/
private theorem beBytesToNat_append (a b : List (BitVec 8)) :
    beBytesToNat (a ++ b) = beBytesToNat a * 256 ^ b.length + beBytesToNat b := by
  unfold beBytesToNat
  rw [List.foldl_append, foldl_be' b]

/-- The 8 big-endian bytes of a u64 decode back to its value. -/
private theorem beBytesToNat_beBytesOfLimb (v : Word) :
    beBytesToNat (beBytesOfLimb v) = v.toNat := by
  have hlt : v.toNat < 2 ^ 64 := v.isLt
  simp only [beBytesOfLimb, beBytesToNat, leByte, List.range, List.range.loop,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reduceMul]
  omega

/-- Byte-list bridge (inverse of `leLimbs_chunks_eq_beBytesToNat`): a 32-byte
    big-endian buffer whose four 8-byte big-endian blocks encode the limbs
    `[v3, v2, v1, v0]` decodes to `leLimbsToNat [v0, v1, v2, v3]`. -/
theorem beBytesToNat_beBlocks (v0 v1 v2 v3 : Word) :
    beBytesToNat (beBytesOfLimb v3 ++ beBytesOfLimb v2 ++ beBytesOfLimb v1
        ++ beBytesOfLimb v0)
      = Accel.leLimbsToNat [v0, v1, v2, v3] := by
  rw [beBytesToNat_append, beBytesToNat_append, beBytesToNat_append,
    beBytesToNat_beBytesOfLimb, beBytesToNat_beBytesOfLimb, beBytesToNat_beBytesOfLimb,
    beBytesToNat_beBytesOfLimb]
  simp only [length_beBytesOfLimb, Accel.leLimbsToNat, List.foldr]
  ring

-- ============================================================================
-- Block-execution engine helpers (own heartbeat budget)
-- ============================================================================

private def setupInstrs : List Instr :=
  [.SLLI .x6 .x5 (3 : BitVec 6), .ADD .x7 .x10 .x6, .LD .x28 .x7 (0 : BitVec 12),
   .LI .x6 (31 : Word), .SLLI .x7 .x5 (3 : BitVec 6), .SUB .x6 .x6 .x7,
   .ADD .x6 .x11 .x6, .LI .x29 (8 : Word)]

private def innerBodyInstrs : List Instr :=
  [.ANDI .x30 .x28 (255 : BitVec 12), .SB .x6 .x30 (0 : BitVec 12),
   .SRLI .x28 .x28 (8 : BitVec 6), .ADDI .x6 .x6 (-1 : BitVec 12),
   .ADDI .x29 .x29 (-1 : BitVec 12)]

private def bumpInstrs : List Instr :=
  [.ADDI .x5 .x5 (1 : BitVec 12), .LI .x6 (4 : Word)]

/-- `w &&& 0xff`, truncated to a byte, is the low byte of `w`. -/
private theorem and255_trunc (w : Word) :
    (w &&& (255 : Word)).truncate 8 = BitVec.ofNat 8 w.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat,
    show ((255 : Word)).toNat = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `ofNat 8` only sees the value mod 256, so a `mod 2^64` wrapper is invisible. -/
private theorem ofNat8_mod (a : Nat) : BitVec.ofNat 8 (a % 2 ^ 64) = BitVec.ofNat 8 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- An `LD` that misses the writable window reads the read-only region dword. -/
private theorem ld_romiss (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwb ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF reg rwb rf ws (.LD rd rs1 ofs)
      = (rf.set rd (reg.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF; dsimp only [aluSem, loadSem]; rw [if_neg h]

/-- A read-only dword at `src + 8k` misses the disjoint 32-byte writable
    window. -/
private theorem src_dword_miss (src dst : Word) (ws : List (BitVec 8)) (k : Nat)
    (hk : k < 4) (hws : ws.length = 32) (hfr : frameOk src dst) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw; rw [hws]; rcases hdisj with h | h <;> bv_omega

/-- The setup block, executed: loads limb `k = wsDword inBytes (8k)` into
    `x28`, points `x6` at the LSB destination byte `dst + (31 - 8k)`, seeds
    `x29 := 8`; `x5`/`x10`/`x11`/window untouched. -/
private theorem setup_exec (src dst : Word) (inBytes wsp : List (BitVec 8))
    (rfp : RegFile) (k : Nat) (hk : k < 4)
    (hx5 : rfp.get .x5 = BitVec.ofNat 64 k) (hx10 : rfp.get .x10 = src)
    (hx11 : rfp.get .x11 = dst) (hws : wsp.length = 32) (hfr : frameOk src dst) :
    (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).1.get .x5 = BitVec.ofNat 64 k
    ∧ (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).1.get .x28
        = wsDword inBytes (8 * k)
    ∧ (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).1.get .x6
        = dst + BitVec.ofNat 64 (31 - 8 * k)
    ∧ (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).1.get .x29 = (8 : Word)
    ∧ (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).1.get .x10 = src
    ∧ (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).1.get .x11 = dst
    ∧ (execBlock ⟨src, inBytes⟩ dst rfp wsp setupInstrs).2 = wsp := by
  have hX : (BitVec.ofNat 64 k <<< (3 : BitVec 6).toNat) = BitVec.ofNat 64 (8 * k) := by
    interval_cases k <;> decide
  have hdw : (Region.mk src inBytes).dwordAt (src + BitVec.ofNat 64 (8 * k))
      = wsDword inBytes (8 * k) := by
    have ho : (src + BitVec.ofNat 64 (8 * k) - src).toNat = 8 * k := by
      have : 8 * k < 2 ^ 64 := by omega
      bv_omega
    show packBytes ((inBytes.drop ((src + BitVec.ofNat 64 (8 * k) - src).toNat)).take 8) = _
    rw [ho]; rfl
  rw [show setupInstrs = [.SLLI .x6 .x5 (3 : BitVec 6), .ADD .x7 .x10 .x6,
      .LD .x28 .x7 (0 : BitVec 12), .LI .x6 (31 : Word), .SLLI .x7 .x5 (3 : BitVec 6),
      .SUB .x6 .x6 .x7, .ADD .x6 .x11 .x6, .LI .x29 (8 : Word)] from rfl]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  -- the LD reads `x7 = src + 8k` from the read-only region (missing the window)
  have haddr : ((RegFile.set (RegFile.set rfp .x6 (rfp.get .x5 <<< (3 : BitVec 6).toNat)) .x7
        ((RegFile.set rfp .x6 (rfp.get .x5 <<< (3 : BitVec 6).toNat)).get .x10
          + (RegFile.set rfp .x6 (rfp.get .x5 <<< (3 : BitVec 6).toNat)).get .x6)).get .x7)
      + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 (8 * k) := by
    rw [RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6), hx10,
      RegFile.get_set_self _ _ _ (by decide), hx5, hX,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    simp
  rw [execBlock_cons, ld_romiss ⟨src, inBytes⟩ dst _ wsp .x28 .x7 (0 : BitVec 12)
    (by rw [haddr]; exact src_dword_miss src dst wsp k hk hws hfr)]
  rw [haddr, hdw]
  dsimp only
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execBlock_nil]; dsimp only [execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hx5]
  · simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
  · simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hx11, hx5, hX]
    interval_cases k <;> bv_omega
  · simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
  · simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hx10]
  · simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, hx11]

/-- One inner body run: store the low byte of `x28` at the current
    destination offset `off`, shift `x28` right one byte, step the pointers. -/
private theorem inner_body_exec (src dst : Word) (inBytes ws : List (BitVec 8))
    (rf : RegFile) (off : Nat) (hoff : off < 32)
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 off) :
    (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).2
        = setBytes ws off [(rf.get .x28 &&& (255 : Word)).truncate 8]
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x28
        = rf.get .x28 >>> (8 : Nat)
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x6
        = rf.get .x6 + signExtend12 (-1 : BitVec 12)
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x29
        = rf.get .x29 + signExtend12 (-1 : BitVec 12)
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x5 = rf.get .x5
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x10 = rf.get .x10
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x11 = rf.get .x11 := by
  have haddr : ((rf.set .x30 (rf.get .x28 &&& signExtend12 (255 : BitVec 12))).get .x6
      + signExtend12 (0 : BitVec 12) - dst).toNat = off := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hx6]
    have : off < 2 ^ 64 := by omega
    bv_omega
  rw [show innerBodyInstrs = [.ANDI .x30 .x28 (255 : BitVec 12), .SB .x6 .x30 (0 : BitVec 12),
      .SRLI .x28 .x28 (8 : BitVec 6), .ADDI .x6 .x6 (-1 : BitVec 12),
      .ADDI .x29 .x29 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte ⟨src, inBytes⟩ dst _ _ .x6 .x30 (0 : BitVec 12) off haddr]
  dsimp only
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]; dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execBlock_nil]; dsimp only [execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, show signExtend12 (255 : BitVec 12) = (255 : Word) from by decide,
      show (8 : BitVec 6).toNat = 8 from rfl]

/-- Address side conditions of the inner body: its single `SB` writes byte
    `off < 32` of the writable window (in range; byte stores are 1-aligned). -/
private theorem inner_blockVCs (src dst : Word) (inBytes ws : List (BitVec 8))
    (rf : RegFile) (off : Nat) (hoff : off < 32)
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 off) (hws : ws.length = 32) :
    blockVCs ⟨src, inBytes⟩ dst rf ws innerBodyInstrs := by
  have haddr : ((rf.set .x30 (rf.get .x28 &&& signExtend12 (255 : BitVec 12))).get .x6
      + signExtend12 (0 : BitVec 12) - dst).toNat = off := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hx6]
    have : off < 2 ^ 64 := by omega
    bv_omega
  simp only [innerBodyInstrs, blockVCs, loadSem, storeSem, execInstrRF, aluSem]
  refine ⟨trivial, ⟨?_, ?_⟩, trivial, trivial, trivial, trivial⟩
  · show inRw dst ws ((rf.set .x30 (rf.get .x28 &&& signExtend12 (255 : BitVec 12))).get .x6
      + signExtend12 (0 : BitVec 12)) 1
    unfold inRw; rw [haddr, hws]; omega
  · show (1 : Nat) ∣ ((rf.set .x30 (rf.get .x28 &&& signExtend12 (255 : BitVec 12))).get .x6
      + signExtend12 (0 : BitVec 12) - dst).toNat
    exact Nat.one_dvd _

/-- The inner-loop snapshot after `setup`: `x5 = k < 4`, `x28` holds limb `k`,
    `x6` points at the LSB destination byte `dst + (31 - 8k)`, `x29 = 8`, and
    the earlier limbs `0..k-1` of the window already hold their big-endian
    blocks. -/
private theorem snap_facts (src dst : Word) (inBytes orig : List (BitVec 8))
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (hsp : Stmt.sp ⟨src, inBytes⟩ ⟨dst, 32⟩ (Stmt.block "setup" setupInstrs)
      (fun rf ws A =>
        Stmt.sp ⟨src, inBytes⟩ ⟨dst, 32⟩ (Stmt.block "init" [.LI .x5 (0 : Word)])
            (secfLeToBeFn src dst inBytes orig).pre rf ws A
          ∨ ∃ i < 3, outerInv src dst inBytes i rf ws A ∧ (Cond.bne .x5 .x6).holds rf)
      rf₀ ws₀ A₀) :
    ∃ k, k < 4 ∧ rf₀.get .x5 = BitVec.ofNat 64 k
      ∧ rf₀.get .x28 = wsDword inBytes (8 * k)
      ∧ rf₀.get .x6 = dst + BitVec.ofNat 64 (31 - 8 * k)
      ∧ rf₀.get .x29 = (8 : Word)
      ∧ rf₀.get .x10 = src ∧ rf₀.get .x11 = dst
      ∧ ws₀.length = 32 ∧ frameOk src dst
      ∧ (∀ m, m < k →
          (ws₀.drop (24 - 8 * m)).take 8 = beBytesOfLimb (wsDword inBytes (8 * m))) := by
  obtain ⟨rfp, wsp, hwsp, hreach, rfl, rfl⟩ := hsp
  obtain ⟨k, hk, hpx5, hpx10, hpx11, hpwslen, hpfr, hplimbs⟩ :
      ∃ k, k < 4 ∧ rfp.get .x5 = BitVec.ofNat 64 k ∧ rfp.get .x10 = src
        ∧ rfp.get .x11 = dst ∧ ws₀.length = 32 ∧ frameOk src dst
        ∧ (∀ m, m < k →
            (ws₀.drop (24 - 8 * m)).take 8 = beBytesOfLimb (wsDword inBytes (8 * m))) := by
    rcases hreach with hinit | ⟨i, hi, houter, hguard⟩
    · obtain ⟨rfi, wsi, hwsi, hpre, rfl, rfl⟩ := hinit
      obtain ⟨hx10, hx11, rfl, holen, hilen', hnws, hnwd, hdisj, -⟩ := hpre
      refine ⟨0, by omega, ?_, ?_, ?_, ?_, ⟨hnws, hnwd, hdisj⟩, by intro m hm; omega⟩
      all_goals simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10, hx11, holen]
      rfl
    · obtain ⟨hx5, hx6, hx10, hx11, hwslen, hfr, hlimbs, -⟩ := houter
      exact ⟨i + 1, by omega, hx5, hx10, hx11, hwslen, hfr, fun m hm => hlimbs m (by omega)⟩
  obtain ⟨he5, he28, he6, he29, he10, he11, he2⟩ :=
    setup_exec src dst inBytes ws₀ rfp k hk hpx5 hpx10 hpx11 hpwslen hpfr
  exact ⟨k, hk, he5, he28, he6, he29, he10, he11, he2 ▸ hpwslen, hpfr,
    fun m hm => he2 ▸ hplimbs m hm⟩

/-- `ofNat 64` commutes with an 8-bit right shift below the width. -/
private theorem ofNat_ushift (a : Nat) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a) >>> (8 : Nat) = BitVec.ofNat 64 (a >>> 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha]
  omega

/-- The stored low byte at step `i+1` is exactly `leByte limb (i+1)`. -/
private theorem storeByte_eq (limb : Word) (i : Nat) :
    ((BitVec.ofNat 64 (limb.toNat >>> (8 * (i + 1))) &&& (255 : Word)).truncate 8)
      = leByte limb (i + 1) := by
  rw [and255_trunc, BitVec.toNat_ofNat, ofNat8_mod]; rfl

/-- `ofNat` subtraction below the width. -/
private theorem ofNat_sub (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a) - (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `ofNat` successor. -/
private theorem ofNat_succ' (a : Nat) :
    BitVec.ofNat 64 a + (1 : Word) = BitVec.ofNat 64 (a + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((1 : Word)).toNat = 1 from rfl]
  omega

/-- Pointer decrement: `a - ofNat b - 1 = a - ofNat (b+1)` (as `+ (-1)`). -/
private theorem ptr_dec (a : Word) (b : Nat) :
    a - BitVec.ofNat 64 b + (-1 : Word) = a - BitVec.ofNat 64 (b + 1) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, show ((-1 : Word)).toNat = 2 ^ 64 - 1 from by decide]
  omega

/-- One inner-loop step, sealed behind an abstract-`rf` boundary (the
    `#9812`/`cfjzu.1` deep-recursion fix): from `innerInv i` with the guard
    holding, running the dispersal body once establishes `innerInv (i+1)`.
    All numeric side goals go through `ring` + `ofNat_sub`/`ofNat_succ'`
    (never `bv_omega`, which diverges on the 64-bit pointer subtraction). -/
private theorem inner_step_engine (src dst : Word) (inBytes : List (BitVec 8))
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion) (i k : Nat)
    (hk : k < 4) (hi : i < 7)
    (hs6 : rf₀.get .x6 = dst + BitVec.ofNat 64 (31 - 8 * k))
    (hkeq : (rf₀.get .x5).toNat = k)
    (hInv : innerInv src dst rf₀ ws₀ A₀ i rf ws A) :
    innerInv src dst rf₀ ws₀ A₀ (i + 1)
      (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1
      (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).2 A := by
  obtain ⟨hp29, hp28, hp6, hp5, hp10, hp11, hpws, hpfr, hpbytes, hpframe, hpA⟩ := hInv
  rw [hkeq] at hpbytes hpframe
  set limb := rf₀.get .x28 with hlimb
  have hle : i + 1 ≤ 31 - 8 * k := by omega
  have hoff : (31 - 8 * k) - (i + 1) < 32 := by omega
  have hse1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  -- current pointer = dst + off, off = (31-8k)-(i+1)
  have hx6 : rf.get .x6 = dst + BitVec.ofNat 64 ((31 - 8 * k) - (i + 1)) := by
    rw [hp6, hs6]
    apply BitVec.eq_of_toNat_eq
    have hd := dst.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  obtain ⟨e2, e28, e6, e29, e5, e10, e11⟩ :=
    inner_body_exec src dst inBytes ws rf ((31 - 8 * k) - (i + 1)) hoff hx6
  have hlimblt : limb.toNat >>> (8 * (i + 1)) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) limb.isLt
  dsimp only [innerInv]
  rw [hkeq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hpfr, ?_, ?_, hpA⟩
  · -- x29 = ofNat (7 - (i+1))
    rw [e29, hp29, hse1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show ((-1 : Word)).toNat = 2 ^ 64 - 1 from by decide]
    omega
  · -- x28 = ofNat (limb >>> 8*(i+2))
    rw [e28, hp28, ofNat_ushift _ hlimblt,
      show 8 * (i + 1 + 1) = 8 * (i + 1) + 8 from by omega, Nat.shiftRight_add]
  · -- x6 = rf₀.x6 - ofNat (i+2)
    rw [e6, hp6, hse1, ptr_dec (rf₀.get .x6) (i + 1)]
  · rw [e5, hp5]
  · rw [e10, hp10]
  · rw [e11, hp11]
  · rw [e2, length_setBytes]; exact hpws
  · -- byte fact: t ≤ i+1
    intro t ht
    rw [e2, getByteAt_setBytes _ _ _ _
      (by rw [hpws]; simp only [List.length_singleton]; omega)]
    by_cases hte : t = i + 1
    · subst hte
      rw [if_pos (by simp only [List.length_singleton]; omega),
        show (31 - 8 * k) - (i + 1) - ((31 - 8 * k) - (i + 1)) = 0 from by omega]
      show getByteAt [(rf.get .x28 &&& (255 : Word)).truncate 8] 0 = leByte limb (i + 1)
      rw [hp28]; exact storeByte_eq limb i
    · rw [if_neg (by simp only [List.length_singleton]; omega)]
      exact hpbytes t (by omega)
  · -- frame: bytes above the (new) top are untouched — the write is at
    -- offset (31-8k)-(i+1) ≤ 31-8k < idx
    intro idx hidx
    rw [e2, getByteAt_setBytes _ _ _ _
      (by rw [hpws]; simp only [List.length_singleton]; omega)]
    rw [if_neg (by simp only [List.length_singleton]; omega)]
    exact hpframe idx (by omega)

/-- The `bump` tail block: `x5 := k+1`, `x6 := 4`; window/`x10`/`x11` intact. -/
private theorem bump_exec (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (k : Nat) (hx5 : rf.get .x5 = BitVec.ofNat 64 k) :
    (execBlock reg rwb rf ws bumpInstrs).1.get .x5 = BitVec.ofNat 64 (k + 1)
    ∧ (execBlock reg rwb rf ws bumpInstrs).1.get .x6 = (4 : Word)
    ∧ (execBlock reg rwb rf ws bumpInstrs).1.get .x10 = rf.get .x10
    ∧ (execBlock reg rwb rf ws bumpInstrs).1.get .x11 = rf.get .x11
    ∧ (execBlock reg rwb rf ws bumpInstrs).2 = ws := by
  simp only [bumpInstrs, execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx5]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; exact ofNat_succ' k)
      | rfl
      | trivial

/-- The eight per-byte facts assemble the destination slice into
    `beBytesOfLimb limb`. -/
private theorem slice_eq_beBytesOfLimb (ws : List (BitVec 8)) (limb : Word) (k : Nat)
    (hk : k < 4) (hws : ws.length = 32)
    (hb : ∀ t, t ≤ 7 → getByteAt ws ((31 - 8 * k) - t) = leByte limb t) :
    (ws.drop (24 - 8 * k)).take 8 = beBytesOfLimb limb := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, hws, length_beBytesOfLimb]; omega
  · intro s h1 _
    have hs8 : s < 8 := by
      rw [List.length_take, List.length_drop, hws] at h1; omega
    have hidx : (24 - 8 * k) + s = (31 - 8 * k) - (7 - s) := by omega
    have hlt : (24 - 8 * k) + s < ws.length := by rw [hws]; omega
    rw [List.getElem_take, List.getElem_drop]
    rw [show (ws[(24 - 8 * k) + s]) = getByteAt ws ((24 - 8 * k) + s) from by
      unfold getByteAt; rw [dif_pos hlt]]
    rw [hidx, hb (7 - s) (by omega)]
    show leByte limb (7 - s) = (beBytesOfLimb limb)[s]
    simp only [beBytesOfLimb, List.getElem_map, List.getElem_range]

/-- Address side conditions of the `setup` block: its single `LD` routes to
    the read-only source region (missing the disjoint window), aligned and in
    range; every other instruction is register-only. -/
private theorem setup_blockVCs (src dst : Word) (inBytes ws : List (BitVec 8))
    (rf : RegFile) (k : Nat) (hk : k < 4) (hilen : inBytes.length = 32)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 k) (hx10 : rf.get .x10 = src)
    (hws : ws.length = 32) (hfr : frameOk src dst) :
    blockVCs ⟨src, inBytes⟩ dst rf ws setupInstrs := by
  have hX : (rf.get .x5 <<< (3 : BitVec 6).toNat) = BitVec.ofNat 64 (8 * k) := by
    rw [hx5]; interval_cases k <;> decide
  have haddr : (rf.get .x10 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12)) = src + BitVec.ofNat 64 (8 * k) := by
    rw [hx10, hX, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; simp
  have hmiss : ¬ inRw dst ws (rf.get .x10 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12)) 8 := by
    rw [haddr]; exact src_dword_miss src dst ws k hk hws hfr
  have hoff : (rf.get .x10 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12) - src).toNat = 8 * k := by
    rw [haddr]; bv_omega
  simp only [setupInstrs, blockVCs, loadSem, storeSem, execInstrRF, aluSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [if_neg hmiss]
  refine ⟨trivial, trivial, ⟨?_, ?_⟩, trivial, trivial, trivial, trivial, trivial, trivial⟩
  · show 8 ∣ (rf.get .x10 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12) - src).toNat
    rw [hoff]; exact ⟨k, by ring⟩
  · show (rf.get .x10 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12) - src).toNat + 8 ≤ inBytes.length
    rw [hoff, hilen]; omega

/-- One outer-loop step, sealed behind an abstract-`rf` boundary: from the
    inner-loop exit (`innerInv 7` — the current limb's 8 bytes written, and the
    frame preserving the earlier limbs) plus `snap_facts` (`x28 = wsDword
    inBytes (8k)`, earlier limbs set in `ws₀`), the `bump` block establishes
    `outerInv k`. -/
private theorem outer_step_engine (src dst : Word) (inBytes : List (BitVec 8))
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (rf2 : RegFile) (ws2 : List (BitVec 8)) (A' : Assertion) (k : Nat)
    (hk : k < 4) (hs5 : rf₀.get .x5 = BitVec.ofNat 64 k)
    (hs28 : rf₀.get .x28 = wsDword inBytes (8 * k)) (hws0len : ws₀.length = 32)
    (hlimbs : ∀ m, m < k →
      (ws₀.drop (24 - 8 * m)).take 8 = beBytesOfLimb (wsDword inBytes (8 * m)))
    (hA0 : A₀ = empAssertion)
    (hInv : innerInv src dst rf₀ ws₀ A₀ 7 rf2 ws2 A') :
    outerInv src dst inBytes k
      (execBlock ⟨src, inBytes⟩ dst rf2 ws2 bumpInstrs).1
      (execBlock ⟨src, inBytes⟩ dst rf2 ws2 bumpInstrs).2 A' := by
  obtain ⟨-, -, -, hp5, hp10, hp11, hpws, hpfr, hpbytes, hpframe, hpA⟩ := hInv
  have hkeq : (rf₀.get .x5).toNat = k := by rw [hs5, BitVec.toNat_ofNat]; omega
  rw [hkeq] at hpbytes hpframe
  have hx5 : rf2.get .x5 = BitVec.ofNat 64 k := by rw [hp5, hs5]
  have hws2 : ws2.length = 32 := hpws
  obtain ⟨hb5, hb6, hb10, hb11, hb2⟩ := bump_exec ⟨src, inBytes⟩ dst rf2 ws2 k hx5
  dsimp only [outerInv]
  refine ⟨hb5, hb6, hb10.trans hp10, hb11.trans hp11, ?_, hpfr, ?_, hpA.trans hA0⟩
  · rw [hb2]; exact hws2
  · intro m hm
    rw [hb2]
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · -- earlier limb m < k: its slice (offsets 24-8m..31-8m, all > 31-8k) is
      -- untouched by this limb's dispersal (frame) and matches ws₀
      have hslice : (ws2.drop (24 - 8 * m)).take 8 = (ws₀.drop (24 - 8 * m)).take 8 := by
        apply List.ext_getElem
        · rw [List.length_take, List.length_drop, List.length_take, List.length_drop,
            hws2, hws0len]
        · intro s h1 _
          have hs8 : s < 8 := by
            rw [List.length_take, List.length_drop, hws2] at h1; omega
          have hlt2 : (24 - 8 * m) + s < ws2.length := by rw [hws2]; omega
          have hlt0 : (24 - 8 * m) + s < ws₀.length := by rw [hws0len]; omega
          have hfr := hpframe ((24 - 8 * m) + s) (by omega)
          unfold getByteAt at hfr
          rw [dif_pos hlt2, dif_pos hlt0] at hfr
          simp only [List.getElem_take, List.getElem_drop]
          exact hfr
      rw [hslice]; exact hlimbs m hlt
    · rw [heq, slice_eq_beBytesOfLimb ws2 (rf₀.get .x28) k hk hws2 hpbytes, hs28]

/-- The first inner-body run, sealed behind an abstract-`rf` boundary (kept a
    standalone lemma so its `execBlock`/`setBytes` term is kernel-checked in
    isolation rather than inlined into the main VC — the `#9812` deep-recursion
    pattern): from the post-`setup` snapshot facts, one dispersal store
    establishes `innerInv 0`. -/
private theorem inner_init_engine (src dst : Word) (inBytes : List (BitVec 8))
    (rfp : RegFile) (wsp : List (BitVec 8)) (A₀ A' : Assertion) (k : Nat) (hk : k < 4)
    (hs5 : rfp.get .x5 = BitVec.ofNat 64 k)
    (hs6 : rfp.get .x6 = dst + BitVec.ofNat 64 (31 - 8 * k))
    (hs29 : rfp.get .x29 = (8 : Word))
    (hs10 : rfp.get .x10 = src) (hs11 : rfp.get .x11 = dst)
    (hwslen : wsp.length = 32) (hfr : frameOk src dst) (hAeq : A' = A₀) :
    innerInv src dst rfp wsp A₀ 0
      (execBlock ⟨src, inBytes⟩ dst rfp wsp innerBodyInstrs).1
      (execBlock ⟨src, inBytes⟩ dst rfp wsp innerBodyInstrs).2 A' := by
  have hkeq : (rfp.get .x5).toNat = k := by rw [hs5, BitVec.toNat_ofNat]; omega
  obtain ⟨e2, e28, e6, e29, e5, e10, e11⟩ :=
    inner_body_exec src dst inBytes wsp rfp (31 - 8 * k) (by omega) hs6
  dsimp only [innerInv]
  rw [hkeq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr, ?_, ?_, hAeq⟩
  · rw [e29, hs29, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
    bv_omega
  · rw [e28]
    apply BitVec.eq_of_toNat_eq
    have hlt : (rfp.get .x28).toNat < 2 ^ 64 := (rfp.get .x28).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, show 8 * (0 + 1) = 8 from rfl]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ 8) hlt)]
  · rw [e6, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
    bv_omega
  · rw [e5, hs5]
  · rw [e10, hs10]
  · rw [e11, hs11]
  · rw [e2, length_setBytes]; exact hwslen
  · intro t ht
    have ht0 : t = 0 := by omega
    subst ht0
    rw [e2, getByteAt_setBytes _ _ _ _ (by rw [hwslen]; simp only [List.length_singleton]; omega),
      show (31 - 8 * k) - 0 = 31 - 8 * k from by omega,
      if_pos (by simp only [List.length_singleton]; omega),
      show (31 - 8 * k) - (31 - 8 * k) = 0 from by omega]
    show getByteAt [(rfp.get .x28 &&& (255 : Word)).truncate 8] 0 = leByte (rfp.get .x28) 0
    unfold getByteAt
    rw [dif_pos (by simp only [List.length_singleton]; omega)]
    show (rfp.get .x28 &&& (255 : Word)).truncate 8 = leByte (rfp.get .x28) 0
    rw [and255_trunc]
    show BitVec.ofNat 8 ((rfp.get .x28).toNat) = BitVec.ofNat 8 ((rfp.get .x28).toNat >>> (8 * 0))
    rw [show 8 * 0 = 0 from rfl, Nat.shiftRight_zero]
  · intro idx hidx
    rw [e2, getByteAt_setBytes _ _ _ _ (by rw [hwslen]; simp only [List.length_singleton]; omega),
      if_neg (by simp only [List.length_singleton]; omega)]

theorem secfLeToBeFn_spec (src dst : Word) (inBytes orig : List (BitVec 8))
    (hwf : (Region.mk src inBytes).wf) (hrww : RwRegion.wf ⟨dst, 32⟩)
    (hilen : inBytes.length = 32) (base : Word) :
    (secfLeToBeFn src dst inBytes orig).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case secfLeToBe.outer.body.inner.exhausted =>
    rintro rf₀ ws₀ A₀ hreach₀ rf ws A ⟨hx29, -, -, -, -, -, -, -, -, -, -⟩
    intro hc; apply hc; rw [hx29]
    show (BitVec.ofNat 64 (7 - 7) : Word) = (0 : Word); decide
  case secfLeToBe.outer.exhausted =>
    rintro rf ws A ⟨hx5, hx6, -, -, -, -, -, -⟩
    intro hc; apply hc; rw [hx5, hx6]; decide
  case secfLeToBe.outer.body.setup.mem =>
    rintro rf ws A hlen hreach
    rcases hreach with hinit | ⟨i, hi, houter, hguard⟩
    · obtain ⟨rfi, wsi, hwsi, hpre, rfl, rfl⟩ := hinit
      obtain ⟨hx10, hx11, rfl, holen, -, hnws, hnwd, hdisj, -⟩ := hpre
      refine setup_blockVCs src dst inBytes _ _ 0 (by omega) hilen ?_ ?_ hlen ⟨hnws, hnwd, hdisj⟩
      · simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      · simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem, hx10]
    · obtain ⟨hx5, -, hx10, -, -, hfr, -, -⟩ := houter
      exact setup_blockVCs src dst inBytes ws rf (i + 1) (by omega) hilen hx5 hx10 hlen hfr
  case secfLeToBe.outer.body.inner.body.body.mem =>
    rintro rf ws A hlen hreach
    rcases hreach with hsetup | ⟨rf₀, ws₀, A₀, hsnap, i, hi, hInv, hg⟩
    · obtain ⟨k, hk, -, -, hs6, -, -, -, -, -, -⟩ :=
        snap_facts src dst inBytes orig rf ws A hsetup
      exact inner_blockVCs src dst inBytes ws rf (31 - 8 * k) (by omega) hs6 hlen
    · obtain ⟨k, hk, -, -, hs6, -, -, -, -, -, -⟩ :=
        snap_facts src dst inBytes orig rf₀ ws₀ A₀ hsnap
      obtain ⟨-, -, hp6, -, -, -, -, -, -, -, -⟩ := hInv
      have hx6 : rf.get .x6 = dst + BitVec.ofNat 64 ((31 - 8 * k) - (i + 1)) := by
        rw [hp6, hs6]
        apply BitVec.eq_of_toNat_eq
        have hd := dst.isLt
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      exact inner_blockVCs src dst inBytes ws rf ((31 - 8 * k) - (i + 1)) (by omega) hx6 hlen
  case secfLeToBe.post =>
    rintro rf ws A ⟨⟨i, hile, hx5, hx6, -, -, hwslen, -, hlimbs, hA⟩, hng⟩
    have hi3 : i = 3 := by
      dsimp only [Cond.holds] at hng
      rw [hx5, hx6] at hng
      have heq : (BitVec.ofNat 64 (i + 1) : Word) = 4 := Decidable.of_not_not hng
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, show ((4 : Word)).toNat = 4 from by decide] at this
      omega
    subst hi3
    refine ⟨?_, hwslen, hA⟩
    have l0 := hlimbs 0 (by omega)
    have l1 := hlimbs 1 (by omega)
    have l2 := hlimbs 2 (by omega)
    have l3 := hlimbs 3 (by omega)
    simp only [show (24 - 8 * 0 : Nat) = 24 from rfl, show (8 * 0 : Nat) = 0 from rfl,
      show (24 - 8 * 1 : Nat) = 16 from rfl, show (8 * 1 : Nat) = 8 from rfl,
      show (24 - 8 * 2 : Nat) = 8 from rfl, show (8 * 2 : Nat) = 16 from rfl,
      show (24 - 8 * 3 : Nat) = 0 from rfl, show (8 * 3 : Nat) = 24 from rfl,
      List.drop_zero] at l0 l1 l2 l3
    have hd24 : (ws.drop 24).take 8 = ws.drop 24 :=
      List.take_of_length_le (by rw [List.length_drop, hwslen])
    have l0' : ws.drop 24 = beBytesOfLimb (wsDword inBytes 0) := by rw [← hd24]; exact l0
    have hsplit : ws = ws.take 8 ++ ((ws.drop 8).take 8 ++ ((ws.drop 16).take 8
        ++ ws.drop 24)) := by
      conv_lhs => rw [← List.take_append_drop 8 ws]
      congr 1
      conv_lhs => rw [← List.take_append_drop 8 (ws.drop 8)]
      rw [List.drop_drop]
      congr 1
      conv_lhs => rw [← List.take_append_drop 8 (ws.drop 16)]
      rw [List.drop_drop]
    rw [hsplit, l3, l2, l1, l0', ← List.append_assoc, ← List.append_assoc]
    exact beBytesToNat_beBlocks (wsDword inBytes 0) (wsDword inBytes 8)
      (wsDword inBytes 16) (wsDword inBytes 24)
  case secfLeToBe.outer.body.inner.inv_init =>
    rintro rf₀ ws₀ A₀ hsnap rf' ws' A' ⟨rfp, wsp, hwsp, ⟨hrp, hwp, hAeq⟩, rfl, rfl⟩
    subst hrp hwp
    obtain ⟨k, hk, hs5, -, hs6, hs29, hs10, hs11, hws0len, hfr, _⟩ :=
      snap_facts src dst inBytes orig rfp wsp A₀ hsnap
    exact inner_init_engine src dst inBytes rfp wsp A₀ A' k hk hs5 hs6 hs29 hs10 hs11
      hws0len hfr hAeq
  case secfLeToBe.outer.body.inner.inv_step =>
    rintro rf₀ ws₀ A₀ hsnap i hi rf' ws' A' ⟨rfp, wsp, hwsp, ⟨hInv, hg⟩, rfl, rfl⟩
    obtain ⟨k, hk, hs5, -, hs6, -, -, -, -, -, -⟩ :=
      snap_facts src dst inBytes orig rf₀ ws₀ A₀ hsnap
    have hkeq : (rf₀.get .x5).toNat = k := by rw [hs5, BitVec.toNat_ofNat]; omega
    exact inner_step_engine src dst inBytes rf₀ ws₀ A₀ rfp wsp A' i k hk hi hs6 hkeq hInv
  case secfLeToBe.outer.inv_init =>
    rintro rf' ws' A'
      ⟨rf2, ws2, hws2len, ⟨rf₀, ws₀, A₀, hsetup, ⟨j, hj, hInv⟩, hng⟩, rfl, rfl⟩
    have hj7 : j = 7 := by
      have hp29 : rf2.get .x29 = BitVec.ofNat 64 (7 - j) := hInv.1
      have hx0 : rf2.get .x29 = rf2.get .x0 := by
        simp only [Cond.holds] at hng; exact not_not.mp hng
      rw [hp29, RegFile.get_x0] at hx0
      have := congrArg BitVec.toNat hx0
      rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
      omega
    subst hj7
    obtain ⟨rfpre, wspre, -, hinit, hrf0, hws0⟩ := hsetup
    obtain ⟨rfi, wsi, -, hpre, hrfpre, hwspre⟩ := hinit
    obtain ⟨hx10, hx11, hwseq, holen, -, hnws, hnwd, hdisj, hA0⟩ := hpre
    have hpre5 : rfpre.get .x5 = BitVec.ofNat 64 0 := by
      rw [hrfpre]; simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    have hpre10 : rfpre.get .x10 = src := by
      rw [hrfpre]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
      exact hx10
    have hpre11 : rfpre.get .x11 = dst := by
      rw [hrfpre]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      exact hx11
    have hprelen : wspre.length = 32 := by
      rw [hwspre]; simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [hwseq]; exact holen
    obtain ⟨he5, he28, -, -, -, -, he2⟩ :=
      setup_exec src dst inBytes wspre rfpre 0 (by omega) hpre5 hpre10 hpre11 hprelen
        ⟨hnws, hnwd, hdisj⟩
    -- keep `rf₀`/`ws₀` opaque (the setup `LD` makes the execBlock term whnf-explode
    -- if substituted into the engine application); normalize the `Fn.region`/`rw`
    -- projections to the literal window so `hrf0`/`hws0` match `setup_exec`'s output.
    rw [show (secfLeToBeFn src dst inBytes orig).region = (⟨src, inBytes⟩ : Region) from rfl,
      show (secfLeToBeFn src dst inBytes orig).rw.base = dst from rfl] at hrf0 hws0 ⊢
    have hs5 : rf₀.get .x5 = BitVec.ofNat 64 0 := by rw [hrf0]; exact he5
    have hs28 : rf₀.get .x28 = wsDword inBytes (8 * 0) := by rw [hrf0]; exact he28
    have hws0len : ws₀.length = 32 := by rw [hws0]; exact he2 ▸ hprelen
    exact outer_step_engine src dst inBytes rf₀ ws₀ A₀ rf2 ws' A' 0 (by omega)
      hs5 hs28 hws0len (fun m hm => by omega) hA0 hInv
  case secfLeToBe.outer.inv_step =>
    rintro i hi rf' ws' A'
      ⟨rf2, ws2, hws2len, ⟨rf₀, ws₀, A₀, hsetup, ⟨j, hj, hInv⟩, hng⟩, rfl, rfl⟩
    have hj7 : j = 7 := by
      have hp29 : rf2.get .x29 = BitVec.ofNat 64 (7 - j) := hInv.1
      have hx0 : rf2.get .x29 = rf2.get .x0 := by
        simp only [Cond.holds] at hng; exact not_not.mp hng
      rw [hp29, RegFile.get_x0] at hx0
      have := congrArg BitVec.toNat hx0
      rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
      omega
    subst hj7
    obtain ⟨rfpre, wspre, -, ⟨houter, -⟩, hrf0, hws0⟩ := hsetup
    obtain ⟨ho5, -, ho10, ho11, howslen, hofr, holimbs, hA0⟩ := houter
    obtain ⟨he5, he28, -, -, -, -, he2⟩ :=
      setup_exec src dst inBytes wspre rfpre (i + 1) (by omega) ho5 ho10 ho11 howslen hofr
    rw [show (secfLeToBeFn src dst inBytes orig).region = (⟨src, inBytes⟩ : Region) from rfl,
      show (secfLeToBeFn src dst inBytes orig).rw.base = dst from rfl] at hrf0 hws0 ⊢
    have hs5 : rf₀.get .x5 = BitVec.ofNat 64 (i + 1) := by rw [hrf0]; exact he5
    have hs28 : rf₀.get .x28 = wsDword inBytes (8 * (i + 1)) := by rw [hrf0]; exact he28
    have hws0len : ws₀.length = 32 := by rw [hws0]; exact he2 ▸ howslen
    have hlimbs : ∀ m, m < i + 1 →
        (ws₀.drop (24 - 8 * m)).take 8 = beBytesOfLimb (wsDword inBytes (8 * m)) := by
      intro m hm; rw [hws0]; exact he2 ▸ holimbs m (by omega)
    exact outer_step_engine src dst inBytes rf₀ ws₀ A₀ rf2 ws' A' (i + 1) (by omega)
      hs5 hs28 hws0len hlimbs hA0 hInv

end Secp256k1FieldLeToBeSAsm

end EvmAsm.Codegen
