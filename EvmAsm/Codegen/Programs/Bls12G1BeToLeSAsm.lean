/-
  EvmAsm.Codegen.Programs.Bls12G1BeToLeSAsm

  Verified SAsm port of the secp256k1 BE→LE field-element converter
  (bead evm-asm-4ch8f.38.2 wave-2, unblocked by the merged `doWhileS`
  combinator, `.69`/#9822):

  - `blsgBeToLe` (`blsgBeToLe_prog`, Bls12G1.lean:168): convert the
    48-byte BIG-ENDIAN buffer at `a0` into six LITTLE-ENDIAN u64 limbs
    (LSB-first) at `a1` — the ziskemu Arith256Mod operand format.

  Shape (confirmed byte-identical to the bn254 analogue `blsgBeToLe_prog`
  that `Codegen/Proofs/DoWhileDemo.lean` already pins): a nested bottom-test
  loop —
    * OUTER `doWhile` (`x5 = 0..4`, limb index; back-edge `BNE x5 x6(=4)`),
      whose body rereads `x5` after the inner loop to address the
      destination limb;
    * INNER `doWhileS` (`x29 = 8..0`, byte-in-limb; back-edge `BNE x29 x0`),
      assembling one big-endian u64 from 8 bytes — snapshot-parameterized so
      the enclosing iteration's `x5` survives the inner loop (the whole
      reason `doWhileS` exists).

  Functional post (real, unweakened, in the `.38.1`/`Accel` Nat vocabulary):
  the little-endian decode of the six output limbs equals the big-endian
  value of the input 48 bytes — `wsNat256 ws 0 = beBytesToNat inBytes`.

  Byte-identity is kernel-pinned: `<body>.flatten 0 ++ [ret] = blsgBeToLe_prog`
  (exact — the flatten matches, so guest bytes do not move).
-/

import Mathlib.Tactic.Ring
import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bls12G1

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt EvmAsm.Crypto

namespace Bls12G1BeToLeSAsm

/-- The big-endian u64 value of the `k`-th 8-byte chunk of a 48-byte buffer,
    counting from the LEAST-significant limb (`k = 0` ⇒ bytes 24..31, the low
    64 bits; `k = 3` ⇒ bytes 0..7, the high 64 bits). -/
def beChunk (inBytes : List (BitVec 8)) (k : Nat) : Nat :=
  beBytesToNat ((inBytes.drop (40 - 8 * k)).take 8)

/-- The read-only/writable regions are 48 bytes, non-wrapping and disjoint —
    the frame conditions of `pre`, carried through every loop invariant so
    the per-access routing VCs stay provable at any iteration. -/
def frameOk (src dst : Word) : Prop :=
  src.toNat + 48 < 2 ^ 64 ∧ dst.toNat + 48 < 2 ^ 64
  ∧ (src.toNat + 48 ≤ dst.toNat ∨ dst.toNat + 48 ≤ src.toNat)

-- ============================================================================
-- Invariants
-- ============================================================================

/-- Inner byte-assembly loop invariant, **snapshot-parameterized** by the
    inner loop's entry state `(rf₀, ws₀, A₀)`.  At entry the outer iteration
    has set `x5 = k` (the limb index, carried through the inner loop only via
    this snapshot), `x6 = src + (24 - 8k)` (MSB-first source byte pointer),
    `x28 = 0`, `x29 = 8`.  After the `(j+1)`-th inner body run:
    - `x29 = 7 - j` (bytes remaining);
    - `x28` = the big-endian value of the `j+1` bytes read so far;
    - `x6` = the entry pointer advanced by `j+1`;
    - `x5`, `x10`, `x11`, and the writable window are unchanged from entry. -/
def innerInv (src dst : Word) (inBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion →
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ ws₀ _ j rf ws _ =>
    let k := (rf₀.get .x5).toNat
    rf.get .x29 = BitVec.ofNat 64 (7 - j)
    ∧ rf.get .x28 = BitVec.ofNat 64 (beBytesToNat ((inBytes.drop (40 - 8 * k)).take (j + 1)))
    ∧ rf.get .x6 = rf₀.get .x6 + BitVec.ofNat 64 (j + 1)
    ∧ rf.get .x5 = rf₀.get .x5
    ∧ rf.get .x10 = src ∧ rf.get .x11 = dst
    ∧ ws = ws₀ ∧ frameOk src dst

/-- Outer limb loop invariant (plain `doWhile`, genuinely counting).  After
    the `(i+1)`-th outer body run: `x5 = i + 1` limbs are done, `x6 = 4` (the
    bound, reloaded at the tail), the pointers are preserved, and the first
    `i+1` limbs of the writable window hold their big-endian chunk values. -/
def outerInv (src dst : Word) (inBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x5 = BitVec.ofNat 64 (i + 1)
    ∧ rf.get .x6 = (6 : Word)
    ∧ rf.get .x10 = src ∧ rf.get .x11 = dst
    ∧ ws.length = 48 ∧ frameOk src dst
    ∧ ∀ m, m ≤ i → wsDword ws (8 * m) = BitVec.ofNat 64 (beChunk inBytes m)

-- ============================================================================
-- The routine body (shape identical to DoWhileDemo.bnfOuterNestedSlice)
-- ============================================================================

/-- The BE→LE converter body: `init` prologue, then the outer limb
    `doWhile` whose body is a setup block, the inner byte `doWhileS`, and a
    store-limb tail block.  Parameterized by the invariant data `(src, dst,
    inBytes)`; the emitted instructions are independent of it (flatten
    ignores `inv`), so the byte-tie below uses dummy arguments. -/
def blsgBeToLeBody (src dst : Word) (inBytes : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word)] ;;;
  .doWhile "outer" (.bne .x5 .x6) 5 (outerInv src dst inBytes)
    ( .block "setup"
        [ .LI .x6 (40 : Word),
          .SLLI .x7 .x5 (3 : BitVec 6),
          .SUB .x6 .x6 .x7,
          .ADD .x6 .x10 .x6,
          .LI .x28 (0 : Word),
          .LI .x29 (8 : Word) ] ;;;
      .doWhileS "inner" (.bne .x29 .x0) 7 (innerInv src dst inBytes)
        (.block "body"
          [ .SLLI .x28 .x28 (8 : BitVec 6),
            .LBU .x30 .x6 (0 : BitVec 12),
            .OR .x28 .x28 .x30,
            .ADDI .x6 .x6 (1 : BitVec 12),
            .ADDI .x29 .x29 (-1 : BitVec 12) ]) ;;;
      .block "storeLimb"
        [ .SLLI .x7 .x5 (3 : BitVec 6),
          .ADD .x7 .x11 .x7,
          .SD .x7 .x28 (0 : BitVec 12),
          .ADDI .x5 .x5 (1 : BitVec 12),
          .LI .x6 (6 : Word) ] )

def blsgBeToLe_verified : Program := (blsgBeToLeBody 0 0 []).flatten 0

#guard (blsgBeToLe_verified : List Instr).length = 19
#guard (blsgBeToLeBody 0 0 []).flatten 0 = (blsgBeToLeBody 0 0 []).flatten 0x80000000
-- Byte-identity to the emitted routine: the nested bottom-test loop plus the
-- calling-convention `ret` epilogue reproduce `blsgBeToLe_prog` exactly.
#guard (blsgBeToLeBody 0 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
  = blsgBeToLe_prog

-- ============================================================================
-- The function and its spec
-- ============================================================================

def blsgBeToLeFn (src dst : Word) (inBytes orig : List (BitVec 8)) : Fn where
  name := "blsgBeToLe"
  region := ⟨src, inBytes⟩
  rw := ⟨dst, 48⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧ orig.length = 48 ∧
    inBytes.length = 48 ∧
    src.toNat + 48 < 2 ^ 64 ∧ dst.toNat + 48 < 2 ^ 64 ∧
    (src.toNat + 48 ≤ dst.toNat ∨ dst.toNat + 48 ≤ src.toNat)
  post := fun _ ws _ => Accel.leLimbsToNat [wsDword ws 0, wsDword ws 8, wsDword ws 16, wsDword ws 24, wsDword ws 32, wsDword ws 40] = beBytesToNat inBytes ∧ ws.length = 48
  body := blsgBeToLeBody src dst inBytes

/-- Generalized-accumulator unfolding of the `beBytesToNat` foldl (local
    copy of the private `PowLadder.foldl_be`). -/
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

/-- Big-endian value of a concatenation: the high part is shifted by the low
    part's byte width. -/
private theorem beBytesToNat_append (a b : List (BitVec 8)) :
    beBytesToNat (a ++ b) = beBytesToNat a * 256 ^ b.length + beBytesToNat b := by
  unfold beBytesToNat
  rw [List.foldl_append, foldl_be' b]

/-- Each 8-byte chunk fits in a u64. -/
private theorem beChunk_lt (inBytes : List (BitVec 8)) (k : Nat) :
    beChunk inBytes k < 2 ^ 64 := by
  have hlt := beBytesToNat_lt ((inBytes.drop (40 - 8 * k)).take 8)
  have hlen : ((inBytes.drop (40 - 8 * k)).take 8).length ≤ 8 := by
    rw [List.length_take]; omega
  exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- One more big-endian byte extends the running value by a base-256 digit. -/
private theorem beBytesToNat_take_succ (l : List (BitVec 8)) (n : Nat)
    (hn : n < l.length) :
    beBytesToNat (l.take (n + 1))
      = beBytesToNat (l.take n) * 256 + (l.getD n 0).toNat := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some,
    beBytesToNat_append]
  simp [beBytesToNat, List.getD, List.getElem?_eq_getElem hn]

/-- A shifted value or-ed with a small byte is their sum (disjoint bits). -/
private theorem mul_pow_lor (v : Nat) (b : Nat) (hb : b < 2 ^ 8) :
    v * 2 ^ 8 ||| b = v * 2 ^ 8 + b := by
  have key : v * 2 ^ 8 ||| b = 2 ^ 8 * v + b := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add v hb j, Nat.testBit_mul_two_pow]
    rcases Nat.lt_or_ge j 8 with hj | hj
    · simp [Nat.not_le.mpr hj, hj]
    · rw [Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hj))]
      simp [Nat.not_lt.mpr hj, hj]
  rw [key]; ring

/-- Shift-then-or a byte in: exactly a base-256 append when the accumulator
    fits in the low 56 bits. -/
private theorem shiftOr_eq (v : Nat) (b : BitVec 8) (hv : v < 2 ^ 56) :
    (BitVec.ofNat 64 v <<< (8 : Nat)) ||| (b.zeroExtend 64)
      = BitVec.ofNat 64 (v * 256 + b.toNat) := by
  have hb : b.toNat < 256 := b.isLt
  have hze : (b.zeroExtend 64).toNat = b.toNat := by have := b.isLt; simp; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, hze, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : v * 2 ^ 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : v * 256 + b.toNat < 2 ^ 64),
    mul_pow_lor v b.toNat (by omega)]
  omega

/-- Byte-list bridge: the little-endian decode of the six big-endian chunks
    of a 48-byte buffer equals the big-endian value of the whole buffer. -/
theorem leLimbs_chunks_eq_beBytesToNat (inBytes : List (BitVec 8))
    (h : inBytes.length = 48) :
    Accel.leLimbsToNat
      [BitVec.ofNat 64 (beChunk inBytes 0), BitVec.ofNat 64 (beChunk inBytes 1),
       BitVec.ofNat 64 (beChunk inBytes 2), BitVec.ofNat 64 (beChunk inBytes 3),
       BitVec.ofNat 64 (beChunk inBytes 4), BitVec.ofNat 64 (beChunk inBytes 5)]
      = beBytesToNat inBytes := by
  have hlen8 : (inBytes.drop 8).length = 40 := by rw [List.length_drop, h]
  have hlen16 : (inBytes.drop 16).length = 32 := by rw [List.length_drop, h]
  have hlen24 : (inBytes.drop 24).length = 24 := by rw [List.length_drop, h]
  have hlen32 : (inBytes.drop 32).length = 16 := by rw [List.length_drop, h]
  have hlen40 : (inBytes.drop 40).length = 8 := by rw [List.length_drop, h]
  have hc5 : beChunk inBytes 5 = beBytesToNat (inBytes.take 8) := by
    simp [beChunk]
  have hc4 : beChunk inBytes 4 = beBytesToNat ((inBytes.drop 8).take 8) := by
    simp [beChunk]
  have hc3 : beChunk inBytes 3 = beBytesToNat ((inBytes.drop 16).take 8) := by
    simp [beChunk]
  have hc2 : beChunk inBytes 2 = beBytesToNat ((inBytes.drop 24).take 8) := by
    simp [beChunk]
  have hc1 : beChunk inBytes 1 = beBytesToNat ((inBytes.drop 32).take 8) := by
    simp [beChunk]
  have hc0 : beChunk inBytes 0 = beBytesToNat (inBytes.drop 40) := by
    rw [beChunk, Nat.sub_zero, List.take_of_length_le (by rw [hlen40])]
  have hdrop16 : (inBytes.drop 8).drop 8 = inBytes.drop 16 := by
    rw [List.drop_drop]
  have hdrop24 : (inBytes.drop 16).drop 8 = inBytes.drop 24 := by
    rw [List.drop_drop]
  have hdrop32 : (inBytes.drop 24).drop 8 = inBytes.drop 32 := by
    rw [List.drop_drop]
  have hdrop40 : (inBytes.drop 32).drop 8 = inBytes.drop 40 := by
    rw [List.drop_drop]
  have hdecomp : beBytesToNat inBytes
      = beBytesToNat (inBytes.take 8) * 256 ^ 40
        + (beBytesToNat ((inBytes.drop 8).take 8) * 256 ^ 32
          + (beBytesToNat ((inBytes.drop 16).take 8) * 256 ^ 24
            + (beBytesToNat ((inBytes.drop 24).take 8) * 256 ^ 16
              + (beBytesToNat ((inBytes.drop 32).take 8) * 256 ^ 8
                + beBytesToNat (inBytes.drop 40))))) := by
    conv_lhs => rw [← List.take_append_drop 8 inBytes]
    rw [beBytesToNat_append, hlen8]
    conv_lhs => rw [show inBytes.drop 8
      = (inBytes.drop 8).take 8 ++ (inBytes.drop 8).drop 8 from
        (List.take_append_drop 8 (inBytes.drop 8)).symm, hdrop16]
    rw [beBytesToNat_append, hlen16]
    conv_lhs => rw [show inBytes.drop 16
      = (inBytes.drop 16).take 8 ++ (inBytes.drop 16).drop 8 from
        (List.take_append_drop 8 (inBytes.drop 16)).symm, hdrop24]
    rw [beBytesToNat_append, hlen24]
    conv_lhs => rw [show inBytes.drop 24
      = (inBytes.drop 24).take 8 ++ (inBytes.drop 24).drop 8 from
        (List.take_append_drop 8 (inBytes.drop 24)).symm, hdrop32]
    rw [beBytesToNat_append, hlen32]
    conv_lhs => rw [show inBytes.drop 32
      = (inBytes.drop 32).take 8 ++ (inBytes.drop 32).drop 8 from
        (List.take_append_drop 8 (inBytes.drop 32)).symm, hdrop40]
    rw [beBytesToNat_append, hlen40]
  have p8 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  have p16 : (256 : Nat) ^ 16 = 2 ^ 64 * 2 ^ 64 := by norm_num
  have p24 : (256 : Nat) ^ 24 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by norm_num
  have p32 : (256 : Nat) ^ 32 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by norm_num
  have p40 : (256 : Nat) ^ 40 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by norm_num
  simp only [Accel.leLimbsToNat, List.foldr, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (beChunk_lt inBytes 0), Nat.mod_eq_of_lt (beChunk_lt inBytes 1),
    Nat.mod_eq_of_lt (beChunk_lt inBytes 2), Nat.mod_eq_of_lt (beChunk_lt inBytes 3),
    Nat.mod_eq_of_lt (beChunk_lt inBytes 4), Nat.mod_eq_of_lt (beChunk_lt inBytes 5)]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hdecomp, p8, p16, p24, p32, p40]
  ring

-- ============================================================================
-- Block-execution engine helpers (own heartbeat budget)
-- ============================================================================

/-- The setup block, executed: `x6 := src + (24 - 8k)` (MSB-first chunk
    pointer for limb `k`), `x28 := 0`, `x29 := 8`; `x5`/`x10`/`x11`/window
    untouched. -/
private def setupInstrs : List Instr :=
  [.LI .x6 (40 : Word), .SLLI .x7 .x5 (3 : BitVec 6), .SUB .x6 .x6 .x7,
   .ADD .x6 .x10 .x6, .LI .x28 (0 : Word), .LI .x29 (8 : Word)]

private theorem setup_exec (reg : Region) (rwb src : Word) (rfp : RegFile)
    (wsp : List (BitVec 8)) (k : Nat) (hk : k < 6)
    (hx5 : rfp.get .x5 = BitVec.ofNat 64 k) (hx10 : rfp.get .x10 = src) :
    (execBlock reg rwb rfp wsp setupInstrs).1.get .x5 = BitVec.ofNat 64 k
    ∧ (execBlock reg rwb rfp wsp setupInstrs).1.get .x6 = src + BitVec.ofNat 64 (40 - 8 * k)
    ∧ (execBlock reg rwb rfp wsp setupInstrs).1.get .x28 = (0 : Word)
    ∧ (execBlock reg rwb rfp wsp setupInstrs).1.get .x29 = (8 : Word)
    ∧ (execBlock reg rwb rfp wsp setupInstrs).1.get .x10 = src
    ∧ (execBlock reg rwb rfp wsp setupInstrs).1.get .x11 = rfp.get .x11
    ∧ (execBlock reg rwb rfp wsp setupInstrs).2 = wsp := by
  simp only [setupInstrs, execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx5, hx10,
    true_and, and_true]
  congr 1
  interval_cases k <;> decide

private def innerBodyInstrs : List Instr :=
  [.SLLI .x28 .x28 (8 : BitVec 6), .LBU .x30 .x6 (0 : BitVec 12),
   .OR .x28 .x28 .x30, .ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x29 .x29 (-1 : BitVec 12)]

private def storeLimbInstrs : List Instr :=
  [.SLLI .x7 .x5 (3 : BitVec 6), .ADD .x7 .x11 .x7, .SD .x7 .x28 (0 : BitVec 12),
   .ADDI .x5 .x5 (1 : BitVec 12), .LI .x6 (6 : Word)]

/-- An `LBU` that misses the writable window reads the read-only region byte. -/
private theorem lbu_romiss (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwb ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF reg rwb rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((reg.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF; dsimp only [aluSem, loadSem]; rw [if_neg h]

/-- The read-only region byte at `src + o`. -/
private theorem byteAt_src (src : Word) (inBytes : List (BitVec 8)) (o : Nat)
    (ho : o < 2 ^ 64) :
    (Region.mk src inBytes).byteAt (src + BitVec.ofNat 64 o) = inBytes.getD o 0 := by
  show inBytes.getD ((src + BitVec.ofNat 64 o) - src).toNat 0 = inBytes.getD o 0
  congr 1
  bv_omega

/-- A source-region byte at offset `o < 48` misses the disjoint 48-byte
    writable window. -/
private theorem src_miss (src dst : Word) (ws : List (BitVec 8)) (o : Nat)
    (ho : o < 48) (hws : ws.length = 48) (hfr : frameOk src dst) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 o) 1 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

/-- One inner body run: accumulate the source byte at `src + o` (missing the
    disjoint window), advance the pointer, decrement the counter. -/
private theorem inner_body_exec (src dst : Word) (inBytes ws : List (BitVec 8))
    (rf : RegFile) (o : Nat) (ho : o < 48)
    (hx6 : rf.get .x6 = src + BitVec.ofNat 64 o) (hws : ws.length = 48)
    (hfr : frameOk src dst) :
    (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x28
        = (rf.get .x28 <<< (8 : Nat)) ||| ((inBytes.getD o 0).zeroExtend 64)
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x29
        = rf.get .x29 + signExtend12 (-1 : BitVec 12)
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x6
        = rf.get .x6 + signExtend12 (1 : BitVec 12)
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x5 = rf.get .x5
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x10 = rf.get .x10
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1.get .x11 = rf.get .x11
    ∧ (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).2 = ws := by
  have haddr : (rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x6
      + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 o := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hx6]
    simp
  have hmiss : ¬ inRw dst ws
      ((rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x6
        + signExtend12 (0 : BitVec 12)) 1 := by
    rw [haddr]; exact src_miss src dst ws o ho hws hfr
  rw [show innerBodyInstrs = [.SLLI .x28 .x28 (8 : BitVec 6), .LBU .x30 .x6 (0 : BitVec 12),
      .OR .x28 .x28 .x30, .ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x29 .x29 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons,
    show execInstrRF ⟨src, inBytes⟩ dst rf ws (.SLLI .x28 .x28 (8 : BitVec 6))
      = (rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat), ws) from rfl]
  rw [execBlock_cons, lbu_romiss _ _ _ _ .x30 .x6 (0 : BitVec 12) hmiss, haddr,
    byteAt_src src inBytes o (by omega)]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, show (8 : BitVec 6).toNat = 8 from rfl]

/-- The store-limb tail block: write the assembled limb `x28` to `dst + 8k`,
    bump the counter to `k+1`, reload `x6 := 4`. -/
private theorem storeLimb_exec (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (k : Nat) (hk : k < 6)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 k) (hx11 : rf.get .x11 = dst) :
    (execBlock reg dst rf ws storeLimbInstrs).2
        = setBytes ws (8 * k) (dwordBytes (rf.get .x28))
    ∧ (execBlock reg dst rf ws storeLimbInstrs).1.get .x5 = BitVec.ofNat 64 (k + 1)
    ∧ (execBlock reg dst rf ws storeLimbInstrs).1.get .x6 = (6 : Word)
    ∧ (execBlock reg dst rf ws storeLimbInstrs).1.get .x10 = rf.get .x10
    ∧ (execBlock reg dst rf ws storeLimbInstrs).1.get .x11 = dst := by
  have hX : (BitVec.ofNat 64 k <<< (3 : BitVec 6).toNat) = BitVec.ofNat 64 (8 * k) := by
    interval_cases k <;> decide
  have hk64 : 8 * k < 2 ^ 64 := by omega
  have haddr : ((rf.get .x11 + rf.get .x5 <<< (3 : BitVec 6).toNat)
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * k := by
    rw [hx5, hX, hx11, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    have : ((dst + BitVec.ofNat 64 (8 * k) + 0 - dst)).toNat = 8 * k := by bv_omega
    simpa using this
  have hx5succ : (BitVec.ofNat 64 k : Word) + signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (k + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show ((signExtend12 (1 : BitVec 12))).toNat = 1
      from by decide]
    omega
  simp only [storeLimbInstrs, execBlock, execInstrRF, storeSem, loadSem, aluSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true,
    hx5, hx11, hX, hx5succ]
  refine ⟨?_, trivial, trivial, trivial, trivial⟩
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  congr 1
  bv_omega

/-- `getD` commutes with `drop`. -/
private theorem getD_drop (l : List (BitVec 8)) (m n : Nat) :
    (l.drop m).getD n 0 = l.getD (m + n) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- `src + ofNat a + ofNat b = src + ofNat (a + b)`. -/
private theorem add_ofNat_add (src : Word) (a b : Nat) :
    src + BitVec.ofNat 64 a + BitVec.ofNat 64 b = src + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- The inner-loop snapshot after the `setup` block: whichever outer
    iteration we are in, `x5 = k < 6` is the limb index, `x6` points at the
    MSB-first start of chunk `k`, the accumulator/counter are freshly seeded,
    and limbs `0..k-1` of the window already hold their chunk values. -/
private theorem snap_facts (src dst : Word) (inBytes orig : List (BitVec 8))
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (hsp : Stmt.sp ⟨src, inBytes⟩ ⟨dst, 48⟩ (Stmt.block "setup" setupInstrs)
      (fun rf ws A =>
        Stmt.sp ⟨src, inBytes⟩ ⟨dst, 48⟩ (Stmt.block "init" [.LI .x5 (0 : Word)])
            (blsgBeToLeFn src dst inBytes orig).pre rf ws A
          ∨ ∃ i < 5, outerInv src dst inBytes i rf ws A ∧ (Cond.bne .x5 .x6).holds rf)
      rf₀ ws₀ A₀) :
    ∃ k, k < 6 ∧ rf₀.get .x5 = BitVec.ofNat 64 k
      ∧ rf₀.get .x6 = src + BitVec.ofNat 64 (40 - 8 * k)
      ∧ rf₀.get .x28 = (0 : Word) ∧ rf₀.get .x29 = (8 : Word)
      ∧ rf₀.get .x10 = src ∧ rf₀.get .x11 = dst
      ∧ ws₀.length = 48 ∧ frameOk src dst
      ∧ (∀ m, m < k → wsDword ws₀ (8 * m) = BitVec.ofNat 64 (beChunk inBytes m)) := by
  obtain ⟨rfp, wsp, hwsp, hreach, rfl, rfl⟩ := hsp
  -- pre-setup facts: x5 = ofNat k (k<4), x10 = src, x11 = dst, ws length 32,
  -- frameOk, and limbs 0..k-1 already set.
  obtain ⟨k, hk, hpx5, hpx10, hpx11, hpwslen, hpfr, hplimbs⟩ :
      ∃ k, k < 6 ∧ rfp.get .x5 = BitVec.ofNat 64 k ∧ rfp.get .x10 = src
        ∧ rfp.get .x11 = dst ∧ ws₀.length = 48 ∧ frameOk src dst
        ∧ (∀ m, m < k → wsDword ws₀ (8 * m) = BitVec.ofNat 64 (beChunk inBytes m)) := by
    rcases hreach with hinit | ⟨i, hi, houter, hguard⟩
    · obtain ⟨rfi, wsi, hwsi, hpre, rfl, rfl⟩ := hinit
      obtain ⟨hx10, hx11, rfl, holen, hilen, hnws, hnwd, hdisj⟩ := hpre
      refine ⟨0, by omega, ?_, ?_, ?_, ?_, ⟨hnws, hnwd, hdisj⟩, by intro m hm; omega⟩
      all_goals simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10, hx11, holen]
      rfl
    · obtain ⟨hx5, hx6, hx10, hx11, hwslen, hfr, hlimbs⟩ := houter
      exact ⟨i + 1, by omega, hx5, hx10, hx11, hwslen, hfr, fun m hm => hlimbs m (by omega)⟩
  obtain ⟨he5, he6, he28, he29, he10, he11, he2⟩ :=
    setup_exec ⟨src, inBytes⟩ dst src rfp ws₀ k hk hpx5 hpx10
  exact ⟨k, hk, he5, he6, he28, he29, he10, he11 ▸ hpx11, he2 ▸ hpwslen, hpfr,
    fun m hm => he2 ▸ hplimbs m hm⟩

/-- Address side conditions of the inner body: its single `LBU` routes to the
    read-only source region (missing the disjoint window), aligned and in
    range; every other instruction is register-only. -/
private theorem inner_blockVCs (src dst : Word) (inBytes ws : List (BitVec 8))
    (rf : RegFile) (o : Nat) (ho : o < 48) (hilen : inBytes.length = 48)
    (hx6 : rf.get .x6 = src + BitVec.ofNat 64 o) (hws : ws.length = 48)
    (hfr : frameOk src dst) :
    blockVCs ⟨src, inBytes⟩ dst rf ws innerBodyInstrs := by
  have hmiss : ¬ inRw dst ws
      ((rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x6
        + signExtend12 (0 : BitVec 12)) 1 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hx6]
    simpa using src_miss src dst ws o ho hws hfr
  have haddr : ((rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x6
      + signExtend12 (0 : BitVec 12) - src).toNat = o := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hx6]
    have : ((src + BitVec.ofNat 64 o + 0 - src)).toNat = o := by bv_omega
    simpa using this
  simp only [innerBodyInstrs, blockVCs, loadSem, storeSem, execInstrRF, aluSem]
  rw [if_neg hmiss]
  refine ⟨trivial, ⟨?_, ?_⟩, trivial, trivial, trivial, trivial⟩
  · show 1 ∣ ((rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x6
      + signExtend12 (0 : BitVec 12) - src).toNat
    exact Nat.one_dvd _
  · show ((rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x6
      + signExtend12 (0 : BitVec 12) - src).toNat + 1 ≤ inBytes.length
    rw [haddr, hilen]; omega

/-- Address side conditions of the store-limb block: its single `SD` writes
    dword `k` of the disjoint writable window, aligned and in range. -/
private theorem storeLimb_blockVCs (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (k : Nat) (hk : k < 6)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 k) (hx11 : rf.get .x11 = dst)
    (hws : ws.length = 48) :
    blockVCs reg dst rf ws storeLimbInstrs := by
  have hX : (BitVec.ofNat 64 k <<< (3 : BitVec 6).toNat) = BitVec.ofNat 64 (8 * k) := by
    interval_cases k <;> decide
  have haddr : ((rf.get .x11 + rf.get .x5 <<< (3 : BitVec 6).toNat)
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * k := by
    rw [hx5, hX, hx11, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    have : ((dst + BitVec.ofNat 64 (8 * k) + 0 - dst)).toNat = 8 * k := by bv_omega
    simpa using this
  simp only [storeLimbInstrs, blockVCs, loadSem, storeSem, execInstrRF, aluSem,
    RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  refine ⟨trivial, trivial, ⟨?_, ?_⟩, trivial, trivial, trivial⟩
  · show inRw dst ws (rf.get .x11 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12)) 8
    unfold inRw; rw [haddr, hws]; omega
  · show 8 ∣ (rf.get .x11 + rf.get .x5 <<< (3 : BitVec 6).toNat
      + signExtend12 (0 : BitVec 12) - dst).toNat
    rw [haddr]; exact ⟨k, by ring⟩

/-- One inner-loop step, sealed behind an abstract-`rf` boundary so the
    kernel never unfolds the `execBlock ∘ shiftOr ∘ take_succ` composition
    inline (the `#9812`/`cfjzu.1` deep-recursion fix): from `innerInv i` with
    the guard holding, running the body once establishes `innerInv (i+1)`.
    The snapshot facts (`hs6`, `hkeq`, `hfr`) are supplied as hypotheses so
    this lemma's own term is bounded. -/
private theorem inner_step_engine (src dst : Word) (inBytes : List (BitVec 8))
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion) (i k : Nat)
    (hk : k < 6) (hi : i < 7) (hilen : inBytes.length = 48)
    (hwslen : ws.length = 48)
    (hs6 : rf₀.get .x6 = src + BitVec.ofNat 64 (40 - 8 * k))
    (hkeq : (rf₀.get .x5).toNat = k) (hfr : frameOk src dst)
    (hInv : innerInv src dst inBytes rf₀ ws₀ A₀ i rf ws A) :
    innerInv src dst inBytes rf₀ ws₀ A₀ (i + 1)
      (execBlock ⟨src, inBytes⟩ dst rf ws innerBodyInstrs).1 ws A := by
  obtain ⟨hp29, hp28, hp6, hp5, hp10, hp11, hpws, hpfr⟩ := hInv
  rw [hkeq] at hp28
  have hpx6 : rf.get .x6 = src + BitVec.ofNat 64 (40 - 8 * k + (i + 1)) := by
    rw [hp6, hs6, add_ofNat_add]
  obtain ⟨e28, e29, e6, e5, e10, e11, e2⟩ :=
    inner_body_exec src dst inBytes ws rf (40 - 8 * k + (i + 1)) (by omega) hpx6 hwslen hfr
  have hv : beBytesToNat ((inBytes.drop (40 - 8 * k)).take (i + 1)) < 2 ^ 56 := by
    have hlt := beBytesToNat_lt ((inBytes.drop (40 - 8 * k)).take (i + 1))
    have hl : ((inBytes.drop (40 - 8 * k)).take (i + 1)).length ≤ 7 := by
      rw [List.length_take]; omega
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  dsimp only [innerInv]
  rw [hkeq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hpws, hfr⟩
  · rw [e29, hp29, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
    have hi1 : 7 - i < 2 ^ 64 := by omega
    have hi2 : 7 - (i + 1) < 2 ^ 64 := by omega
    bv_omega
  · rw [e28, hp28,
      shiftOr_eq (beBytesToNat ((inBytes.drop (40 - 8 * k)).take (i + 1)))
        (inBytes.getD (40 - 8 * k + (i + 1)) 0) hv]
    congr 1
    rw [beBytesToNat_take_succ (inBytes.drop (40 - 8 * k)) (i + 1)
        (by rw [List.length_drop, hilen]; omega), getD_drop]
  · rw [e6, hp6, show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide,
      add_ofNat_add]
  · rw [e5, hp5]
  · rw [e10, hp10]
  · rw [e11, hp11]

/-- Reading a dword back at the offset it was just written. -/
private theorem wsDword_setBytes_self (ws : List (BitVec 8)) (v : Word) (j : Nat)
    (h : j + 8 ≤ ws.length) : wsDword (setBytes ws j (dwordBytes v)) j = v := by
  unfold wsDword
  have hs := setBytes_slot ws (dwordBytes v) j (by rw [length_dwordBytes]; exact h)
  rw [length_dwordBytes] at hs
  rw [hs, packBytes_dwordBytes]

/-- One outer-loop step, sealed behind an abstract-`rf` boundary: from the
    inner-loop exit (`innerInv 7` — `x28` holds the whole big-endian chunk `k`)
    and the earlier limbs `0..k-1`, the store-limb block writes limb `k` and
    establishes `outerInv k`. -/
private theorem outer_step_engine (src dst : Word) (inBytes : List (BitVec 8))
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (rf2 : RegFile) (ws2 : List (BitVec 8)) (A' : Assertion) (k : Nat)
    (hk : k < 6) (hs5 : rf₀.get .x5 = BitVec.ofNat 64 k) (hws0len : ws₀.length = 48)
    (hlimbs : ∀ m, m < k → wsDword ws₀ (8 * m) = BitVec.ofNat 64 (beChunk inBytes m))
    (hInv : innerInv src dst inBytes rf₀ ws₀ A₀ 7 rf2 ws2 A') :
    outerInv src dst inBytes k
      (execBlock ⟨src, inBytes⟩ dst rf2 ws2 storeLimbInstrs).1
      (execBlock ⟨src, inBytes⟩ dst rf2 ws2 storeLimbInstrs).2 A' := by
  obtain ⟨_, hp28, _, hp5, hp10, hp11, hpws, hfr⟩ := hInv
  have hkeq : (rf₀.get .x5).toNat = k := by rw [hs5, BitVec.toNat_ofNat]; omega
  rw [hkeq] at hp28
  have hx28 : rf2.get .x28 = BitVec.ofNat 64 (beChunk inBytes k) := by
    rw [hp28]; rfl
  have hx5 : rf2.get .x5 = BitVec.ofNat 64 k := by rw [hp5, hs5]
  have hws2 : ws2.length = 48 := by rw [hpws]; exact hws0len
  obtain ⟨se2, se5, se6, se10, se11⟩ :=
    storeLimb_exec ⟨src, inBytes⟩ dst rf2 ws2 k hk hx5 hp11
  dsimp only [outerInv]
  refine ⟨se5, se6, se10.trans hp10, se11, ?_, hfr, ?_⟩
  · rw [se2, length_setBytes]; exact hws2
  · intro m hm
    rw [se2]
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · rw [wsDword_setBytes_low (by omega), hpws]; exact hlimbs m hlt
    · subst heq
      rw [wsDword_setBytes_self ws2 (rf2.get .x28) (8 * m) (by omega), hx28]

theorem blsgBeToLeFn_spec (src dst : Word) (inBytes orig : List (BitVec 8))
    (hwf : (Region.mk src inBytes).wf) (hrww : RwRegion.wf ⟨dst, 48⟩)
    (hilen : inBytes.length = 48) (base : Word) :
    (blsgBeToLeFn src dst inBytes orig).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case blsgBeToLe.outer.body.inner.exhausted =>
    rintro rf₀ ws₀ A₀ hreach₀ rf ws A ⟨hx29, -, -, -, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx29]
    show (BitVec.ofNat 64 (7 - 7) : Word) = (0 : Word)
    decide
  case blsgBeToLe.outer.exhausted =>
    rintro rf ws A ⟨hx5, hx6, -, -, -, -, -⟩
    intro hc
    apply hc
    rw [hx5, hx6]
    decide
  case blsgBeToLe.outer.body.inner.body.body.mem =>
    rintro rf ws A hlen hreach
    rcases hreach with hsetup | ⟨rf₀, ws₀, A₀, hsnap, i, hi, hInv, hg⟩
    · obtain ⟨k, hk, _, hs6, _, _, _, _, _, hfr, _⟩ :=
        snap_facts src dst inBytes orig rf ws A hsetup
      exact inner_blockVCs src dst inBytes ws rf (40 - 8 * k) (by omega) hilen hs6 hlen hfr
    · obtain ⟨k, hk, _, hs6, _, _, _, _, _, _, _⟩ :=
        snap_facts src dst inBytes orig rf₀ ws₀ A₀ hsnap
      obtain ⟨_, _, hp6, _, _, _, _, hpfr⟩ := hInv
      have hx6 : rf.get .x6 = src + BitVec.ofNat 64 (40 - 8 * k + (i + 1)) := by
        rw [hp6, hs6, add_ofNat_add]
      exact inner_blockVCs src dst inBytes ws rf (40 - 8 * k + (i + 1)) (by omega) hilen hx6
        hlen hpfr
  case blsgBeToLe.outer.body.storeLimb.mem =>
    rintro rf ws A hlen ⟨rf₀, ws₀, A₀, hsnap, ⟨j, hj, hInv⟩, hng⟩
    obtain ⟨k, hk, hs5, _, _, _, _, _, _, _, _⟩ :=
      snap_facts src dst inBytes orig rf₀ ws₀ A₀ hsnap
    obtain ⟨_, _, _, hp5, _, hp11, _, _⟩ := hInv
    exact storeLimb_blockVCs ⟨src, inBytes⟩ dst rf ws k hk (by rw [hp5, hs5]) hp11 hlen
  case blsgBeToLe.post =>
    rintro rf ws A ⟨⟨i, hile, hx5, hx6, _, _, hwslen, _, hlimbs⟩, hng⟩
    have hi5 : i = 5 := by
      dsimp only [Cond.holds] at hng
      rw [hx5, hx6] at hng
      have heq : (BitVec.ofNat 64 (i + 1) : Word) = 6 := Decidable.of_not_not hng
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, show ((6 : Word)).toNat = 6 from by decide] at this
      omega
    subst hi5
    refine ⟨?_, hwslen⟩
    have l0 := hlimbs 0 (by omega)
    have l1 := hlimbs 1 (by omega)
    have l2 := hlimbs 2 (by omega)
    have l3 := hlimbs 3 (by omega)
    have l4 := hlimbs 4 (by omega)
    have l5 := hlimbs 5 (by omega)
    simp only [show (8 * 0 : Nat) = 0 from rfl, show (8 * 1 : Nat) = 8 from rfl,
      show (8 * 2 : Nat) = 16 from rfl, show (8 * 3 : Nat) = 24 from rfl,
      show (8 * 4 : Nat) = 32 from rfl, show (8 * 5 : Nat) = 40 from rfl] at l0 l1 l2 l3 l4 l5
    rw [l0, l1, l2, l3, l4, l5]
    exact leLimbs_chunks_eq_beBytesToNat inBytes hilen
  case blsgBeToLe.outer.body.inner.inv_init =>
    rintro rf₀ ws₀ A₀ hsnap rf' ws' A' ⟨rfp, wsp, hwsp, ⟨hrp, hwp, -⟩, rfl, rfl⟩
    subst hrp hwp
    obtain ⟨k, hk, hs5, hs6, hs28, hs29, hs10, hs11, hswslen, hfr, _⟩ :=
      snap_facts src dst inBytes orig rfp ws' A₀ hsnap
    obtain ⟨e28, e29, e6, e5, e10, e11, e2⟩ :=
      inner_body_exec src dst inBytes ws' rfp (40 - 8 * k) (by omega) hs6 hswslen hfr
    have hkeq : (rfp.get .x5).toNat = k := by rw [hs5, BitVec.toNat_ofNat]; omega
    show innerInv src dst inBytes rfp ws' A₀ 0
      (execBlock ⟨src, inBytes⟩ dst rfp ws' innerBodyInstrs).1 ws' A'
    dsimp only [innerInv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, hfr⟩
    · rw [e29, hs29]; decide
    · rw [e28, hs28, hkeq, show (0 : Word) = BitVec.ofNat 64 0 from rfl,
        shiftOr_eq 0 (inBytes.getD (40 - 8 * k) 0) (by norm_num),
        beBytesToNat_take_succ (inBytes.drop (40 - 8 * k)) 0
          (by rw [List.length_drop, hilen]; omega), getD_drop]
      simp [beBytesToNat]
    · rw [e6, hs6, show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide,
        add_ofNat_add]
    · rw [e5, hs5]
    · rw [e10, hs10]
    · rw [e11, hs11]
  case blsgBeToLe.outer.body.inner.inv_step =>
    rintro rf₀ ws₀ A₀ hsnap i hi rf' ws' A' ⟨rfp, wsp, hwsp, ⟨hInv, hg⟩, rfl, rfl⟩
    obtain ⟨k, hk, hs5, hs6, _, _, _, _, _, hfr, _⟩ :=
      snap_facts src dst inBytes orig rf₀ ws₀ A₀ hsnap
    have hkeq : (rf₀.get .x5).toNat = k := by rw [hs5, BitVec.toNat_ofNat]; omega
    exact inner_step_engine src dst inBytes rf₀ ws₀ A₀ rfp ws' A' i k hk hi hilen hwsp hs6
      hkeq hfr hInv
  case blsgBeToLe.outer.inv_init =>
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
    obtain ⟨hx10, -, hwseq, holen, -, -, -, -⟩ := hpre
    have hpre5 : rfpre.get .x5 = BitVec.ofNat 64 0 := by
      rw [hrfpre]
      simp [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    have hpre10 : rfpre.get .x10 = src := by
      rw [hrfpre]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
      exact hx10
    have hprelen : wspre.length = 48 := by
      rw [hwspre]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [hwseq]; exact holen
    obtain ⟨he5, -, -, -, -, -, he2⟩ :=
      setup_exec ⟨src, inBytes⟩ dst src rfpre wspre 0 (by omega) hpre5 hpre10
    subst hrf0 hws0
    exact outer_step_engine src dst inBytes _ _ A₀ rf2 ws2 A' 0 (by omega)
      he5 (he2 ▸ hprelen) (fun m hm => by omega) hInv
  case blsgBeToLe.outer.inv_step =>
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
    obtain ⟨rfpre, wspre, -, ⟨houter, -⟩, rfl, rfl⟩ := hsetup
    obtain ⟨ho5, -, ho10, -, howslen, -, holimbs⟩ := houter
    obtain ⟨he5, -, -, -, -, -, -⟩ :=
      setup_exec ⟨src, inBytes⟩ dst src rfpre ws₀ (i + 1) (by omega) ho5 ho10
    exact outer_step_engine src dst inBytes _ ws₀ A₀ rf2 ws2 A' (i + 1) (by omega) he5
      howslen (fun m hm => holimbs m (by omega)) hInv

end Bls12G1BeToLeSAsm

end EvmAsm.Codegen
