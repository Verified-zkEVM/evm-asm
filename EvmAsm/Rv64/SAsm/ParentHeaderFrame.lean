/-
  EvmAsm.Rv64.SAsm.ParentHeaderFrame

  **The first real sp-frame guest routine verified through the ABI-frame
  construct** (bead evm-asm-ffziu): the re-emitted, verified drop-in for
  `parent_header_matches_witness_first`
  (`EvmAsm/Codegen/Programs/BlockHashPredicates.lean`).

  The routine is a probe-only leaf (no cross-call): given
    a0 = parent_header_rlp ptr, a1 = its length,
    a2 = witness.headers section ptr, a3 = section length,
    a4 = is_match output cell,
  it decodes the section's SSZ offset table and compares
  `witness.headers[0]` against `parent_header_rlp` byte-for-byte, returning
    a0 = 1 (section empty, incl. the N = 0 offset-table case), is_match = 0
    a0 = 0 otherwise, is_match = 1 iff lengths match AND every byte agrees.

  ## The re-emission (byte-changed, functionally identical)

  Two deliberate reshapes make the hand-written original verifiable at the
  `cpsTripleWithin` level, with **identical observable behavior**:

  * The original's `lwu` offset-table reads are misaligned whenever the
    section pointer is not 4-aligned (at the real callsite the section starts
    at `0x40000018 + parent_len`); ziskemu tolerates this (Zicclsm) but the
    verified RV64 model does not.  The re-emission byte-reconstructs the two
    u32-LE offset words with `lbu`+`slli`+`add` (`bytesRegion_lbu_within`).
  * The original's byte loop early-exits on the first mismatch; the
    re-emission accumulates a branch-free match flag over ALL `len` bytes —
    the exact countdown shape of the verified memcmp core
    (`ParentHeaderMemcmp.memcmpLoop_spec`).  Both loops read only within the
    guarded element span and write nothing, so short-circuiting has zero
    observable effect: same outputs on every input.

  ## Structure of the verification

  * `phmwBody` — the 65-instruction single-exit body: every branch
    (empty / N = 0 / single-vs-multi element / length mismatch / match)
    reconverges to the body's fall-through exit into the epilogue.
  * `phmwProg = abiFrameProg (-64) 64 phmwFrame phmwBody` — the whole
    84-instruction routine; `#guard`/`rfl` tie it to the spelled-out
    `phmwProgList` (and `BlockHashPredicates.lean` ties the emitted Program
    to `phmwProgList` by `rfl`, so verified == emitted).
  * `phmwCore_spec` — the unified single-exit body triple with the genuine
    disjunctive post (`phmwStatus` / `phmwIsMatch` below), proven by case
    analysis over the input classification; the byte loop is discharged by
    the verified memcmp core, lifted into the routine's CodeReq
    (the routine is anchored at `0xF18` so the loop header lands exactly on
    the memcmp core's `0x1000` anchor).
  * `phmwFrame_spec` — the whole-routine ABI contract via `abiFrame_spec`:
    `sp`, `ra`, and all seven saved `s`-registers restored to entry.

  Strictly additive: `cpsTripleWithin` only; no `Ast`/`Vc`/`StmtSound*`/
  `blockOk` changes.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.ParentHeaderMemcmp
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm
namespace ParentHeaderFrame

open EvmAsm.Rv64.Tactics

/-- pcFree discharge for chains that may contain `bytesRegion` atoms. -/
local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact bytesRegion_pcFree _ _)

-- ============================================================================
-- The re-emitted routine.
-- ============================================================================

/-- The 8-slot frame: `ra` at 0, then `s0 s1 s18 s19 s20 s21 s22` — exactly
    the original routine's frame. -/
def phmwFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
   (.x21, 48), (.x22, 56)]

/-- The single-exit body (65 instructions).  Register plan mirrors the
    original: `s0/s1` = parent ptr/len, `s18/s19` = section ptr/len,
    `s20` = out ptr, `s21/s22` = element-0 start/end; the memcmp countdown
    runs in `t`-registers (`x28` = counter, `x5` = match flag, `x6`/`x7` =
    cursors) in exactly the shape `ParentHeaderMemcmp.loopProgList` verifies
    (body indices 49–58). -/
def phmwBody : List Instr :=
  [ .MV .x8 .x10,                     -- 0:  s0 := parent ptr
    .MV .x9 .x11,                     -- 1:  s1 := parent len
    .MV .x18 .x12,                    -- 2:  s18 := section ptr
    .MV .x19 .x13,                    -- 3:  s19 := section len
    .MV .x20 .x14,                    -- 4:  s20 := out ptr
    .SD .x20 .x0 (0 : BitVec 12),     -- 5:  is_match := 0
    .BEQ .x19 .x0 (232 : BitVec 13),  -- 6:  empty section → 64
    .MV .x31 .x18,                    -- 7:  cursor := section ptr
    .LBU .x5 .x31 (0 : BitVec 12),    -- 8:  offset0 byte 0
    .ADDI .x31 .x31 (1 : BitVec 12),  -- 9
    .LBU .x6 .x31 (0 : BitVec 12),    -- 10: offset0 byte 1
    .ADDI .x31 .x31 (1 : BitVec 12),  -- 11
    .LBU .x7 .x31 (0 : BitVec 12),    -- 12: offset0 byte 2
    .ADDI .x31 .x31 (1 : BitVec 12),  -- 13
    .LBU .x28 .x31 (0 : BitVec 12),   -- 14: offset0 byte 3
    .SLLI .x6 .x6 (8 : BitVec 6),     -- 15
    .SLLI .x7 .x7 (16 : BitVec 6),    -- 16
    .SLLI .x28 .x28 (24 : BitVec 6),  -- 17
    .ADD .x5 .x5 .x6,                 -- 18
    .ADD .x5 .x5 .x7,                 -- 19
    .ADD .x5 .x5 .x28,                -- 20: x5 = offset0 (u32 LE)
    .SRLI .x29 .x5 (2 : BitVec 6),    -- 21: x29 = N = offset0 >> 2
    .BEQ .x29 .x0 (168 : BitVec 13),  -- 22: N = 0 → 64 (treated as empty)
    .ADD .x21 .x18 .x5,               -- 23: s21 = el0_start
    .LI .x30 (1 : Word),              -- 24
    .BLTU .x30 .x29 (12 : BitVec 13), -- 25: N > 1 → 28
    .ADD .x22 .x18 .x19,              -- 26: s22 = el0_end = section end
    .JAL .x0 (64 : BitVec 21),        -- 27: → 43 (join)
    .ADDI .x31 .x18 (4 : BitVec 12),  -- 28: cursor := &offset1
    .LBU .x5 .x31 (0 : BitVec 12),    -- 29: offset1 byte 0
    .ADDI .x31 .x31 (1 : BitVec 12),  -- 30
    .LBU .x6 .x31 (0 : BitVec 12),    -- 31: offset1 byte 1
    .ADDI .x31 .x31 (1 : BitVec 12),  -- 32
    .LBU .x7 .x31 (0 : BitVec 12),    -- 33: offset1 byte 2
    .ADDI .x31 .x31 (1 : BitVec 12),  -- 34
    .LBU .x28 .x31 (0 : BitVec 12),   -- 35: offset1 byte 3
    .SLLI .x6 .x6 (8 : BitVec 6),     -- 36
    .SLLI .x7 .x7 (16 : BitVec 6),    -- 37
    .SLLI .x28 .x28 (24 : BitVec 6),  -- 38
    .ADD .x5 .x5 .x6,                 -- 39
    .ADD .x5 .x5 .x7,                 -- 40
    .ADD .x5 .x5 .x28,                -- 41: x5 = offset1 (u32 LE)
    .ADD .x22 .x18 .x5,               -- 42: s22 = el0_end
    .SUB .x5 .x22 .x21,               -- 43: x5 = el0_len   (join)
    .BNE .x5 .x9 (72 : BitVec 13),    -- 44: length mismatch → 62
    .MV .x6 .x8,                      -- 45: p1 := parent
    .MV .x7 .x21,                     -- 46: p2 := el0_start
    .MV .x28 .x9,                     -- 47: ctr := len
    .LI .x5 (1 : Word),               -- 48: matchFlag := 1
    .BEQ .x28 .x0 (40 : BitVec 13),   -- 49: loop hdr (== loopProgList)
    .LBU .x29 .x6 (0 : BitVec 12),    -- 50
    .LBU .x30 .x7 (0 : BitVec 12),    -- 51
    .XOR .x29 .x29 .x30,              -- 52
    .SLTIU .x31 .x29 (1 : BitVec 12), -- 53
    .AND .x5 .x5 .x31,                -- 54
    .ADDI .x6 .x6 (1 : BitVec 12),    -- 55
    .ADDI .x7 .x7 (1 : BitVec 12),    -- 56
    .ADDI .x28 .x28 (-1 : BitVec 12), -- 57
    .JAL .x0 (-36 : BitVec 21),       -- 58: back-edge → 49
    .SD .x20 .x5 (0 : BitVec 12),     -- 59: is_match := matchFlag
    .LI .x10 (0 : Word),              -- 60: status := 0
    .JAL .x0 (16 : BitVec 21),        -- 61: → 65 (body exit)
    .LI .x10 (0 : Word),              -- 62: status := 0 (mismatch)
    .JAL .x0 (8 : BitVec 21),         -- 63: → 65 (body exit)
    .LI .x10 (1 : Word) ]             -- 64: status := 1 (empty / N = 0)

/-- The whole routine as the ABI-frame flatten. -/
def phmwProg : List Instr :=
  abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) phmwFrame phmwBody

/-- The same 84 instructions spelled out (the emit source, and the routine
    `CodeReq`). -/
def phmwProgList : List Instr :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12) ]
  ++ phmwBody ++
  [ .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

-- Byte-transparency: the ABI-frame flatten is exactly the spelled-out list.
#guard phmwProg = phmwProgList
#guard phmwProgList.length = 84

/-- Byte-transparency as a kernel-checked `rfl`. -/
theorem phmwProg_eq : phmwProg = phmwProgList := rfl

/-- The routine `CodeReq`, anchored at `0xF18` so that the memcmp loop header
    (routine index 58) lands exactly at the verified core's `0x1000` anchor:
    `0xF18 + 4·58 = 0x1000`. -/
def phmwCr : CodeReq := CodeReq.ofProg 0xF18 phmwProgList

/-- Code-membership: instruction `idx` of the routine sits in `phmwCr`. -/
private theorem memAt (idx : Nat) (addr : Word) (instr : Instr)
    (hk : idx < phmwProgList.length) (hbound : 4 * phmwProgList.length < 2 ^ 64)
    (haddr : addr = (0xF18 : Word) + BitVec.ofNat 64 (4 * idx))
    (hget : phmwProgList.get ⟨idx, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → phmwCr a = some i := by
  have m := CodeReq.ofProg_lookup_addr (0xF18 : Word) phmwProgList idx addr hk hbound haddr
  rw [hget] at m
  exact CodeReq.singleton_mono m

/-- Lift a segment triple proven over its own contiguous `ofProg` slice into
    the routine `CodeReq`. -/
private theorem liftSeg {n : Nat} {A B : Word} {seg : List Instr} {P Q : Assertion}
    (idx : Nat)
    (haddr : A = (0xF18 : Word) + BitVec.ofNat 64 (4 * idx))
    (hslice : (phmwProgList.drop idx).take seg.length = seg)
    (hrange : idx + seg.length ≤ phmwProgList.length)
    (h : cpsTripleWithin n A B (CodeReq.ofProg A seg) P Q) :
    cpsTripleWithin n A B phmwCr P Q :=
  cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub (0xF18 : Word) A phmwProgList seg idx haddr hslice hrange
      (by decide)) h

/-- The verified memcmp loop core's `CodeReq` is a slice of the routine
    (routine indices 58–67 at `0x1000`). -/
private theorem loopSub :
    ∀ a i, ParentHeaderMemcmp.loopCr a = some i → phmwCr a = some i :=
  CodeReq.ofProg_mono_sub (0xF18 : Word) (0x1000 : Word) phmwProgList
    ParentHeaderMemcmp.loopProgList 58 (by decide) (by rfl) (by decide) (by decide)

-- ============================================================================
-- Arithmetic helpers.
-- ============================================================================

private theorem ofNat_add' (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem ofNat_succ_addr (b : Word) (p : Nat) :
    (b + BitVec.ofNat 64 p) + signExtend12 (1 : BitVec 12)
      = b + BitVec.ofNat 64 (p + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide,
      BitVec.add_assoc, ofNat_add']

/-- `x + sext12 0 = x`. -/
private theorem add_sext0 (x : Word) : x + signExtend12 (0 : BitVec 12) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (signExtend12 (0 : BitVec 12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

/-- `x + ofNat 0 = x`. -/
private theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt x.isLt]

/-- Fold `base + ofNat a + ofNat b` into `base + ofNat (a + b)`. -/
private theorem addr_fold (b : Word) (i j : Nat) :
    (b + BitVec.ofNat 64 i) + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, ofNat_add']

private theorem ofNat_inj' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]

private theorem ofNat_ne_zero {a : Nat} (h0 : a ≠ 0) (hlt : a < 2 ^ 64) :
    BitVec.ofNat 64 a ≠ (0 : Word) := by
  intro h
  have h2 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h2
  have hz : ((0 : Word).toNat) = 0 := by decide
  omega

/-- `srli 2` on an in-range `ofNat` computes division by 4. -/
private theorem ofNat_shr2 (v : Nat) (h : v < 2 ^ 64) :
    (BitVec.ofNat 64 v) >>> 2 = BitVec.ofNat 64 (v / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.shiftRight_eq_div_pow]

/-- Subtracting in-range `ofNat`s (no wrap when `b ≤ a`). -/
private theorem ofNat_sub_ofNat {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]
  omega

/-- `(base + x) - (base + y) = x - y` (pure wrap-around arithmetic). -/
private theorem sub_common_base (base x y : Word) :
    (base + x) - (base + y) = x - y := by
  bv_omega

/-- `BitVec.ult 1 (ofNat n)` decides `1 < n` for in-range `n`. -/
private theorem ult_one_ofNat {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ult (1 : Word) (BitVec.ofNat 64 n) = true) ↔ 1 < n := by
  rw [BitVec.ult]
  simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
  rw [Nat.mod_eq_of_lt h]
  have h1 : (1 : Word).toNat = 1 := by decide
  omega

-- ============================================================================
-- The u32-LE offset word.
-- ============================================================================

/-- The little-endian u32 at byte index `i` of `l`, as a `Nat`. -/
def u32le (l : List (BitVec 8)) (i : Nat) : Nat :=
  (l.getD i 0).toNat + 2 ^ 8 * (l.getD (i + 1) 0).toNat
    + 2 ^ 16 * (l.getD (i + 2) 0).toNat + 2 ^ 24 * (l.getD (i + 3) 0).toNat

theorem u32le_lt (l : List (BitVec 8)) (i : Nat) : u32le l i < 2 ^ 32 := by
  have h0 := (l.getD i 0).isLt
  have h1 := (l.getD (i + 1) 0).isLt
  have h2 := (l.getD (i + 2) 0).isLt
  have h3 := (l.getD (i + 3) 0).isLt
  unfold u32le
  omega

/-- The emitted `lbu`+`slli`+`add` fold reconstructs the u32-LE word. -/
private theorem u32le_fold (b0 b1 b2 b3 : BitVec 8) :
    ((b0.zeroExtend 64 + b1.zeroExtend 64 <<< 8) + b2.zeroExtend 64 <<< 16)
        + b3.zeroExtend 64 <<< 24
      = BitVec.ofNat 64 (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat
          + 2 ^ 24 * b3.toNat) := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

-- ============================================================================
-- The genuine disjunctive semantics (the unified post's spec functions).
-- ============================================================================

/-- Element count `N` of the SSZ offset table: first offset `>> 2`. -/
def phmwN (sb : List (BitVec 8)) (secOfs : Nat) : Nat := u32le sb secOfs / 4

/-- Byte offset (within the section) of element 0's END: the section end for a
    single-element table, else the second offset. -/
def phmwElEnd (sb : List (BitVec 8)) (secOfs sectionLen : Nat) : Nat :=
  if phmwN sb secOfs = 1 then sectionLen else u32le sb (secOfs + 4)

/-- Element 0's byte length. -/
def phmwElLen (sb : List (BitVec 8)) (secOfs sectionLen : Nat) : Nat :=
  phmwElEnd sb secOfs sectionLen - u32le sb secOfs

/-- `status` (`a0` on exit): `1` iff the witness-headers section is empty
    (including the `N = 0` offset-table case, exactly as the original routine
    branches), else `0`. -/
def phmwStatus (sb : List (BitVec 8)) (secOfs sectionLen : Nat) : Word :=
  if sectionLen = 0 ∨ phmwN sb secOfs = 0 then 1 else 0

/-- `is_match` (the dword at `[a4]` on exit): `1` iff the section is non-empty
    (`N ≥ 1`), element 0's length equals `parent_header_rlp`'s, and every byte
    agrees; else `0`.  The genuine, unweakened predicate. -/
def phmwIsMatch (pb sb : List (BitVec 8)) (secOfs sectionLen : Nat) : Word :=
  if sectionLen ≠ 0 ∧ phmwN sb secOfs ≠ 0
      ∧ phmwElLen sb secOfs sectionLen = pb.length
      ∧ (∀ k, k < pb.length →
          pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0)
  then 1 else 0

-- ============================================================================
-- Straight-line segments (each proven over its own slice, lifted into the
-- routine CodeReq via `liftSeg`).
-- ============================================================================

/-- The contiguous instruction slices of the body, named so segment triples
    can be stated over their own `ofProg` and lifted via `liftSeg`. -/
private def seg1Prog : List Instr :=
  [ .MV .x8 .x10, .MV .x9 .x11, .MV .x18 .x12, .MV .x19 .x13, .MV .x20 .x14,
    .SD .x20 .x0 (0 : BitVec 12) ]
private def seg2Prog : List Instr :=
  [ .MV .x31 .x18,
    .LBU .x5 .x31 (0 : BitVec 12), .ADDI .x31 .x31 (1 : BitVec 12),
    .LBU .x6 .x31 (0 : BitVec 12), .ADDI .x31 .x31 (1 : BitVec 12),
    .LBU .x7 .x31 (0 : BitVec 12), .ADDI .x31 .x31 (1 : BitVec 12),
    .LBU .x28 .x31 (0 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6), .SLLI .x7 .x7 (16 : BitVec 6),
    .SLLI .x28 .x28 (24 : BitVec 6),
    .ADD .x5 .x5 .x6, .ADD .x5 .x5 .x7, .ADD .x5 .x5 .x28,
    .SRLI .x29 .x5 (2 : BitVec 6) ]
private def seg3Prog : List Instr :=
  [ .ADD .x21 .x18 .x5, .LI .x30 (1 : Word) ]
private def seg4n1Prog : List Instr :=
  [ .ADD .x22 .x18 .x19, .JAL .x0 (64 : BitVec 21) ]
private def seg4n2Prog : List Instr :=
  [ .ADDI .x31 .x18 (4 : BitVec 12),
    .LBU .x5 .x31 (0 : BitVec 12), .ADDI .x31 .x31 (1 : BitVec 12),
    .LBU .x6 .x31 (0 : BitVec 12), .ADDI .x31 .x31 (1 : BitVec 12),
    .LBU .x7 .x31 (0 : BitVec 12), .ADDI .x31 .x31 (1 : BitVec 12),
    .LBU .x28 .x31 (0 : BitVec 12),
    .SLLI .x6 .x6 (8 : BitVec 6), .SLLI .x7 .x7 (16 : BitVec 6),
    .SLLI .x28 .x28 (24 : BitVec 6),
    .ADD .x5 .x5 .x6, .ADD .x5 .x5 .x7, .ADD .x5 .x5 .x28,
    .ADD .x22 .x18 .x5 ]
private def seg5Prog : List Instr := [ .SUB .x5 .x22 .x21 ]
private def seg6Prog : List Instr :=
  [ .MV .x6 .x8, .MV .x7 .x21, .MV .x28 .x9, .LI .x5 (1 : Word) ]
private def seg7Prog : List Instr :=
  [ .SD .x20 .x5 (0 : BitVec 12), .LI .x10 (0 : Word), .JAL .x0 (16 : BitVec 21) ]
private def seg8Prog : List Instr :=
  [ .LI .x10 (0 : Word), .JAL .x0 (8 : BitVec 21) ]
private def seg9Prog : List Instr := [ .LI .x10 (1 : Word) ]

/-- Body 0–5 (`0xF3C → 0xF54`): move the five arguments into the saved
    `s`-registers and zero the `is_match` cell. -/
private theorem seg1_spec (parentBase lenW secPtrW secLenW outPtr oldOut : Word)
    (arb8 arb9 arb18 arb19 arb20 : Word) :
    cpsTripleWithin 6 (0xF3C : Word) (0xF54 : Word) phmwCr
      ((.x10 ↦ᵣ parentBase) ** (.x8 ↦ᵣ arb8)
        ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ arb9)
        ** (.x12 ↦ᵣ secPtrW) ** (.x18 ↦ᵣ arb18)
        ** (.x13 ↦ᵣ secLenW) ** (.x19 ↦ᵣ arb19)
        ** (.x14 ↦ᵣ outPtr) ** (.x20 ↦ᵣ arb20)
        ** (outPtr ↦ₘ oldOut))
      ((.x10 ↦ᵣ parentBase) ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ lenW) ** (.x9 ↦ᵣ lenW)
        ** (.x12 ↦ᵣ secPtrW) ** (.x18 ↦ᵣ secPtrW)
        ** (.x13 ↦ᵣ secLenW) ** (.x19 ↦ᵣ secLenW)
        ** (.x14 ↦ᵣ outPtr) ** (.x20 ↦ᵣ outPtr)
        ** (outPtr ↦ₘ (0 : Word))) := by
  refine liftSeg (seg := seg1Prog) 9 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 6 (0xF3C : Word) (0xF54 : Word) (CodeReq.ofProg (0xF3C : Word) seg1Prog) _ _
  simp only [seg1Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have h0 := mv_spec_gen_within .x8 .x10 parentBase arb8 (0xF3C : Word) (by decide)
  have h1 := mv_spec_gen_within .x9 .x11 lenW arb9 (0xF40 : Word) (by decide)
  have h2 := mv_spec_gen_within .x18 .x12 secPtrW arb18 (0xF44 : Word) (by decide)
  have h3 := mv_spec_gen_within .x19 .x13 secLenW arb19 (0xF48 : Word) (by decide)
  have h4 := mv_spec_gen_within .x20 .x14 outPtr arb20 (0xF4C : Word) (by decide)
  have h5 := sd_x0_spec_gen_within .x20 outPtr oldOut (0 : BitVec 12) (0xF50 : Word)
  rw [add_sext0] at h5
  runBlock h0 h1 h2 h3 h4 h5

/-- Body 7–21 (`0xF58 → 0xF94`): byte-reconstruct the first u32-LE offset word
    into `x5` and compute `N = offset0 >> 2` into `x29`. -/
private theorem seg2_spec (secBase : Word) (sb : List (BitVec 8)) (secOfs : Nat)
    (v31 v5 v6 v7 v28 v29 : Word)
    (hj : secOfs + 4 ≤ sb.length) (halignS : secBase.toNat % 8 = 0)
    (hsover : secBase.toNat + sb.length < 2 ^ 64)
    (hsvalid : ∀ i, i < sb.length →
      isValidByteAccess (secBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 15 (0xF58 : Word) (0xF94 : Word) phmwCr
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs)) ** (.x31 ↦ᵣ v31)
        ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
        ** (.x29 ↦ᵣ v29) ** bytesRegion secBase sb)
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x29 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs / 4))
        ** bytesRegion secBase sb) := by
  have hb0 : secOfs < sb.length := by omega
  have hb1 : secOfs + 1 < sb.length := by omega
  have hb2 : secOfs + 2 < sb.length := by omega
  have hb3 : secOfs + 3 < sb.length := by omega
  refine liftSeg (seg := seg2Prog) 16 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 15 (0xF58 : Word) (0xF94 : Word) (CodeReq.ofProg (0xF58 : Word) seg2Prog) _ _
  simp only [seg2Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hmv := mv_spec_gen_within .x31 .x18 (secBase + BitVec.ofNat 64 secOfs) v31
    (0xF58 : Word) (by decide)
  have hlbu0 := bytesRegion_lbu_within .x5 .x31 secBase v5 (0xF5C : Word) sb secOfs
    (by decide) halignS hb0 (by omega) (hsvalid secOfs hb0)
  have haddi0 := addi_spec_gen_same_within .x31 (secBase + BitVec.ofNat 64 secOfs)
    (1 : BitVec 12) (0xF60 : Word) (by decide)
  rw [ofNat_succ_addr] at haddi0
  have hlbu1 := bytesRegion_lbu_within .x6 .x31 secBase v6 (0xF64 : Word) sb (secOfs + 1)
    (by decide) halignS hb1 (by omega) (hsvalid _ hb1)
  have haddi1 := addi_spec_gen_same_within .x31 (secBase + BitVec.ofNat 64 (secOfs + 1))
    (1 : BitVec 12) (0xF68 : Word) (by decide)
  rw [ofNat_succ_addr] at haddi1
  have hlbu2 := bytesRegion_lbu_within .x7 .x31 secBase v7 (0xF6C : Word) sb (secOfs + 2)
    (by decide) halignS hb2 (by omega) (hsvalid _ hb2)
  have haddi2 := addi_spec_gen_same_within .x31 (secBase + BitVec.ofNat 64 (secOfs + 2))
    (1 : BitVec 12) (0xF70 : Word) (by decide)
  rw [ofNat_succ_addr] at haddi2
  have hlbu3 := bytesRegion_lbu_within .x28 .x31 secBase v28 (0xF74 : Word) sb (secOfs + 3)
    (by decide) halignS hb3 (by omega) (hsvalid _ hb3)
  have hslli1 := slli_spec_gen_same_within .x6 ((sb[secOfs + 1]'hb1).zeroExtend 64)
    (8 : BitVec 6) (0xF78 : Word) (by decide)
  have hslli2 := slli_spec_gen_same_within .x7 ((sb[secOfs + 2]'hb2).zeroExtend 64)
    (16 : BitVec 6) (0xF7C : Word) (by decide)
  have hslli3 := slli_spec_gen_same_within .x28 ((sb[secOfs + 3]'hb3).zeroExtend 64)
    (24 : BitVec 6) (0xF80 : Word) (by decide)
  rw [show ((8 : BitVec 6)).toNat = 8 from rfl] at hslli1
  rw [show ((16 : BitVec 6)).toNat = 16 from rfl] at hslli2
  rw [show ((24 : BitVec 6)).toNat = 24 from rfl] at hslli3
  have hadd1 := add_spec_gen_rd_eq_rs1_within .x5 .x6
    ((sb[secOfs]'hb0).zeroExtend 64) (((sb[secOfs + 1]'hb1).zeroExtend 64) <<< 8)
    (0xF84 : Word) (by decide)
  have hadd2 := add_spec_gen_rd_eq_rs1_within .x5 .x7
    ((sb[secOfs]'hb0).zeroExtend 64 + ((sb[secOfs + 1]'hb1).zeroExtend 64) <<< 8)
    (((sb[secOfs + 2]'hb2).zeroExtend 64) <<< 16) (0xF88 : Word) (by decide)
  have hadd3 := add_spec_gen_rd_eq_rs1_within .x5 .x28
    (((sb[secOfs]'hb0).zeroExtend 64 + ((sb[secOfs + 1]'hb1).zeroExtend 64) <<< 8)
      + ((sb[secOfs + 2]'hb2).zeroExtend 64) <<< 16)
    (((sb[secOfs + 3]'hb3).zeroExtend 64) <<< 24) (0xF8C : Word) (by decide)
  -- The folded u32-LE value.
  have hfold :
      (((sb[secOfs]'hb0).zeroExtend 64 + ((sb[secOfs + 1]'hb1).zeroExtend 64) <<< 8)
          + ((sb[secOfs + 2]'hb2).zeroExtend 64) <<< 16)
          + ((sb[secOfs + 3]'hb3).zeroExtend 64) <<< 24
        = BitVec.ofNat 64 (u32le sb secOfs) := by
    rw [u32le_fold]
    unfold u32le
    rw [List.getElem_eq_getD (l := sb) (i := secOfs) 0,
        List.getElem_eq_getD (l := sb) (i := secOfs + 1) 0,
        List.getElem_eq_getD (l := sb) (i := secOfs + 2) 0,
        List.getElem_eq_getD (l := sb) (i := secOfs + 3) 0]
  rw [hfold] at hadd3
  have hsrli := srli_spec_gen_within .x29 .x5 v29 (BitVec.ofNat 64 (u32le sb secOfs))
    (2 : BitVec 6) (0xF90 : Word) (by decide)
  rw [show ((2 : BitVec 6)).toNat = 2 from rfl,
      ofNat_shr2 _ (lt_trans (u32le_lt sb secOfs) (by norm_num))] at hsrli
  refine cpsTripleWithin_weaken (fun _ h => h)
    (Q := (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
      ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
      ** (.x6 ↦ᵣ (((sb[secOfs + 1]'hb1).zeroExtend 64) <<< 8))
      ** (.x7 ↦ᵣ (((sb[secOfs + 2]'hb2).zeroExtend 64) <<< 16))
      ** (.x28 ↦ᵣ (((sb[secOfs + 3]'hb3).zeroExtend 64) <<< 24))
      ** (.x29 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs / 4))
      ** bytesRegion secBase sb)
    (fun h hq => ?_)
    (by runBlock hmv hlbu0 haddi0 hlbu1 haddi1 hlbu2 haddi2 hlbu3 hslli1 hslli2 hslli3
        hadd1 hadd2 hadd3 hsrli)
  rw [List.getElem_eq_getD (l := sb) (i := secOfs + 1),
      List.getElem_eq_getD (l := sb) (i := secOfs + 2),
      List.getElem_eq_getD (l := sb) (i := secOfs + 3)] at hq
  exact hq
  all_goals exact bytesRegion_pcFree _ _

/-- Body 23–24 (`0xF98 → 0xFA0`): compute element 0's start pointer into
    `s21`, load the constant `1` for the `N > 1` test. -/
private theorem seg3_spec (secBase : Word) (sb : List (BitVec 8)) (secOfs : Nat)
    (arb21 v30 : Word) :
    cpsTripleWithin 2 (0xF98 : Word) (0xFA0 : Word) phmwCr
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x21 ↦ᵣ arb21) ** (.x30 ↦ᵣ v30))
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x30 ↦ᵣ (1 : Word))) := by
  refine liftSeg (seg := seg3Prog) 32 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 2 (0xF98 : Word) (0xFA0 : Word) (CodeReq.ofProg (0xF98 : Word) seg3Prog) _ _
  simp only [seg3Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hadd := add_spec_gen_within .x21 .x18 .x5 (secBase + BitVec.ofNat 64 secOfs)
    (BitVec.ofNat 64 (u32le sb secOfs)) arb21 (0xF98 : Word) (by decide)
  rw [addr_fold] at hadd
  have hli := li_spec_gen_within .x30 v30 (1 : Word) (0xF9C : Word) (by decide)
  runBlock hadd hli

/-- Body 26–27 (`0xFA4 → 0xFE8`), the `N = 1` route: element 0 ends at the
    section end; jump to the join. -/
private theorem seg4n1_spec (secBase : Word) (secOfs sectionLen : Nat)
    (arb22 : Word) :
    cpsTripleWithin 2 (0xFA4 : Word) (0xFE8 : Word) phmwCr
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x22 ↦ᵣ arb22))
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + sectionLen)))) := by
  refine liftSeg (seg := seg4n1Prog) 35 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 2 (0xFA4 : Word) (0xFE8 : Word) (CodeReq.ofProg (0xFA4 : Word) seg4n1Prog) _ _
  simp only [seg4n1Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hadd := add_spec_gen_within .x22 .x18 .x19 (secBase + BitVec.ofNat 64 secOfs)
    (BitVec.ofNat 64 sectionLen) arb22 (0xFA4 : Word) (by decide)
  rw [addr_fold] at hadd
  have hjal := jal_x0_spec_gen_within (64 : BitVec 21) (0xFA8 : Word)
  rw [show (0xFA8 : Word) + signExtend21 (64 : BitVec 21) = (0xFE8 : Word) from by decide]
    at hjal
  runBlock hadd hjal

/-- Body 28–42 (`0xFAC → 0xFE8`), the `N > 1` route: byte-reconstruct the
    second u32-LE offset word and compute element 0's end pointer into `s22`. -/
private theorem seg4n2_spec (secBase : Word) (sb : List (BitVec 8)) (secOfs : Nat)
    (v31 v5 v6 v7 v28 arb22 : Word)
    (hj : secOfs + 8 ≤ sb.length) (halignS : secBase.toNat % 8 = 0)
    (hsover : secBase.toNat + sb.length < 2 ^ 64)
    (hsvalid : ∀ i, i < sb.length →
      isValidByteAccess (secBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 15 (0xFAC : Word) (0xFE8 : Word) phmwCr
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs)) ** (.x31 ↦ᵣ v31)
        ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
        ** (.x22 ↦ᵣ arb22) ** bytesRegion secBase sb)
      ((.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 4 + 3)))
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb (secOfs + 4)))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 4 + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 4 + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 4 + 3) 0).zeroExtend 64) <<< 24))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb (secOfs + 4))))
        ** bytesRegion secBase sb) := by
  have hb0 : secOfs + 4 < sb.length := by omega
  have hb1 : secOfs + 4 + 1 < sb.length := by omega
  have hb2 : secOfs + 4 + 2 < sb.length := by omega
  have hb3 : secOfs + 4 + 3 < sb.length := by omega
  refine liftSeg (seg := seg4n2Prog) 37 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 15 (0xFAC : Word) (0xFE8 : Word) (CodeReq.ofProg (0xFAC : Word) seg4n2Prog) _ _
  simp only [seg4n2Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have haddi := addi_spec_gen_within .x31 .x18 v31 (secBase + BitVec.ofNat 64 secOfs)
    (4 : BitVec 12) (0xFAC : Word) (by decide)
  rw [show signExtend12 (4 : BitVec 12) = BitVec.ofNat 64 4 from by decide,
      addr_fold] at haddi
  have hlbu0 := bytesRegion_lbu_within .x5 .x31 secBase v5 (0xFB0 : Word) sb (secOfs + 4)
    (by decide) halignS hb0 (by omega) (hsvalid _ hb0)
  have haddi0 := addi_spec_gen_same_within .x31 (secBase + BitVec.ofNat 64 (secOfs + 4))
    (1 : BitVec 12) (0xFB4 : Word) (by decide)
  rw [ofNat_succ_addr] at haddi0
  have hlbu1 := bytesRegion_lbu_within .x6 .x31 secBase v6 (0xFB8 : Word) sb (secOfs + 4 + 1)
    (by decide) halignS hb1 (by omega) (hsvalid _ hb1)
  have haddi1 := addi_spec_gen_same_within .x31 (secBase + BitVec.ofNat 64 (secOfs + 4 + 1))
    (1 : BitVec 12) (0xFBC : Word) (by decide)
  rw [ofNat_succ_addr] at haddi1
  have hlbu2 := bytesRegion_lbu_within .x7 .x31 secBase v7 (0xFC0 : Word) sb (secOfs + 4 + 2)
    (by decide) halignS hb2 (by omega) (hsvalid _ hb2)
  have haddi2 := addi_spec_gen_same_within .x31 (secBase + BitVec.ofNat 64 (secOfs + 4 + 2))
    (1 : BitVec 12) (0xFC4 : Word) (by decide)
  rw [ofNat_succ_addr] at haddi2
  have hlbu3 := bytesRegion_lbu_within .x28 .x31 secBase v28 (0xFC8 : Word) sb
    (secOfs + 4 + 3) (by decide) halignS hb3 (by omega) (hsvalid _ hb3)
  have hslli1 := slli_spec_gen_same_within .x6 ((sb[secOfs + 4 + 1]'hb1).zeroExtend 64)
    (8 : BitVec 6) (0xFCC : Word) (by decide)
  have hslli2 := slli_spec_gen_same_within .x7 ((sb[secOfs + 4 + 2]'hb2).zeroExtend 64)
    (16 : BitVec 6) (0xFD0 : Word) (by decide)
  have hslli3 := slli_spec_gen_same_within .x28 ((sb[secOfs + 4 + 3]'hb3).zeroExtend 64)
    (24 : BitVec 6) (0xFD4 : Word) (by decide)
  rw [show ((8 : BitVec 6)).toNat = 8 from rfl] at hslli1
  rw [show ((16 : BitVec 6)).toNat = 16 from rfl] at hslli2
  rw [show ((24 : BitVec 6)).toNat = 24 from rfl] at hslli3
  have hadd1 := add_spec_gen_rd_eq_rs1_within .x5 .x6
    ((sb[secOfs + 4]'hb0).zeroExtend 64)
    (((sb[secOfs + 4 + 1]'hb1).zeroExtend 64) <<< 8) (0xFD8 : Word) (by decide)
  have hadd2 := add_spec_gen_rd_eq_rs1_within .x5 .x7
    ((sb[secOfs + 4]'hb0).zeroExtend 64 + ((sb[secOfs + 4 + 1]'hb1).zeroExtend 64) <<< 8)
    (((sb[secOfs + 4 + 2]'hb2).zeroExtend 64) <<< 16) (0xFDC : Word) (by decide)
  have hadd3 := add_spec_gen_rd_eq_rs1_within .x5 .x28
    (((sb[secOfs + 4]'hb0).zeroExtend 64 + ((sb[secOfs + 4 + 1]'hb1).zeroExtend 64) <<< 8)
      + ((sb[secOfs + 4 + 2]'hb2).zeroExtend 64) <<< 16)
    (((sb[secOfs + 4 + 3]'hb3).zeroExtend 64) <<< 24) (0xFE0 : Word) (by decide)
  have hfold :
      (((sb[secOfs + 4]'hb0).zeroExtend 64
            + ((sb[secOfs + 4 + 1]'hb1).zeroExtend 64) <<< 8)
          + ((sb[secOfs + 4 + 2]'hb2).zeroExtend 64) <<< 16)
          + ((sb[secOfs + 4 + 3]'hb3).zeroExtend 64) <<< 24
        = BitVec.ofNat 64 (u32le sb (secOfs + 4)) := by
    rw [u32le_fold]
    unfold u32le
    rw [List.getElem_eq_getD (l := sb) (i := secOfs + 4) 0,
        List.getElem_eq_getD (l := sb) (i := secOfs + 4 + 1) 0,
        List.getElem_eq_getD (l := sb) (i := secOfs + 4 + 2) 0,
        List.getElem_eq_getD (l := sb) (i := secOfs + 4 + 3) 0]
  rw [hfold] at hadd3
  have hadd4 := add_spec_gen_within .x22 .x18 .x5 (secBase + BitVec.ofNat 64 secOfs)
    (BitVec.ofNat 64 (u32le sb (secOfs + 4))) arb22 (0xFE4 : Word) (by decide)
  rw [addr_fold] at hadd4
  refine cpsTripleWithin_weaken (fun _ h => h)
    (Q := (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
      ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 4 + 3)))
      ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb (secOfs + 4)))
      ** (.x6 ↦ᵣ (((sb[secOfs + 4 + 1]'hb1).zeroExtend 64) <<< 8))
      ** (.x7 ↦ᵣ (((sb[secOfs + 4 + 2]'hb2).zeroExtend 64) <<< 16))
      ** (.x28 ↦ᵣ (((sb[secOfs + 4 + 3]'hb3).zeroExtend 64) <<< 24))
      ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb (secOfs + 4))))
      ** bytesRegion secBase sb)
    (fun h hq => ?_)
    (by runBlock haddi hlbu0 haddi0 hlbu1 haddi1 hlbu2 haddi2 hlbu3 hslli1 hslli2 hslli3
        hadd1 hadd2 hadd3 hadd4)
  rw [List.getElem_eq_getD (l := sb) (i := secOfs + 4 + 1),
      List.getElem_eq_getD (l := sb) (i := secOfs + 4 + 2),
      List.getElem_eq_getD (l := sb) (i := secOfs + 4 + 3)] at hq
  exact hq
  all_goals exact bytesRegion_pcFree _ _

/-- Body 43 (`0xFE8 → 0xFEC`, the join): compute element 0's length into `x5`
    (as `ofNat (elEnd - off0)` under the well-formedness bounds). -/
private theorem seg5_spec (secBase : Word) (secOfs off0 elEnd : Nat) (v5 : Word)
    (hle : off0 ≤ elEnd) (hlt : secOfs + elEnd < 2 ^ 64) :
    cpsTripleWithin 1 (0xFE8 : Word) (0xFEC : Word) phmwCr
      ((.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + off0)))
        ** (.x5 ↦ᵣ v5))
      ((.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + off0)))
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (elEnd - off0))) := by
  refine liftSeg (seg := seg5Prog) 52 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 1 (0xFE8 : Word) (0xFEC : Word) (CodeReq.ofProg (0xFE8 : Word) seg5Prog) _ _
  simp only [seg5Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hsub := sub_spec_gen_within .x5 .x22 .x21
    (secBase + BitVec.ofNat 64 (secOfs + elEnd))
    (secBase + BitVec.ofNat 64 (secOfs + off0)) v5 (0xFE8 : Word) (by decide)
  rw [sub_common_base, ofNat_sub_ofNat (by omega) hlt,
      show secOfs + elEnd - (secOfs + off0) = elEnd - off0 from by omega] at hsub
  runBlock hsub

/-- Body 45–48 (`0xFF0 → 0x1000`): set up the memcmp countdown — cursors,
    counter, match flag. -/
private theorem seg6_spec (parentBase elStartW lenW : Word) (v5 v6 v7 v28 : Word) :
    cpsTripleWithin 4 (0xFF0 : Word) (0x1000 : Word) phmwCr
      ((.x8 ↦ᵣ parentBase) ** (.x21 ↦ᵣ elStartW) ** (.x9 ↦ᵣ lenW)
        ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28))
      ((.x8 ↦ᵣ parentBase) ** (.x21 ↦ᵣ elStartW) ** (.x9 ↦ᵣ lenW)
        ** (.x5 ↦ᵣ (1 : Word)) ** (.x6 ↦ᵣ parentBase) ** (.x7 ↦ᵣ elStartW)
        ** (.x28 ↦ᵣ lenW)) := by
  refine liftSeg (seg := seg6Prog) 54 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 4 (0xFF0 : Word) (0x1000 : Word) (CodeReq.ofProg (0xFF0 : Word) seg6Prog) _ _
  simp only [seg6Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have h0 := mv_spec_gen_within .x6 .x8 parentBase v6 (0xFF0 : Word) (by decide)
  have h1 := mv_spec_gen_within .x7 .x21 elStartW v7 (0xFF4 : Word) (by decide)
  have h2 := mv_spec_gen_within .x28 .x9 lenW v28 (0xFF8 : Word) (by decide)
  have h3 := li_spec_gen_within .x5 v5 (1 : Word) (0xFFC : Word) (by decide)
  runBlock h0 h1 h2 h3

/-- Body 59–61 (`0x1028 → 0x1040`): store the match flag to `[a4]`, set
    `status = 0`, jump to the body exit.  The four loop-touched `t`-registers
    are released to ownership. -/
private theorem seg7_spec (outPtr flagW oldD v10 w6 w7 w28 : Word) :
    cpsTripleWithin 3 (0x1028 : Word) (0x1040 : Word) phmwCr
      ((.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ flagW) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28) ** (outPtr ↦ₘ oldD) ** (.x10 ↦ᵣ v10))
      ((.x20 ↦ᵣ outPtr) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28
        ** (outPtr ↦ₘ flagW) ** (.x10 ↦ᵣ (0 : Word))) := by
  refine liftSeg (seg := seg7Prog) 68 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 3 (0x1028 : Word) (0x1040 : Word) (CodeReq.ofProg (0x1028 : Word) seg7Prog) _ _
  simp only [seg7Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hsd := sd_spec_gen_within .x20 .x5 outPtr flagW oldD (0 : BitVec 12) (0x1028 : Word)
  rw [add_sext0] at hsd
  have hli := li_spec_gen_within .x10 v10 (0 : Word) (0x102C : Word) (by decide)
  have hjal := jal_x0_spec_gen_within (16 : BitVec 21) (0x1030 : Word)
  rw [show (0x1030 : Word) + signExtend21 (16 : BitVec 21) = (0x1040 : Word) from by decide]
    at hjal
  refine cpsTripleWithin_weaken (fun _ h => h)
    (Q := (.x20 ↦ᵣ outPtr) ** (.x5 ↦ᵣ flagW) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7)
      ** (.x28 ↦ᵣ w28) ** (outPtr ↦ₘ flagW) ** (.x10 ↦ᵣ (0 : Word)))
    (fun h hq => ?_)
    (by runBlock hsd hli hjal)
  have hq1 := sepConj_mono_right
    (sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _) (fun _ h2 => h2))))) h hq
  exact hq1

/-- Body 62–63 (`0x1034 → 0x1040`): the length-mismatch exit — `status = 0`,
    jump to the body exit.  The seven scratch `t`-registers are released. -/
private theorem seg8_spec (v10 w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 2 (0x1034 : Word) (0x1040 : Word) phmwCr
      ((.x10 ↦ᵣ v10) ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7
        ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  refine liftSeg (seg := seg8Prog) 71 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 2 (0x1034 : Word) (0x1040 : Word) (CodeReq.ofProg (0x1034 : Word) seg8Prog) _ _
  simp only [seg8Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hli := li_spec_gen_within .x10 v10 (0 : Word) (0x1034 : Word) (by decide)
  have hjal := jal_x0_spec_gen_within (8 : BitVec 21) (0x1038 : Word)
  rw [show (0x1038 : Word) + signExtend21 (8 : BitVec 21) = (0x1040 : Word) from by decide]
    at hjal
  refine cpsTripleWithin_weaken (fun _ h => h)
    (Q := (.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7)
      ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
    (fun h hq => ?_)
    (by runBlock hli hjal)
  exact sepConj_mono_right
    (sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (regIs_to_regOwn .x31 _))))))) h hq

/-- Body 64 (`0x103C → 0x1040`), reached with an empty section: `status = 1`;
    all seven (untouched) scratch `t`-registers are released. -/
private theorem seg9empty_spec (v10 w5 w6 w7 w28 w29 w30 w31 : Word) :
    cpsTripleWithin 1 (0x103C : Word) (0x1040 : Word) phmwCr
      ((.x10 ↦ᵣ v10) ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
      ((.x10 ↦ᵣ (1 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7
        ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
  refine liftSeg (seg := seg9Prog) 73 (by decide) (by rfl) (by decide) ?_
  show cpsTripleWithin 1 (0x103C : Word) (0x1040 : Word) (CodeReq.ofProg (0x103C : Word) seg9Prog) _ _
  simp only [seg9Prog]
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  have hli := li_spec_gen_within .x10 v10 (1 : Word) (0x103C : Word) (by decide)
  refine cpsTripleWithin_weaken (fun _ h => h)
    (Q := (.x10 ↦ᵣ (1 : Word)) ** (.x5 ↦ᵣ w5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7)
      ** (.x28 ↦ᵣ w28) ** (.x29 ↦ᵣ w29) ** (.x30 ↦ᵣ w30) ** (.x31 ↦ᵣ w31))
    (fun h hq => ?_)
    (by runBlock hli)
  exact sepConj_mono_right
    (sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (regIs_to_regOwn .x31 _))))))) h hq

-- ============================================================================
-- The four branches, per direction.
-- ============================================================================

/-- Body 6 (`beq s19, x0`), taken: empty section (`0xF54 → 0x103C`). -/
private theorem br6_taken (v : Word) (hv : v = 0) :
    cpsTripleWithin 1 (0xF54 : Word) (0x103C : Word) phmwCr
      ((.x19 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x19 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x19 .x0 (232 : BitVec 13) v 0 (0xF54 : Word)
  rw [show (0xF54 : Word) + signExtend13 (232 : BitVec 13) = (0x103C : Word) from by decide]
    at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 15 (0xF54 : Word) (.BEQ .x19 .x0 (232 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbeq)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hv)

/-- Body 6 (`beq s19, x0`), not taken: non-empty section (`0xF54 → 0xF58`). -/
private theorem br6_ntaken (v : Word) (hv : v ≠ 0) :
    cpsTripleWithin 1 (0xF54 : Word) (0xF58 : Word) phmwCr
      ((.x19 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x19 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x19 .x0 (232 : BitVec 13) v 0 (0xF54 : Word)
  rw [show (0xF54 : Word) + 4 = (0xF58 : Word) from by decide] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 15 (0xF54 : Word) (.BEQ .x19 .x0 (232 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbeq)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hv ((sepConj_pure_right _).1 hBP).2)

/-- Body 22 (`beq x29, x0`), taken: `N = 0` (`0xF94 → 0x103C`). -/
private theorem br22_taken (v : Word) (hv : v = 0) :
    cpsTripleWithin 1 (0xF94 : Word) (0x103C : Word) phmwCr
      ((.x29 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x29 .x0 (168 : BitVec 13) v 0 (0xF94 : Word)
  rw [show (0xF94 : Word) + signExtend13 (168 : BitVec 13) = (0x103C : Word) from by decide]
    at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 31 (0xF94 : Word) (.BEQ .x29 .x0 (168 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbeq)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hv)

/-- Body 22 (`beq x29, x0`), not taken: `N ≠ 0` (`0xF94 → 0xF98`). -/
private theorem br22_ntaken (v : Word) (hv : v ≠ 0) :
    cpsTripleWithin 1 (0xF94 : Word) (0xF98 : Word) phmwCr
      ((.x29 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word)))
      ((.x29 ↦ᵣ v) ** (Reg.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x29 .x0 (168 : BitVec 13) v 0 (0xF94 : Word)
  rw [show (0xF94 : Word) + 4 = (0xF98 : Word) from by decide] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 31 (0xF94 : Word) (.BEQ .x29 .x0 (168 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbeq)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hv ((sepConj_pure_right _).1 hBP).2)

/-- Body 25 (`bltu x30, x29` with `x30 = 1`), taken: `N > 1`
    (`0xFA0 → 0xFAC`). -/
private theorem br25_taken (v : Word) (hv : BitVec.ult (1 : Word) v = true) :
    cpsTripleWithin 1 (0xFA0 : Word) (0xFAC : Word) phmwCr
      ((.x30 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ v))
      ((.x30 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ v)) := by
  have hbltu := bltu_spec_gen_within .x30 .x29 (12 : BitVec 13) (1 : Word) v (0xFA0 : Word)
  rw [show (0xFA0 : Word) + signExtend13 (12 : BitVec 13) = (0xFAC : Word) from by decide]
    at hbltu
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 34 (0xFA0 : Word) (.BLTU .x30 .x29 (12 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbltu)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hv)

/-- Body 25 (`bltu x30, x29` with `x30 = 1`), not taken: `N ≤ 1`
    (`0xFA0 → 0xFA4`). -/
private theorem br25_ntaken (v : Word) (hv : ¬ BitVec.ult (1 : Word) v = true) :
    cpsTripleWithin 1 (0xFA0 : Word) (0xFA4 : Word) phmwCr
      ((.x30 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ v))
      ((.x30 ↦ᵣ (1 : Word)) ** (.x29 ↦ᵣ v)) := by
  have hbltu := bltu_spec_gen_within .x30 .x29 (12 : BitVec 13) (1 : Word) v (0xFA0 : Word)
  rw [show (0xFA0 : Word) + 4 = (0xFA4 : Word) from by decide] at hbltu
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 34 (0xFA0 : Word) (.BLTU .x30 .x29 (12 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbltu)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hv ((sepConj_pure_right _).1 hBP).2)

/-- Body 44 (`bne x5, x9`), taken: length mismatch (`0xFEC → 0x1034`). -/
private theorem br44_taken (v1 v2 : Word) (hv : v1 ≠ v2) :
    cpsTripleWithin 1 (0xFEC : Word) (0x1034 : Word) phmwCr
      ((.x5 ↦ᵣ v1) ** (.x9 ↦ᵣ v2))
      ((.x5 ↦ᵣ v1) ** (.x9 ↦ᵣ v2)) := by
  have hbne := bne_spec_gen_within .x5 .x9 (72 : BitVec 13) v1 v2 (0xFEC : Word)
  rw [show (0xFEC : Word) + signExtend13 (72 : BitVec 13) = (0x1034 : Word) from by decide]
    at hbne
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 53 (0xFEC : Word) (.BNE .x5 .x9 (72 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbne)
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hv ((sepConj_pure_right _).1 hBP).2)

/-- Body 44 (`bne x5, x9`), not taken: lengths equal (`0xFEC → 0xFF0`). -/
private theorem br44_ntaken (v1 v2 : Word) (hv : v1 = v2) :
    cpsTripleWithin 1 (0xFEC : Word) (0xFF0 : Word) phmwCr
      ((.x5 ↦ᵣ v1) ** (.x9 ↦ᵣ v2))
      ((.x5 ↦ᵣ v1) ** (.x9 ↦ᵣ v2)) := by
  have hbne := bne_spec_gen_within .x5 .x9 (72 : BitVec 13) v1 v2 (0xFEC : Word)
  rw [show (0xFEC : Word) + 4 = (0xFF0 : Word) from by decide] at hbne
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (memAt 53 (0xFEC : Word) (.BNE .x5 .x9 (72 : BitVec 13)) (by decide) (by decide) (by decide) (by rfl)) hbne)
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 hv)

-- ============================================================================
-- The join tail (`0xFE8 → 0x1040`): length check, memcmp countdown (via the
-- verified core), and the reconverging exits.
-- ============================================================================

/-- From the join (element-0 window computed) to the body exit: on a length
    mismatch `is_match` stays `0`; on matching lengths the verified memcmp
    countdown accumulates the genuine byte-equality flag into `[a4]`.  Either
    way `status = 0` and control reconverges at `0x1040`. -/
private theorem tail_spec
    (parentBase secBase outPtr : Word) (pb sb : List (BitVec 8))
    (secOfs sectionLen elEnd : Nat)
    (v5 w6 w7 w28 v29 v30 v31 : Word)
    (hfit : secOfs + sectionLen ≤ sb.length)
    (halignP : parentBase.toNat % 8 = 0) (halignS : secBase.toNat % 8 = 0)
    (hpover : parentBase.toNat + pb.length < 2 ^ 64)
    (hsover : secBase.toNat + sb.length < 2 ^ 64)
    (hpvalid : ∀ i, i < pb.length →
      isValidByteAccess (parentBase + BitVec.ofNat 64 i) = true)
    (hsvalid : ∀ i, i < sb.length →
      isValidByteAccess (secBase + BitVec.ofNat 64 i) = true)
    (hoffle : u32le sb secOfs ≤ elEnd) (hendle : elEnd ≤ sectionLen) :
    cpsTripleWithin (10 * pb.length + 12) (0xFE8 : Word) (0x1040 : Word) phmwCr
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ w6) ** (.x7 ↦ᵣ w7) ** (.x28 ↦ᵣ w28)
        ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
        ** (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb ** bytesRegion secBase sb)
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28
        ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
        ** (.x8 ↦ᵣ parentBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (if elEnd - u32le sb secOfs = pb.length
              ∧ (∀ k, k < pb.length →
                  pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0)
            then (1 : Word) else (0 : Word)))
        ** bytesRegion parentBase pb ** bytesRegion secBase sb) := by
  have hslt : sectionLen < 2 ^ 64 := by omega
  have hlenlt : pb.length < 2 ^ 64 := by omega
  have hellenlt : elEnd - u32le sb secOfs < 2 ^ 64 := by omega
  have h5 := seg5_spec secBase secOfs (u32le sb secOfs) elEnd v5 hoffle (by omega)
  by_cases hLen : elEnd - u32le sb secOfs = pb.length
  · -- matching lengths: run the verified memcmp countdown.
    have hbr := br44_ntaken (BitVec.ofNat 64 (elEnd - u32le sb secOfs))
      (BitVec.ofNat 64 pb.length) (by rw [hLen])
    have h6 := seg6_spec parentBase
      (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs))
      (BitVec.ofNat 64 pb.length) (BitVec.ofNat 64 (elEnd - u32le sb secOfs)) w6 w7 w28
    have hsb2 : secOfs + u32le sb secOfs + pb.length ≤ sb.length := by omega
    have hloop0 := ParentHeaderMemcmp.memcmpLoop_spec parentBase secBase pb sb
      (secOfs + u32le sb secOfs) pb.length hlenlt rfl hsb2 halignP halignS hpover
      (by omega) hpvalid (fun i hi => hsvalid _ (by omega))
    have hloop1 := cpsTripleWithin_extend_code loopSub hloop0
    simp only [ParentHeaderMemcmp.memcmpInv, Nat.sub_self, Nat.sub_zero,
      ParentHeaderMemcmp.memcmpFlag_zero, Nat.add_zero, add_ofNat_zero] at hloop1
    have hloop2 := cpsTripleWithin_weaken
      (fun h hp => sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (regIs_to_regOwn .x29 v29)
            (sepConj_mono (regIs_to_regOwn .x30 v30)
              (sepConj_mono (regIs_to_regOwn .x31 v31) (fun _ h2 => h2)))))))) h hp)
      (fun _ h => h) hloop1
    have h7 := seg7_spec outPtr
      (ParentHeaderMemcmp.memcmpFlag pb sb (secOfs + u32le sb secOfs) pb.length)
      0 parentBase (parentBase + BitVec.ofNat 64 pb.length)
      (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs + pb.length))
      (BitVec.ofNat 64 0)
    -- The accumulated flag IS the genuine byte-equality predicate.
    have hflag :
        ParentHeaderMemcmp.memcmpFlag pb sb (secOfs + u32le sb secOfs) pb.length
          = (if elEnd - u32le sb secOfs = pb.length
                ∧ (∀ k, k < pb.length →
                    pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0)
              then (1 : Word) else (0 : Word)) := by
      obtain ⟨hiff, h01⟩ := ParentHeaderMemcmp.memcmpFlag_eq_one_iff pb sb
        (secOfs + u32le sb secOfs) pb.length
      by_cases hbeq : ∀ k, k < pb.length →
          pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0
      · rw [if_pos ⟨hLen, hbeq⟩]; exact hiff.mpr hbeq
      · rw [if_neg (fun hc => hbeq hc.2)]
        rcases h01 with h0 | h1
        · exact h0
        · exact absurd (hiff.mp h1) hbeq
    rw [← hflag]
    have h5F := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ w6)
        ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) h5
    have hbrF := cpsTripleWithin_frameR
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x6 ↦ᵣ w6)
        ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) hbr
    have h6F := cpsTripleWithin_frameR
      ((.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) h6
    have hloopF := cpsTripleWithin_frameR
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x8 ↦ᵣ parentBase)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (outPtr ↦ₘ (0 : Word)))
      (by pcf) hloop2
    have h7F := cpsTripleWithin_frameR
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x8 ↦ᵣ parentBase)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb
        ** regOwn .x29 ** regOwn .x30 ** regOwn .x31)
      (by pcf) h7
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h5F hbrF
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h6F
    have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hloopF
    have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 h7F
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_mono_nSteps (by omega) s4)
  · -- length mismatch: skip the loop, `is_match` stays 0.
    have hbr := br44_taken (BitVec.ofNat 64 (elEnd - u32le sb secOfs))
      (BitVec.ofNat 64 pb.length)
      (fun heq => hLen ((ofNat_inj' hellenlt hlenlt).1 heq))
    have h8 := seg8_spec parentBase (BitVec.ofNat 64 (elEnd - u32le sb secOfs))
      w6 w7 w28 v29 v30 v31
    rw [if_neg (fun hc => hLen hc.1)]
    have h5F := cpsTripleWithin_frameR
      ((.x6 ↦ᵣ w6)
        ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) h5
    have hbrF := cpsTripleWithin_frameR
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x6 ↦ᵣ w6)
        ** (.x7 ↦ᵣ w7)
        ** (.x28 ↦ᵣ w28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x10 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) hbr
    have h8F := cpsTripleWithin_frameR
      ((.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + elEnd)))
        ** (.x8 ↦ᵣ parentBase)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) h8
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h5F hbrF
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h8F
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_mono_nSteps (by omega) s2)


-- ============================================================================
-- The unified single-exit body triple: the genuine disjunctive semantics.
-- ============================================================================

/-- **The whole single-exit body** (`0xF3C → 0x1040`), with the routine's
    genuine, unweakened disjunctive post:

    * `a0 = phmwStatus` — `1` iff the section is empty or its offset table has
      `N = 0` (both branch to the same exit in the original), else `0`;
    * `[a4] = phmwIsMatch` — `1` iff the section is non-empty, `N ≥ 1`,
      element 0's length equals `parent_header_rlp`'s, and every byte agrees;
    * the saved `s`-registers hold the documented working values (element-0
      window in `s21`/`s22` on the reached paths), scratch `t`-registers are
      released, and both byte regions are untouched.

    Well-formedness hypotheses `hwf4`/`hwf8`/`hwfEnd` are the SSZ offset-table
    facts (non-empty section has a 4-byte first offset; `N ≥ 2` implies an
    8-byte table; element 0's window lies within the section) — all hold for
    any validly-serialized witness section. -/
theorem phmwCore_spec
    (parentBase secBase outPtr oldOut : Word) (pb sb : List (BitVec 8))
    (secOfs sectionLen : Nat)
    (arb8 arb9 arb18 arb19 arb20 arb21 arb22 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (hfit : secOfs + sectionLen ≤ sb.length)
    (halignP : parentBase.toNat % 8 = 0) (halignS : secBase.toNat % 8 = 0)
    (hpover : parentBase.toNat + pb.length < 2 ^ 64)
    (hsover : secBase.toNat + sb.length < 2 ^ 64)
    (hpvalid : ∀ i, i < pb.length →
      isValidByteAccess (parentBase + BitVec.ofNat 64 i) = true)
    (hsvalid : ∀ i, i < sb.length →
      isValidByteAccess (secBase + BitVec.ofNat 64 i) = true)
    (hwf4 : sectionLen ≠ 0 → 4 ≤ sectionLen)
    (hwf8 : sectionLen ≠ 0 → 2 ≤ phmwN sb secOfs → 8 ≤ sectionLen)
    (hwfEnd : sectionLen ≠ 0 → phmwN sb secOfs ≠ 0 →
      u32le sb secOfs ≤ phmwElEnd sb secOfs sectionLen
        ∧ phmwElEnd sb secOfs sectionLen ≤ sectionLen) :
    cpsTripleWithin (10 * pb.length + 60) (0xF3C : Word) (0x1040 : Word) phmwCr
      ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ arb8)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ arb9)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ arb18)
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ arb19)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ arb20)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ v5)
        ** (.x6 ↦ᵣ v6)
        ** (.x7 ↦ᵣ v7)
        ** (.x28 ↦ᵣ v28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ oldOut)
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      ((.x10 ↦ᵣ phmwStatus sb secOfs sectionLen) ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length) ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs)) ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr) ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ (if sectionLen = 0 ∨ phmwN sb secOfs = 0 then arb21
              else secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ (if sectionLen = 0 ∨ phmwN sb secOfs = 0 then arb22
              else secBase + BitVec.ofNat 64 (secOfs + phmwElEnd sb secOfs sectionLen)))
        ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28
        ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ phmwIsMatch pb sb secOfs sectionLen)
        ** bytesRegion parentBase pb ** bytesRegion secBase sb) := by
  have hu32 := u32le_lt sb secOfs
  have hslt : sectionLen < 2 ^ 64 := by omega
  have hNlt : u32le sb secOfs / 4 < 2 ^ 64 := by omega
  simp only [phmwStatus, phmwIsMatch, phmwElLen, phmwElEnd, phmwN]
  have h1 := seg1_spec parentBase (BitVec.ofNat 64 pb.length) (secBase + BitVec.ofNat 64 secOfs) (BitVec.ofNat 64 sectionLen)
    outPtr oldOut arb8 arb9 arb18 arb19 arb20
  have h1F := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ v5)
        ** (.x6 ↦ᵣ v6)
        ** (.x7 ↦ᵣ v7)
        ** (.x28 ↦ᵣ v28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
    (by pcf) h1
  by_cases hS0 : sectionLen = 0
  · -- EMPTY: branch at body 6 straight to the status-1 exit.
    simp only [if_pos (Or.inl hS0 : sectionLen = 0 ∨ u32le sb secOfs / 4 = 0)]
    rw [if_neg (fun hc => hc.1 hS0)]
    have hbr := br6_taken (BitVec.ofNat 64 sectionLen) (by rw [hS0]; rfl)
    have hbrF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ v5)
        ** (.x6 ↦ᵣ v6)
        ** (.x7 ↦ᵣ v7)
        ** (.x28 ↦ᵣ v28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) hbr
    have h9 := seg9empty_spec parentBase v5 v6 v7 v28 v29 v30 v31
    have h9F := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) h9
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1F hbrF
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h9F
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
      (cpsTripleWithin_mono_nSteps (by omega) s2)
  · have hj4 : secOfs + 4 ≤ sb.length := by have := hwf4 hS0; omega
    have hbr6 := br6_ntaken (BitVec.ofNat 64 sectionLen) (ofNat_ne_zero hS0 hslt)
    have hbr6F := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ v5)
        ** (.x6 ↦ᵣ v6)
        ** (.x7 ↦ᵣ v7)
        ** (.x28 ↦ᵣ v28)
        ** (.x29 ↦ᵣ v29)
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ v31)
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
      (by pcf) hbr6
    have h2 := seg2_spec secBase sb secOfs v31 v5 v6 v7 v28 v29 hj4 halignS hsover hsvalid
    have h2F := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x30 ↦ᵣ v30)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb)
      (by pcf) h2
    by_cases hN0 : u32le sb secOfs / 4 = 0
    · -- N = 0: same exit as the empty section (status 1).
      simp only [if_pos (Or.inr hN0 : sectionLen = 0 ∨ u32le sb secOfs / 4 = 0)]
      rw [if_neg (fun hc => hc.2.1 hN0)]
      have hbr22 := br22_taken (BitVec.ofNat 64 (u32le sb secOfs / 4)) (by rw [hN0]; rfl)
      have hbr22F := cpsTripleWithin_frameR
        ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
        (by pcf) hbr22
      have h9 := seg9empty_spec parentBase (BitVec.ofNat 64 (u32le sb secOfs))
        (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8)
        (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16)
        (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24)
        (BitVec.ofNat 64 (u32le sb secOfs / 4)) v30
        (secBase + BitVec.ofNat 64 (secOfs + 3))
      have h9F := cpsTripleWithin_frameR
        ((.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
        (by pcf) h9
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1F hbr6F
      have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h2F
      have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hbr22F
      have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 h9F
      refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
        (cpsTripleWithin_mono_nSteps (by omega) s4)
    · -- Reached: decode element-0's window and run the join tail.
      have hne : ¬ (sectionLen = 0 ∨ u32le sb secOfs / 4 = 0) := fun hc => hc.elim hS0 hN0
      simp only [if_neg hne]
      obtain ⟨hoffle, hendle⟩ := hwfEnd hS0 hN0
      simp only [phmwElEnd, phmwN] at hoffle hendle
      have hbr22 := br22_ntaken (BitVec.ofNat 64 (u32le sb secOfs / 4)) (ofNat_ne_zero hN0 hNlt)
      have hbr22F := cpsTripleWithin_frameR
        ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ arb21)
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x30 ↦ᵣ v30)
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
        (by pcf) hbr22
      have h3 := seg3_spec secBase sb secOfs arb21 v30
      have h3F := cpsTripleWithin_frameR
        ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x22 ↦ᵣ arb22)
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x29 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs / 4))
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
        (by pcf) h3
      by_cases hN1 : u32le sb secOfs / 4 = 1
      · -- N = 1: element 0 ends at the section end.
        simp only [if_pos hN1]
        simp only [show (sectionLen ≠ 0 ∧ u32le sb secOfs / 4 ≠ 0
              ∧ sectionLen - u32le sb secOfs = pb.length
              ∧ (∀ k, k < pb.length →
                  pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0))
            ↔ (sectionLen - u32le sb secOfs = pb.length
              ∧ (∀ k, k < pb.length →
                  pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0)) from
          ⟨fun hc => ⟨hc.2.2.1, hc.2.2.2⟩, fun hc => ⟨hS0, hN0, hc.1, hc.2⟩⟩]
        rw [if_pos hN1] at hoffle hendle
        have hbr25 := br25_ntaken (BitVec.ofNat 64 (u32le sb secOfs / 4))
          (fun hu => by have := (ult_one_ofNat hNlt).1 hu; omega)
        have hbr25F := cpsTripleWithin_frameR
          ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
          (by pcf) hbr25
        have h4 := seg4n1_spec secBase secOfs sectionLen arb22
        have h4F := cpsTripleWithin_frameR
          ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x29 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs / 4))
        ** (.x30 ↦ᵣ (1 : Word))
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
          (by pcf) h4
        have htail := tail_spec parentBase secBase outPtr pb sb secOfs sectionLen
          sectionLen (BitVec.ofNat 64 (u32le sb secOfs)) (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8) (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16) (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24)
          (BitVec.ofNat 64 (u32le sb secOfs / 4)) (1 : Word)
          (secBase + BitVec.ofNat 64 (secOfs + 3))
          hfit halignP halignS hpover hsover hpvalid hsvalid hoffle hendle
        have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1F hbr6F
        have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h2F
        have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hbr22F
        have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 h3F
        have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hbr25F
        have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 h4F
        have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 htail
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
          (cpsTripleWithin_mono_nSteps (by omega) s7)
      · -- N ≥ 2: decode the second offset for element 0's end.
        simp only [if_neg hN1]
        simp only [show (sectionLen ≠ 0 ∧ u32le sb secOfs / 4 ≠ 0
              ∧ u32le sb (secOfs + 4) - u32le sb secOfs = pb.length
              ∧ (∀ k, k < pb.length →
                  pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0))
            ↔ (u32le sb (secOfs + 4) - u32le sb secOfs = pb.length
              ∧ (∀ k, k < pb.length →
                  pb.getD k 0 = sb.getD (secOfs + u32le sb secOfs + k) 0)) from
          ⟨fun hc => ⟨hc.2.2.1, hc.2.2.2⟩, fun hc => ⟨hS0, hN0, hc.1, hc.2⟩⟩]
        rw [if_neg hN1] at hoffle hendle
        have hN2 : 2 ≤ u32le sb secOfs / 4 := by omega
        have hj8 : secOfs + 8 ≤ sb.length := by have := hwf8 hS0 hN2; omega
        have hbr25 := br25_taken (BitVec.ofNat 64 (u32le sb secOfs / 4))
          ((ult_one_ofNat hNlt).2 (by omega))
        have hbr25F := cpsTripleWithin_frameR
          ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x18 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x22 ↦ᵣ arb22)
        ** (.x5 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs))
        ** (.x6 ↦ᵣ (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8))
        ** (.x7 ↦ᵣ (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16))
        ** (.x28 ↦ᵣ (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24))
        ** (.x31 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + 3)))
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb
        ** bytesRegion secBase sb)
          (by pcf) hbr25
        have h4 := seg4n2_spec secBase sb secOfs
          (secBase + BitVec.ofNat 64 (secOfs + 3)) (BitVec.ofNat 64 (u32le sb secOfs))
          (((sb.getD (secOfs + 1) 0).zeroExtend 64) <<< 8) (((sb.getD (secOfs + 2) 0).zeroExtend 64) <<< 16) (((sb.getD (secOfs + 3) 0).zeroExtend 64) <<< 24) arb22 hj8 halignS hsover hsvalid
        have h4F := cpsTripleWithin_frameR
          ((.x10 ↦ᵣ parentBase)
        ** (.x8 ↦ᵣ parentBase)
        ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x9 ↦ᵣ BitVec.ofNat 64 pb.length)
        ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
        ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x19 ↦ᵣ BitVec.ofNat 64 sectionLen)
        ** (.x14 ↦ᵣ outPtr)
        ** (.x20 ↦ᵣ outPtr)
        ** (.x21 ↦ᵣ (secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)))
        ** (.x29 ↦ᵣ BitVec.ofNat 64 (u32le sb secOfs / 4))
        ** (.x30 ↦ᵣ (1 : Word))
        ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (outPtr ↦ₘ (0 : Word))
        ** bytesRegion parentBase pb)
          (by pcf) h4
        have htail := tail_spec parentBase secBase outPtr pb sb secOfs sectionLen
          (u32le sb (secOfs + 4)) (BitVec.ofNat 64 (u32le sb (secOfs + 4)))
          (((sb.getD (secOfs + 4 + 1) 0).zeroExtend 64) <<< 8) (((sb.getD (secOfs + 4 + 2) 0).zeroExtend 64) <<< 16) (((sb.getD (secOfs + 4 + 3) 0).zeroExtend 64) <<< 24)
          (BitVec.ofNat 64 (u32le sb secOfs / 4)) (1 : Word)
          (secBase + BitVec.ofNat 64 (secOfs + 4 + 3))
          hfit halignP halignS hpover hsover hpvalid hsvalid hoffle hendle
        have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1F hbr6F
        have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 h2F
        have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 hbr22F
        have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 h3F
        have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hbr25F
        have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 h4F
        have s7 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s6 htail
        refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
          (cpsTripleWithin_mono_nSteps (by omega) s7)


-- ============================================================================
-- The whole-routine ABI contract, derived from `abiFrame_spec`.
-- ============================================================================

/-- Entry values of the saved registers: `ra ↦ ret` plus the caller's seven
    callee-saved values (arbitrary — the body clobbers all of them). -/
def phmwVals (ret arb8 arb9 arb18 arb19 arb20 arb21 arb22 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ret | .x8 => arb8 | .x9 => arb9 | .x18 => arb18 | .x19 => arb19
  | .x20 => arb20 | .x21 => arb21 | .x22 => arb22 | _ => 0

/-- Post-body values of the saved registers: `ra` untouched, the argument
    copies in `s0`/`s1`/`s18`–`s20`, and element 0's window in `s21`/`s22` on
    the reached paths. -/
def phmwVals' (ret parentBase secBase outPtr : Word) (pb sb : List (BitVec 8))
    (secOfs sectionLen : Nat) (arb21 arb22 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ret
  | .x8 => parentBase
  | .x9 => BitVec.ofNat 64 pb.length
  | .x18 => secBase + BitVec.ofNat 64 secOfs
  | .x19 => BitVec.ofNat 64 sectionLen
  | .x20 => outPtr
  | .x21 => if sectionLen = 0 ∨ phmwN sb secOfs = 0 then arb21
      else secBase + BitVec.ofNat 64 (secOfs + u32le sb secOfs)
  | .x22 => if sectionLen = 0 ∨ phmwN sb secOfs = 0 then arb22
      else secBase + BitVec.ofNat 64 (secOfs + phmwElEnd sb secOfs sectionLen)
  | _ => 0

/-- Caller footprint before the routine: the five arguments, the seven scratch
    `t`-registers (arbitrary), the zero register, the `is_match` output dword,
    and the two read-only byte regions. -/
def phmwCallerPre (parentBase secBase outPtr oldOut : Word)
    (pb sb : List (BitVec 8)) (secOfs sectionLen : Nat)
    (v5 v6 v7 v28 v29 v30 v31 : Word) : Assertion :=
  (.x10 ↦ᵣ parentBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
    ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
    ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x14 ↦ᵣ outPtr)
    ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)
    ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31)
    ** (Reg.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ oldOut)
    ** bytesRegion parentBase pb ** bytesRegion secBase sb

/-- Caller footprint after the routine: `a0 = phmwStatus`, the `is_match`
    dword holding `phmwIsMatch`, scratch registers released, regions
    untouched. -/
def phmwCallerPost (parentBase secBase outPtr : Word)
    (pb sb : List (BitVec 8)) (secOfs sectionLen : Nat) : Assertion :=
  (.x10 ↦ᵣ phmwStatus sb secOfs sectionLen)
    ** (.x11 ↦ᵣ BitVec.ofNat 64 pb.length)
    ** (.x12 ↦ᵣ (secBase + BitVec.ofNat 64 secOfs))
    ** (.x13 ↦ᵣ BitVec.ofNat 64 sectionLen) ** (.x14 ↦ᵣ outPtr)
    ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28
    ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
    ** (Reg.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ phmwIsMatch pb sb secOfs sectionLen)
    ** bytesRegion parentBase pb ** bytesRegion secBase sb

/-- **The whole-routine ABI-frame contract for the re-emitted
    `parent_header_matches_witness_first`, derived from `abiFrame_spec`.**

    Running the routine from entry `0xF18` returns to `ret` with `sp`, `ra`,
    and all seven saved `s`-registers restored to their entry values
    (preservation *derived* by the frame rule — the body clobbered every one
    of them), the frame released with the slots holding the saved values, and
    the caller effect being the routine's genuine disjunctive semantics:

    * `a0 = 1` and `[a4] = 0` when the witness-headers section is empty or its
      offset table is empty (`N = 0`);
    * `a0 = 0` and `[a4] = 1` when element 0's length equals
      `parent_header_rlp`'s and every byte agrees;
    * `a0 = 0` and `[a4] = 0` otherwise (length mismatch or any differing
      byte). -/
theorem phmwFrame_spec
    (ret sp0 parentBase secBase outPtr oldOut : Word)
    (pb sb : List (BitVec 8)) (secOfs sectionLen : Nat)
    (arb8 arb9 arb18 arb19 arb20 arb21 arb22 : Word)
    (v5 v6 v7 v28 v29 v30 v31 : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hfit : secOfs + sectionLen ≤ sb.length)
    (halignP : parentBase.toNat % 8 = 0) (halignS : secBase.toNat % 8 = 0)
    (hpover : parentBase.toNat + pb.length < 2 ^ 64)
    (hsover : secBase.toNat + sb.length < 2 ^ 64)
    (hpvalid : ∀ i, i < pb.length →
      isValidByteAccess (parentBase + BitVec.ofNat 64 i) = true)
    (hsvalid : ∀ i, i < sb.length →
      isValidByteAccess (secBase + BitVec.ofNat 64 i) = true)
    (hwf4 : sectionLen ≠ 0 → 4 ≤ sectionLen)
    (hwf8 : sectionLen ≠ 0 → 2 ≤ phmwN sb secOfs → 8 ≤ sectionLen)
    (hwfEnd : sectionLen ≠ 0 → phmwN sb secOfs ≠ 0 →
      u32le sb secOfs ≤ phmwElEnd sb secOfs sectionLen
        ∧ phmwElEnd sb secOfs sectionLen ≤ sectionLen) :
    cpsTripleWithin
      (1 + phmwFrame.length + (10 * pb.length + 60) + phmwFrame.length + 1 + 1)
      (0xF18 : Word) ret phmwCr
      ((.x2 ↦ᵣ sp0)
        ** regsAt phmwFrame (phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
        ** frameSlotsOwn phmwFrame (sp0 + signExtend12 (-64 : BitVec 12))
        ** phmwCallerPre parentBase secBase outPtr oldOut pb sb secOfs sectionLen
            v5 v6 v7 v28 v29 v30 v31)
      ((.x2 ↦ᵣ sp0)
        ** regsAt phmwFrame (phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
        ** frameSlotsSaved phmwFrame (sp0 + signExtend12 (-64 : BitVec 12))
            (phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
        ** phmwCallerPost parentBase secBase outPtr pb sb secOfs sectionLen) := by
  set newSp := sp0 + signExtend12 (-64 : BitVec 12) with hNS
  have hbody :
      cpsTripleWithin (10 * pb.length + 60)
        ((0xF18 : Word) + BitVec.ofNat 64 (4 * (1 + phmwFrame.length)))
        ((0xF18 : Word) + BitVec.ofNat 64 (4 * (1 + phmwFrame.length + phmwBody.length)))
        phmwCr
        ((.x2 ↦ᵣ newSp)
          ** regsAt phmwFrame (phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
          ** frameSlotsSaved phmwFrame newSp
              (phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
          ** phmwCallerPre parentBase secBase outPtr oldOut pb sb secOfs sectionLen
              v5 v6 v7 v28 v29 v30 v31)
        ((.x2 ↦ᵣ newSp)
          ** regsAt phmwFrame
              (phmwVals' ret parentBase secBase outPtr pb sb secOfs sectionLen arb21 arb22)
          ** frameSlotsSaved phmwFrame newSp
              (phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
          ** phmwCallerPost parentBase secBase outPtr pb sb secOfs sectionLen) := by
    have hentry : (0xF18 : Word) + BitVec.ofNat 64 (4 * (1 + phmwFrame.length))
        = (0xF3C : Word) := by decide
    have hexit : (0xF18 : Word)
          + BitVec.ofNat 64 (4 * (1 + phmwFrame.length + phmwBody.length))
        = (0x1040 : Word) := by decide
    rw [hentry, hexit]
    simp only [phmwFrame, regsAt, frameSlotsSaved, phmwVals, phmwVals',
      phmwCallerPre, phmwCallerPost, List.foldr_cons, List.foldr_nil,
      sepConj_emp_right']
    have hframed := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret)
        ** ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ ret)
        ** ((newSp + signExtend12 (8 : BitVec 12)) ↦ₘ arb8)
        ** ((newSp + signExtend12 (16 : BitVec 12)) ↦ₘ arb9)
        ** ((newSp + signExtend12 (24 : BitVec 12)) ↦ₘ arb18)
        ** ((newSp + signExtend12 (32 : BitVec 12)) ↦ₘ arb19)
        ** ((newSp + signExtend12 (40 : BitVec 12)) ↦ₘ arb20)
        ** ((newSp + signExtend12 (48 : BitVec 12)) ↦ₘ arb21)
        ** ((newSp + signExtend12 (56 : BitVec 12)) ↦ₘ arb22))
      (by pcf)
      (phmwCore_spec parentBase secBase outPtr oldOut pb sb secOfs sectionLen
        arb8 arb9 arb18 arb19 arb20 arb21 arb22 v5 v6 v7 v28 v29 v30 v31
        hfit halignP halignS hpover hsover hpvalid hsvalid hwf4 hwf8 hwfEnd)
    exact cpsTripleWithin_weaken (by xsimp) (by xsimp) hframed
  have h := abiFrame_spec (base := 0xF18) (sp0 := sp0) (ret := ret)
    (negImm := -64) (posImm := 64)
    (frame := phmwFrame) (raOfs := 0)
    (sregs := [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40),
               (.x21, 48), (.x22, 56)])
    (vals := phmwVals ret arb8 arb9 arb18 arb19 arb20 arb21 arb22)
    (vals' := phmwVals' ret parentBase secBase outPtr pb sb secOfs sectionLen arb21 arb22)
    (body := phmwBody) (bodySteps := 10 * pb.length + 60)
    (callerPre := phmwCallerPre parentBase secBase outPtr oldOut pb sb secOfs sectionLen
        v5 v6 v7 v28 v29 v30 v31)
    (callerPost := phmwCallerPost parentBase secBase outPtr pb sb secOfs sectionLen)
    (cr := phmwCr)
    (hframe := rfl)
    (hne := by decide)
    (hbound := by decide)
    (hprogBound := by decide)
    (hret := rfl)
    (halign := halign)
    (hframeRestore := by
      rw [BitVec.add_assoc,
          show signExtend12 (-64 : BitVec 12) + signExtend12 (64 : BitVec 12)
            = (0 : Word) from by decide]
      exact BitVec.add_zero sp0)
    (hcpF := by simp only [phmwCallerPre]; pcf)
    (hcpF' := by simp only [phmwCallerPost]; pcf)
    (hsub := fun a i h => h)
    (hbody := hbody)
  exact h

end ParentHeaderFrame
end SAsm
end EvmAsm.Rv64

#print axioms EvmAsm.Rv64.SAsm.ParentHeaderFrame.phmwCore_spec
#print axioms EvmAsm.Rv64.SAsm.ParentHeaderFrame.phmwFrame_spec
