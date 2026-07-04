/-
  EvmAsm.Codegen.Programs.SwdMinimalCopySAsm

  Bead evm-asm-4ch8f.12.9 — `swd_minimal_copy`: **verified SAsm port**
  (`swdMinimalCopyFn_spec`, classical-3 axioms).

  Both former blockers were resolved and merged to main — `.67`
  (`blockAt`/`focus_rwAtom`, the `*a3` store) and `.huy8w`
  (`Stmt.whileBreak`, the strip loop's mid-loop early exit) — and the port
  composes the three verified phases: `whileBreak` strip (the `scanNzFn`
  shape), a `blockAt` `*a3` store discharged by `focus_rwAtom`, and a
  `«while»` copy (the `SwrRevLeBe` shape).  Byte-identity to the guest
  routine is pinned (`swdMinimalCopyBody_eq_prog`).

  `a0=src, a1=len, a2=dst, a3=len-out ptr`.  Strip the leading zero bytes of
  `src[0..len)`, copy the remainder into `dst`, and write the remaining length
  to `*a3`.  Assembled from three primitives:

  1. **strip loop** (`whileBreak`, bead `.huy8w`): a scan with a mid-loop
     early exit at the first non-zero byte — the shape of `WhileBreakDemo.scanNzFn`.
     Exit: `x5 = src + numLeadingZeros`, `x6 = strippedLen = len − numLeadingZeros`.
  2. **`SD x6 → 0(a3)`** (`blockAt` on the `a3` dword atom, bead `.67`):
     discharged by `focus_rwAtom` on the `⌜RwRegion.wf ⟨a3,8⟩⌝ ** bytesRegion a3 w`
     contract; writes region B, framing the primary `rw` (`dst`).
  3. **copy loop** (`«while»`, the `.12` copy shape): copy `strippedLen`
     bytes from the stripped source into `dst`.

  Post: `dst = strippedBytes bs len` ∧ `*a3 = strippedLen bs len` — both
  regions pinned as functions of the input (no ∃-escape).  The two writable
  regions are disjoint **structurally** via `**` (the `.67` design); `src ≠ dst`
  (`hdisj`) only routes the `LBU`s to the read-only region past the arithmetic
  `inRw` test.  `SD` is an 8-byte access, so `a3` is 8-aligned in the pre (the
  `RwRegion.wf ⟨a3,8⟩` fact, carried in the ambient assertion).

  Byte-identity is pinned: the structured body flattens with the `ret`
  epilogue to exactly `swdMinimalCopy_prog` (all 19 instructions, incl. the
  strip break `BNE +16` past `JAL -20` and the copy `JAL -24`).
-/

import EvmAsm.Codegen.Programs.SystemWrites
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.WhileBreakDemo
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SwdMinimalCopySAsm

/-- Number of leading zero bytes of `src[0..len)` (clamped to `len`). -/
def numLeadingZeros (bs : List (BitVec 8)) (len : Nat) : Nat :=
  ((bs.take len).takeWhile (· == 0)).length

/-- The stripped (leading-zeros-removed) source bytes: `src[s..len)`. -/
def strippedBytes (bs : List (BitVec 8)) (len : Nat) : List (BitVec 8) :=
  (bs.take len).drop (numLeadingZeros bs len)

/-- The output length written to `*a3`: `len - (leading zeros)`. -/
def strippedLen (bs : List (BitVec 8)) (len : Nat) : Nat :=
  len - numLeadingZeros bs len

-- Sanity pins for the ghost spec (the intended functional behaviour).
example : numLeadingZeros [0, 0, 7, 0, 3] 5 = 2 := by decide
example : strippedBytes [0, 0, 7, 0, 3] 5 = [7, 0, 3] := by decide
example : strippedLen [0, 0, 7, 0, 3] 5 = 3 := by decide
example : numLeadingZeros [0, 0, 0] 3 = 3 := by decide      -- all-zero ⇒ empty
example : strippedBytes [0, 0, 0] 3 = [] := by decide
example : strippedLen [0, 0, 0] 3 = 0 := by decide

/-- Bridge to the recursive `nlz` of `WhileBreakDemo`, whose scan lemmas
    (`nlz_le`/`nlz_continue`/`nlz_break`) we reuse for the strip loop. -/
theorem numLeadingZeros_eq_nlz (bs : List (BitVec 8)) (len : Nat) :
    numLeadingZeros bs len = WhileBreakDemo.nlz bs len := by
  induction bs generalizing len with
  | nil => cases len <;> simp [numLeadingZeros, WhileBreakDemo.nlz]
  | cons b bs ih =>
      cases len with
      | zero => simp [numLeadingZeros, WhileBreakDemo.nlz]
      | succ n =>
          simp only [numLeadingZeros, List.take_succ_cons, List.takeWhile_cons,
            WhileBreakDemo.nlz]
          by_cases hb : b = 0
          · simp only [hb, beq_self_eq_true, if_true, List.length_cons]
            have := ih n
            simp only [numLeadingZeros] at this
            omega
          · rw [show (b == 0) = false from by simpa using hb, if_neg hb]
            simp

theorem numLeadingZeros_le (bs : List (BitVec 8)) (len : Nat) :
    numLeadingZeros bs len ≤ len := by
  rw [numLeadingZeros_eq_nlz]; exact WhileBreakDemo.nlz_le bs len

/-- The `k`-th copied byte: source byte at `numLeadingZeros + k`. -/
def copyByte (bs : List (BitVec 8)) (len k : Nat) : BitVec 8 :=
  bs.getD (numLeadingZeros bs len + k) 0

/-- Copy loop window: first `j` output bytes are the stripped prefix, the rest
    is the untouched tail of the original `dst` buffer. -/
def copyWin (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8)) (j : Nat) :
    List (BitVec 8) :=
  (List.range j).map (copyByte bs len) ++ orig.drop j

theorem copyWin_zero (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8)) :
    copyWin bs len orig 0 = orig := by simp [copyWin]

theorem length_copyWin (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8))
    (j : Nat) (h : orig.length = strippedLen bs len) (hj : j ≤ strippedLen bs len) :
    (copyWin bs len orig j).length = strippedLen bs len := by
  simp only [copyWin, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

theorem copyWin_step (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8))
    (j : Nat) (h : orig.length = strippedLen bs len) (hj : j < strippedLen bs len) :
    setBytes (copyWin bs len orig j) j [copyByte bs len j] = copyWin bs len orig (j + 1) := by
  rw [setBytes_singleton]
  have hpre : ((List.range j).map (copyByte bs len)).length = j := by simp
  have hdrop : orig.drop j = orig[j] :: orig.drop (j + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [copyWin, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero]

theorem copyWin_len_eq (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8))
    (h : orig.length = strippedLen bs len) (hlen : len ≤ bs.length) :
    copyWin bs len orig (strippedLen bs len) = strippedBytes bs len := by
  have hnil : orig.drop (strippedLen bs len) = [] := by simp [h]
  have hnlz : numLeadingZeros bs len ≤ len := numLeadingZeros_le bs len
  simp only [copyWin, hnil, List.append_nil]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, strippedBytes, List.length_drop,
      List.length_take, Nat.min_eq_left hlen]
    rfl
  · intro k hk1 hk2
    simp only [List.length_map, List.length_range] at hk1
    simp only [List.getElem_map, List.getElem_range, copyByte, strippedBytes,
      List.getElem_drop, List.getElem_take, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show numLeadingZeros bs len + k < bs.length by
        simp only [strippedLen] at hk1; omega), Option.getD_some]

/-- Region B (the output-length dword) as an ambient assertion atom. -/
def regB (a3 : Word) (w : List (BitVec 8)) : Assertion :=
  ⌜RwRegion.wf ⟨a3, 8⟩⌝ ** bytesRegion a3 w

-- ============================================================================
-- Body pieces
-- ============================================================================

def sinitBlock : List Instr := [.MV .x5 .x10, .MV .x6 .x11]
def loadBlock  : List Instr := [.LBU .x7 .x5 (0 : BitVec 12)]
def decBlock   : List Instr := [.ADDI .x5 .x5 (1 : BitVec 12), .ADDI .x6 .x6 (-1 : BitVec 12)]
def sdBlock    : List Instr := [.SD .x13 .x6 (0 : BitVec 12)]
def cinitBlock : List Instr := [.MV .x28 .x12, .LI .x29 (0 : Word)]
def cstepBlock : List Instr :=
  [.ADD .x30 .x5 .x29, .LBU .x31 .x30 (0 : BitVec 12),
   .ADD .x7 .x28 .x29, .SB .x7 .x31 (0 : BitVec 12), .ADDI .x29 .x29 (1 : BitVec 12)]

/-- Strip-loop invariant at header evaluation `i`. -/
def stripInv (src dst a3 : Word) (bs orig w2 : List (BitVec 8)) (len : Nat) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = src + BitVec.ofNat 64 i
    ∧ rf.get .x6 = BitVec.ofNat 64 (len - i)
    ∧ rf.get .x12 = dst ∧ rf.get .x13 = a3
    ∧ i ≤ numLeadingZeros bs len
    ∧ ws = orig ∧ A = regB a3 w2

/-- Strip-loop post (both exits establish it): cursor at the first non-zero
    byte, remaining = `strippedLen`, buffers untouched. -/
def stripPost (src dst a3 : Word) (bs orig w2 : List (BitVec 8)) (len : Nat) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf ws A =>
    rf.get .x5 = src + BitVec.ofNat 64 (numLeadingZeros bs len)
    ∧ rf.get .x6 = BitVec.ofNat 64 (strippedLen bs len)
    ∧ rf.get .x12 = dst ∧ rf.get .x13 = a3
    ∧ ws = orig ∧ A = regB a3 w2

/-- Focus relation of the `SD` store: window = region B's bytes at `a3`
    (pinned in `x13`), remainder = region B's wf fact. -/
def lenoutWinR (a3 : Word) (w2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    rf.get .x13 = a3 ∧ win = w2 ∧ rest = ⌜RwRegion.wf ⟨a3, 8⟩⌝

/-- Copy-loop invariant at header evaluation `j`. -/
def copyInv (src dst a3 : Word) (bs orig : List (BitVec 8)) (len : Nat) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun j rf ws A =>
    rf.get .x5 = src + BitVec.ofNat 64 (numLeadingZeros bs len)
    ∧ rf.get .x6 = BitVec.ofNat 64 (strippedLen bs len)
    ∧ rf.get .x28 = dst
    ∧ rf.get .x29 = BitVec.ofNat 64 j
    ∧ j ≤ strippedLen bs len
    ∧ ws = copyWin bs len orig j
    ∧ A = regB a3 (dwordBytes (BitVec.ofNat 64 (strippedLen bs len)))

def swdMinimalCopyBody (src dst a3 : Word) (bs orig w2 : List (BitVec 8)) (len : Nat) : Stmt :=
  .block "sinit" sinitBlock ;;;
  .«whileBreak» "strip" (.bne .x6 .x0) len (stripInv src dst a3 bs orig w2 len)
    (stripPost src dst a3 bs orig w2 len)
    (.block "load" loadBlock) (.bne .x7 .x0) (.block "dec" decBlock) ;;;
  .blockAt "lenout" .x13 (lenoutWinR a3 w2) sdBlock ;;;
  .block "cinit" cinitBlock ;;;
  .«while» "copy" (.bne .x29 .x6) len (copyInv src dst a3 bs orig len)
    (.block "cstep" cstepBlock)

/-- The verified function. -/
def swdMinimalCopyFn (src dst a3 : Word) (bs orig w2 : List (BitVec 8)) (len : Nat) : Fn where
  name := "swdMinimalCopy"
  region := ⟨src, bs⟩
  rw := ⟨dst, strippedLen bs len⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len
    ∧ rf.get .x12 = dst ∧ rf.get .x13 = a3
    ∧ ws = orig ∧ orig.length = strippedLen bs len
    ∧ len ≤ bs.length ∧ src.toNat + len < 2 ^ 64
    ∧ dst.toNat + strippedLen bs len < 2 ^ 64
    ∧ (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    ∧ w2.length = 8 ∧ A = regB a3 w2
  post := fun _ ws A =>
    ws = strippedBytes bs len
    ∧ A = regB a3 (dwordBytes (BitVec.ofNat 64 (strippedLen bs len)))
  body := swdMinimalCopyBody src dst a3 bs orig w2 len

/-- **Byte-identity (machine-checked).** -/
theorem swdMinimalCopyBody_eq_prog :
    (swdMinimalCopyBody 0 0 0 [] [] [] 0).flatten 0 ++ [Instr.JALR .x0 .x1 0]
      = swdMinimalCopy_prog := by decide

theorem swdMinimalCopyBody_pic :
    (swdMinimalCopyBody 0 0 0 [] [] [] 0).flatten 0
      = (swdMinimalCopyBody 0 0 0 [] [] [] 0).flatten 0x80000000 := by decide

#guard swdMinimalCopy_prog.length = 19
#guard (swdMinimalCopyBody 0 0 0 [] [] [] 0).flatten 0 ++ [Instr.JALR .x0 .x1 0]
  = swdMinimalCopy_prog

-- ============================================================================
-- Per-phase engine lemmas
-- ============================================================================

/-- An `LBU` that misses the writable window reads the read-only region. -/
private theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF; dsimp only [aluSem, loadSem]; rw [if_neg h]

/-- A load from address `src + m` (`m < len`) misses the writable window
    `⟨dst, ·⟩` when the two regions are disjoint (`hdisj`). -/
theorem load_miss (src dst : Word) (bs : List (BitVec 8)) (len m : Nat)
    (ws : List (BitVec 8)) (rs1 : Reg) (rf : RegFile)
    (hrs1 : rf.get rs1 = src + BitVec.ofNat 64 m) (hm : m < len)
    (hws : ws.length = strippedLen bs len)
    (hsrc : src.toNat + len < 2 ^ 64) (hdst : dst.toNat + strippedLen bs len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) :
    ¬ inRw dst ws (rf.get rs1 + signExtend12 (0 : BitVec 12)) 1 := by
  have hsl : strippedLen bs len ≤ len := by simp only [strippedLen]; omega
  unfold inRw
  rw [hrs1, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide, hws]
  have hm2 : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega
  have hsub : (src + BitVec.ofNat 64 m + 0 - dst).toNat
      = (src.toNat + m + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
    rw [show src + BitVec.ofNat 64 m + 0 = src + BitVec.ofNat 64 m from by bv_omega,
      BitVec.toNat_sub, BitVec.toNat_add, hm2]; congr 1; omega
  rw [hsub]; rcases hdisj with hd | hd <;> omega

/-- The byte at `src + m` in the read-only region is `bs.getD m 0`. -/
theorem byteAt_src (src : Word) (bs : List (BitVec 8)) (m : Nat) (rf : RegFile) (rs1 : Reg)
    (hrs1 : rf.get rs1 = src + BitVec.ofNat 64 m) (hm : src.toNat + m < 2 ^ 64) :
    (Region.mk src bs).byteAt (rf.get rs1 + signExtend12 (0 : BitVec 12)) = bs.getD m 0 := by
  unfold Region.byteAt
  rw [hrs1, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; congr 1
  have hm2 : (BitVec.ofNat 64 m).toNat = m := by rw [BitVec.toNat_ofNat]; omega
  bv_omega

/-- **`loadBlock` engine**: one strip `LBU`, resolved. -/
theorem loadBlock_engine (src dst : Word) (bs : List (BitVec 8)) (len i : Nat)
    (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = src + BitVec.ofNat 64 i) (hi : i < len)
    (hws : ws.length = strippedLen bs len)
    (hsrc : src.toNat + len < 2 ^ 64) (hdst : dst.toNat + strippedLen bs len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) :
    execBlock (Region.mk src bs) dst rf ws loadBlock
      = (rf.set .x7 (BitVec.zeroExtend 64 (bs.getD i 0)), ws) := by
  rw [loadBlock, execBlock_cons,
    execInstrRF_lbu_ro _ _ _ _ _ _ _ (load_miss src dst bs len i ws .x5 rf hx5 hi hws hsrc hdst hdisj),
    byteAt_src src bs i rf .x5 hx5 (by omega), execBlock_nil]

/-- Register file after the `decBlock`. -/
def decRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x5 (rf.get .x5 + signExtend12 (1 : BitVec 12))
  r1.set .x6 (r1.get .x6 + signExtend12 (-1 : BitVec 12))

/-- **`decBlock` engine**: the two `ADDI`s, resolved (no memory). -/
theorem decBlock_engine (reg : Region) (rwb : Word) (rf : RegFile) (ws : List (BitVec 8)) :
    execBlock reg rwb rf ws decBlock = (decRf rf, ws) := by
  rw [decBlock, execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]; rfl

theorem decRf_get_x5 (rf : RegFile) :
    (decRf rf).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold decRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), RegFile.get_set_self _ _ _ (by decide)]

theorem decRf_get_x6 (rf : RegFile) :
    (decRf rf).get .x6 = rf.get .x6 + signExtend12 (-1 : BitVec 12) := by
  unfold decRf
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5)]

theorem decRf_get_other (rf : RegFile) (r : Reg) (h5 : r ≠ .x5) (h6 : r ≠ .x6) :
    (decRf rf).get r = rf.get r := by
  unfold decRf
  rw [RegFile.get_set_ne _ _ _ _ h6, RegFile.get_set_ne _ _ _ _ h5]

/-- Register file after one `cstepBlock` (given the loaded byte). -/
def cstepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r0 := rf.set .x30 (rf.get .x5 + rf.get .x29)
  let r1 := r0.set .x31 (b.zeroExtend 64)
  let r2 := r1.set .x7 (r1.get .x28 + r1.get .x29)
  r2.set .x29 (r2.get .x29 + signExtend12 (1 : BitVec 12))

theorem cstepRf_get_x29 (rf : RegFile) (b : BitVec 8) :
    (cstepRf rf b).get .x29 = rf.get .x29 + signExtend12 (1 : BitVec 12) := by
  unfold cstepRf
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30)]

theorem cstepRf_get_of (rf : RegFile) (b : BitVec 8) (r : Reg)
    (h30 : r ≠ .x30) (h31 : r ≠ .x31) (h7 : r ≠ .x7) (h29 : r ≠ .x29) :
    (cstepRf rf b).get r = rf.get r := by
  unfold cstepRf
  rw [RegFile.get_set_ne _ _ _ _ h29, RegFile.get_set_ne _ _ _ _ h7,
    RegFile.get_set_ne _ _ _ _ h31, RegFile.get_set_ne _ _ _ _ h30]

/-- **`cstepBlock` engine**: one copy iteration, resolved.  Loads `src[nlz+j]`
    from the read-only region (missing the writable window) and stores it at
    `dst[j]` (index `j` of the writable window). -/
theorem cstepBlock_engine (src dst : Word) (bs : List (BitVec 8)) (len j : Nat)
    (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = src + BitVec.ofNat 64 (numLeadingZeros bs len))
    (hx28 : rf.get .x28 = dst) (hx29 : rf.get .x29 = BitVec.ofNat 64 j)
    (hj : j < strippedLen bs len) (hws : ws.length = strippedLen bs len)
    (hsrc : src.toNat + len < 2 ^ 64) (hdst : dst.toNat + strippedLen bs len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) :
    execBlock (Region.mk src bs) dst rf ws cstepBlock
      = (cstepRf rf (bs.getD (numLeadingZeros bs len + j) 0),
         setBytes ws j [bs.getD (numLeadingZeros bs len + j) 0]) := by
  have hnlz : numLeadingZeros bs len ≤ len := numLeadingZeros_le bs len
  have hsldef : strippedLen bs len = len - numLeadingZeros bs len := rfl
  have hsl : strippedLen bs len ≤ len := by omega
  have hj2 : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  -- x30 (after ADD x30 x5 x29) = src + (nlz + j)
  have hx30 : (rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30
      = src + BitVec.ofNat 64 (numLeadingZeros bs len + j) := by
    rw [RegFile.get_set_self _ _ _ (by decide), hx5, hx29]
    have hnn : (BitVec.ofNat 64 (numLeadingZeros bs len)).toNat = numLeadingZeros bs len := by
      rw [BitVec.toNat_ofNat]; omega
    bv_omega
  have hljlt : numLeadingZeros bs len + j < len := by omega
  have hmiss := load_miss src dst bs len (numLeadingZeros bs len + j) ws .x30
    (rf.set .x30 (rf.get .x5 + rf.get .x29)) hx30 hljlt hws hsrc hdst hdisj
  have hbyte := byteAt_src src bs (numLeadingZeros bs len + j)
    (rf.set .x30 (rf.get .x5 + rf.get .x29)) .x30 hx30 (by omega)
  have hjb : j < 2 ^ 64 := by omega
  rw [cstepBlock, execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss, hbyte]
  dsimp only
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ j
    (by
      rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hx28, hx29,
        show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      have hj2' : (BitVec.ofNat 64 j).toNat = j := hj2
      bv_omega)]
  dsimp only
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  refine Prod.ext ?_ ?_
  · rfl
  · dsimp only
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x31 ≠ .x7),
      RegFile.get_set_self _ _ _ (by decide : (Reg.x31 : Reg) ≠ .x0), truncate_zeroExtend_byte]

-- ============================================================================
-- The verified triple
-- ============================================================================

theorem swdMinimalCopyFn_spec (src dst a3 : Word) (bs orig w2 : List (BitVec 8)) (len : Nat)
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, strippedLen bs len⟩)
    (hbwf : RwRegion.wf ⟨a3, 8⟩) (hw2 : w2.length = 8)
    (horig : orig.length = strippedLen bs len)
    (hlen : len ≤ bs.length) (hsrc : src.toNat + len < 2 ^ 64)
    (hdst : dst.toNat + strippedLen bs len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (base : Word) :
    (swdMinimalCopyFn src dst a3 bs orig w2 len).Spec base := by
  have hnlz : numLeadingZeros bs len ≤ len := numLeadingZeros_le bs len
  have hsldef : strippedLen bs len = len - numLeadingZeros bs len := rfl
  have hsl : strippedLen bs len ≤ len := by omega
  have hRw : (swdMinimalCopyFn src dst a3 bs orig w2 len).rw.base = dst := rfl
  have hReg : (swdMinimalCopyFn src dst a3 bs orig w2 len).region = (⟨src, bs⟩ : Region) := rfl
  have hRwlen : (swdMinimalCopyFn src dst a3 bs orig w2 len).rw.len = strippedLen bs len := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  -- ===== strip loop (whileBreak) =====
  case swdMinimalCopy.strip.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, ⟨hx10, hx11, hx12, hx13, hwso, -, -, -, -, -, -, hA⟩, rfl, rfl⟩
    simp only [sinitBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, Nat.zero_le _, hwso, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide), hx10]; simp
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]; simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]; exact hx12
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x5)]; exact hx13
  case swdMinimalCopy.strip.inv_step =>
    rintro i hi rf' ws' A'
      ⟨rfa, wsa, hwsa, ⟨⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrfa, hwsaeq⟩, hnbreak⟩, hrf', hwseq⟩
    obtain ⟨hx5, hx6, hx12, hx13, hle, hwso, hA⟩ := hinv
    have hwsblen : wsb.length = strippedLen bs len := by rw [hwsb, hRwlen]
    have hilt : i < len := by
      rcases Nat.lt_or_ge i len with h | h
      · exact h
      · exact absurd (by rw [hx6, show len - i = 0 from by omega]; rfl : rfb.get .x6 = rfb.get .x0) hg
    rw [hReg, hRw, loadBlock_engine src dst bs len i rfb wsb hx5 hilt hwsblen hsrc hdst hdisj]
      at hrfa hwsaeq
    subst hrfa; subst hwsaeq
    have hz : bs.getD i 0 = 0 := by
      have hne : (rfb.set .x7 (BitVec.zeroExtend 64 (bs.getD i 0))).get .x7
          = (rfb.set .x7 (BitVec.zeroExtend 64 (bs.getD i 0))).get .x0 := by
        by_contra h; exact hnbreak h
      rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x0 ≠ .x7), show rfb.get .x0 = 0 from rfl] at hne
      bv_omega
    rw [decBlock_engine] at hrf' hwseq
    subst hrf'; subst hwseq
    refine ⟨?_, ?_, ?_, ?_, ?_, hwso, hA⟩
    · rw [decRf_get_x5, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), hx5,
        show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [decRf_get_x6, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7), hx6,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [decRf_get_other _ _ (by decide) (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7)]; exact hx12
    · rw [decRf_get_other _ _ (by decide) (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]; exact hx13
    · rw [numLeadingZeros_eq_nlz]
      refine WhileBreakDemo.nlz_continue bs len i hilt hlen hz ?_
      rw [← numLeadingZeros_eq_nlz]; exact hle
  case swdMinimalCopy.strip.exhausted =>
    rintro rf ws A ⟨-, hx6, -, -, -, -, -⟩
    intro hc; apply hc
    rw [hx6, show len - len = 0 from by omega]; rfl
  case swdMinimalCopy.strip.guard_exit =>
    rintro i hile rf ws A ⟨hx5, hx6, hx12, hx13, hle, hwso, hA⟩ hng
    have hil : i = len := by
      by_contra hne; apply hng
      show rf.get .x6 ≠ rf.get .x0
      rw [hx6, show rf.get .x0 = 0 from rfl]
      intro h
      have := congrArg (fun w : Word => w.toNat) h
      simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega
    have hnlzlen : numLeadingZeros bs len = len := by omega
    refine ⟨?_, ?_, hx12, hx13, hwso, hA⟩
    · rw [hx5, hnlzlen, hil]
    · rw [hx6, hil]; congr 1; omega
  case swdMinimalCopy.strip.break =>
    rintro i hi rf' ws' A' ⟨rfb, wsb, hwsb, ⟨hinv, hg⟩, hrf', hwseq⟩ hbreak
    obtain ⟨hx5, hx6, hx12, hx13, hle, hwso, hA⟩ := hinv
    have hwsblen : wsb.length = strippedLen bs len := by rw [hwsb, hRwlen]
    rw [hReg, hRw, loadBlock_engine src dst bs len i rfb wsb hx5 hi hwsblen hsrc hdst hdisj]
      at hrf' hwseq
    subst hrf'; subst hwseq
    have hnz : bs.getD i 0 ≠ 0 := by
      have hne : (rfb.set .x7 (BitVec.zeroExtend 64 (bs.getD i 0))).get .x7
          ≠ (rfb.set .x7 (BitVec.zeroExtend 64 (bs.getD i 0))).get .x0 := hbreak
      rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x0 ≠ .x7), show rfb.get .x0 = 0 from rfl] at hne
      intro hzz; exact hne (by rw [hzz]; rfl)
    have hieq : i = numLeadingZeros bs len := by
      rw [numLeadingZeros_eq_nlz]
      exact WhileBreakDemo.nlz_break bs len i (by rw [← numLeadingZeros_eq_nlz]; exact hle) hnz
    refine ⟨?_, ?_, ?_, ?_, hwso, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), hx5, hieq]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7), hx6, hieq]; congr 1
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7)]; exact hx12
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]; exact hx13
  case swdMinimalCopy.strip.before.load.mem =>
    rintro rf ws A hws ⟨i, hi, ⟨hx5, hx6, hx12, hx13, hle, hwso, hA⟩, hg⟩
    have hwslen : ws.length = strippedLen bs len := by rw [hws, hRwlen]
    have haddr : ((rf.get .x5 + signExtend12 (0 : BitVec 12)) - src).toNat = i := by
      rw [hx5, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      have hti : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    simp only [loadBlock, blockVCs, loadSem, and_true]
    rw [hReg, hRw, if_neg (load_miss src dst bs len i ws .x5 rf hx5 hi hwslen hsrc hdst hdisj)]
    refine ⟨one_dvd _, ?_⟩
    show ((rf.get .x5 + signExtend12 (0 : BitVec 12)) - src).toNat + 1 ≤ bs.length
    omega
  -- ===== SD → a3 (blockAt on region B) =====
  case swdMinimalCopy.lenout.focus =>
    rintro rf ws A ⟨hx5, hx6, hx12, hx13, hwso, hA⟩ hApc hp hhp
    refine ⟨w2, ⌜RwRegion.wf ⟨a3, 8⟩⌝, ⟨hx13, rfl, rfl⟩, ?_, pcFree_pure, ?_⟩
    · rw [hx13]
      have hh := hA ▸ hhp
      rw [regB] at hh
      xperm_hyp hh
    · rw [hx13, hw2]; exact hbwf
  case swdMinimalCopy.lenout.mem =>
    rintro rf ws A win rest hws hreach ⟨hx13, hwin, hrest⟩ hsat
    have haddr : (rf.get .x13 + signExtend12 (0 : BitVec 12) - rf.get .x13).toNat = 0 := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
    have hwl : win.length = 8 := by rw [hwin, hw2]
    simp only [sdBlock, blockVCs, storeSem, inRw, and_true]
    refine ⟨?_, ?_⟩
    · rw [haddr, hwl]
    · rw [haddr]; exact ⟨0, rfl⟩
  -- ===== copy loop (while) =====
  case swdMinimalCopy.copy.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hbA, rfl, rfl⟩
    obtain ⟨rfB, AB, winB, restB, hws₀', hstrip, hsatB, ⟨hx13B, hwinB, hrestB⟩, hrf₀, hAeq⟩ := hbA
    obtain ⟨hx5B, hx6B, hx12B, hx13B', hwsoB, hAB⟩ := hstrip
    have hsdws : (execBlock (⟨src, bs⟩ : Region) a3 rfB w2 sdBlock).2
        = dwordBytes (rfB.get .x6) := by
      rw [sdBlock, execBlock_cons,
        execInstrRF_sd_dword _ _ _ _ _ _ _ 0
          (by rw [hx13B, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega),
        execBlock_nil, setBytes_dword_full _ _ hw2]
    have hrf₀' : rf₀ = rfB := by
      rw [hrf₀, sdBlock, execBlock_cons, execBlock_nil]; rfl
    subst hrf₀'
    rw [hReg, hx13B, hwinB, hsdws, hrestB, hx6B] at hAeq
    simp only [cinitBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, Nat.zero_le _, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]; exact hx5B
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]; exact hx6B
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
        RegFile.get_set_self _ _ _ (by decide)]; exact hx12B
    · rw [RegFile.get_set_self _ _ _ (by decide)]; rfl
    · rw [copyWin_zero]; exact hwsoB
    · rw [hAeq, regB, sepConj_comm']
  case swdMinimalCopy.copy.inv_step =>
    rintro j hj rf' ws' A' ⟨rf₀, ws₀, hws₀, ⟨hcinv, hcond⟩, rfl, rfl⟩
    obtain ⟨hx5, hx6, hx28, hx29, hjle, hwsw, hA⟩ := hcinv
    have hwslen : ws₀.length = strippedLen bs len := by
      rw [hwsw]; exact length_copyWin bs len orig j horig hjle
    have hjlt : j < strippedLen bs len := by
      rcases Nat.lt_or_ge j (strippedLen bs len) with h | h
      · exact h
      · exact absurd (by rw [hx29, hx6]; congr 1; omega : rf₀.get .x29 = rf₀.get .x6) hcond
    rw [hReg, hRw, cstepBlock_engine src dst bs len j rf₀ ws₀ hx5 hx28 hx29 hjlt hwslen hsrc hdst hdisj]
    refine ⟨?_, ?_, ?_, ?_, by omega, ?_, hA⟩
    · rw [cstepRf_get_of _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hx5
    · rw [cstepRf_get_of _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hx6
    · rw [cstepRf_get_of _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hx28
    · rw [cstepRf_get_x29, hx29, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      have h1 : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (j + 1)).toNat = j + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwsw, show bs.getD (numLeadingZeros bs len + j) 0 = copyByte bs len j from rfl]
      exact copyWin_step bs len orig j horig hjlt
  case swdMinimalCopy.copy.exhausted =>
    rintro rf ws A ⟨-, hx6, -, hx29, hjle, -, -⟩
    intro hc; apply hc
    rw [hx29, hx6]; congr 1; omega
  case swdMinimalCopy.copy.body.cstep.mem =>
    rintro rf ws A hws ⟨j, hj, ⟨hx5, hx6, hx28, hx29, hjle, hwsw, hA⟩, hcond⟩
    have hwslen : ws.length = strippedLen bs len := by rw [hws, hRwlen]
    have hjlt : j < strippedLen bs len := by
      rcases Nat.lt_or_ge j (strippedLen bs len) with h | h
      · exact h
      · exact absurd (by rw [hx29, hx6]; congr 1; omega : rf.get .x29 = rf.get .x6) hcond
    have hjj : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
    have hx30 : (rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30
        = src + BitVec.ofNat 64 (numLeadingZeros bs len + j) := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx5, hx29]
      have hnn : (BitVec.ofNat 64 (numLeadingZeros bs len)).toNat = numLeadingZeros bs len := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hljlt : numLeadingZeros bs len + j < len := by omega
    have hmiss := load_miss src dst bs len (numLeadingZeros bs len + j) ws .x30
      (rf.set .x30 (rf.get .x5 + rf.get .x29)) hx30 hljlt hwslen hsrc hdst hdisj
    have haddrL : ((rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30
        + signExtend12 (0 : BitVec 12) - src).toNat = numLeadingZeros bs len + j := by
      rw [hx30, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      have : (BitVec.ofNat 64 (numLeadingZeros bs len + j)).toNat = numLeadingZeros bs len + j := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    -- store address, after ADD x30, LBU x31, ADD x7 : x7 = dst + j
    have haddrS : ∀ v : Word,
        ((((rf.set .x30 (rf.get .x5 + rf.get .x29)).set .x31 v).get .x28
          + ((rf.set .x30 (rf.get .x5 + rf.get .x29)).set .x31 v).get .x29)
          + signExtend12 (0 : BitVec 12) - dst).toNat = j := by
      intro v
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hx28, hx29,
        show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    rw [hReg, hRw, cstepBlock]
    -- ADD x30 (no mem)
    refine ⟨trivial, ?_⟩
    rw [show execInstrRF (⟨src, bs⟩ : Region) dst rf ws (.ADD .x30 .x5 .x29)
        = (rf.set .x30 (rf.get .x5 + rf.get .x29), ws) from rfl]
    -- LBU x31 x30 (routes to RO)
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hmiss]
      refine ⟨one_dvd _, ?_⟩
      show ((rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30 + signExtend12 (0 : BitVec 12)
        - src).toNat + 1 ≤ bs.length
      rw [haddrL]; omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss]
      -- ADD x7 (no mem)
      refine ⟨trivial, ?_⟩
      rw [show execInstrRF (⟨src, bs⟩ : Region) dst
          ((rf.set .x30 (rf.get .x5 + rf.get .x29)).set .x31
            (BitVec.zeroExtend 64 ((⟨src, bs⟩ : Region).byteAt
              ((rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30 + signExtend12 0)))) ws
          (.ADD .x7 .x28 .x29)
          = (((rf.set .x30 (rf.get .x5 + rf.get .x29)).set .x31
              (BitVec.zeroExtend 64 ((⟨src, bs⟩ : Region).byteAt
                ((rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30 + signExtend12 0)))).set .x7
              (((rf.set .x30 (rf.get .x5 + rf.get .x29)).set .x31
                (BitVec.zeroExtend 64 ((⟨src, bs⟩ : Region).byteAt
                  ((rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30 + signExtend12 0)))).get .x28
                + ((rf.set .x30 (rf.get .x5 + rf.get .x29)).set .x31
                  (BitVec.zeroExtend 64 ((⟨src, bs⟩ : Region).byteAt
                    ((rf.set .x30 (rf.get .x5 + rf.get .x29)).get .x30 + signExtend12 0)))).get .x29),
              ws) from rfl]
      -- SB x7 x31 (into region A at index j), then ADDI x29 (no mem)
      refine ⟨⟨?_, ?_⟩, trivial, trivial⟩
      · show inRw dst ws _ 1
        rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0)]
        unfold inRw
        rw [haddrS, hwslen]; omega
      · rw [RegFile.get_set_self _ _ _ (by decide : (Reg.x7 : Reg) ≠ .x0), haddrS]
        exact one_dvd _
  case swdMinimalCopy.post =>
    rintro rf ws A ⟨⟨j, hjfuel, hx5, hx6, hx28, hx29, hjle, hwsw, hA⟩, hncond⟩
    have hjeq : j = strippedLen bs len := by
      have hne : rf.get .x29 = rf.get .x6 := by by_contra h; exact hncond h
      rw [hx29, hx6] at hne
      have := congrArg (fun w : Word => w.toNat) hne
      simp only [BitVec.toNat_ofNat] at this; omega
    subst hjeq
    exact ⟨by rw [hwsw]; exact copyWin_len_eq bs len orig horig hlen, hA⟩

end SwdMinimalCopySAsm

end EvmAsm.Codegen
