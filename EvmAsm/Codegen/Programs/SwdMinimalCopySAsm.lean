/-
  EvmAsm.Codegen.Programs.SwdMinimalCopySAsm

  Bead evm-asm-4ch8f.12.9 — `swd_minimal_copy`: SAsm port.

  ## Status: faithful `Fn` contract stated + byte-identity machine-checked;
  the `Fn.Spec` proof (`swdMinimalCopyFn.Spec`) is the remaining work item.
  Both former blockers are gone — `.67` (`blockAt`/`focus_rwAtom`, the `*a3`
  store) and `.huy8w` (`Stmt.whileBreak`, the strip loop's mid-loop early
  exit) — and the composed structure flattens byte-for-byte to the guest
  routine (`swdMinimalCopyBody_eq_prog`).  The `Fn` below states the intended
  contract (`swdMinimalCopyFn.pre`/`.post`); proving `swdMinimalCopyFn.Spec`
  composes the three verified phase-templates (`scanNzFn` strip, `MultiRw`
  `blockAt` store, `SwrRevLeBe` `«while»` copy).

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

end SwdMinimalCopySAsm

end EvmAsm.Codegen
