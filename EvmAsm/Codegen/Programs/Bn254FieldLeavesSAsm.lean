/-
  EvmAsm.Codegen.Programs.Bn254FieldLeavesSAsm

  Verified SAsm drop-in for `bnfEq32`: 32-byte buffer equality check using
  `readAt` for the two independent read-only input buffers.

  The emitted `bnfEq32_prog` is a two-exit byte scan (BEQ completion + BNE
  break-on-mismatch), where the two exits jump to *different* result blocks
  (`LI x10,1` / `LI x10,0`). Plain `whileBreak` flattens both exits to a
  single Lend, so we model a single-exit `whileBreak` scan + post-loop
  counter-derive result (the same technique as `bnfIsZero32`).

  The two 32-byte input buffers at `a0`/`a1` are modeled as ambient
  `bytesRegion` atoms, each read through a `readAt` focus node (no
  contiguity hypothesis — the inputs may coincide or be at arbitrary
  addresses). This is the `multiReadFn` pattern from `MultiRead.lean`.
-/

import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.MultiRead
import EvmAsm.Rv64.SAsm.WhileBreakDemo
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen
open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

/-- Number of leading matching bytes between `bs0` and `bs1` (up to `n`).
    Returns `n` if all `n` bytes match, else the first mismatch index. -/
def firstDiff (bs0 bs1 : List (BitVec 8)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if firstDiff bs0 bs1 n < n then firstDiff bs0 bs1 n
      else if bs0.getD n 0 ≠ bs1.getD n 0 then n
      else n + 1

@[simp] theorem firstDiff_zero (bs0 bs1 : List (BitVec 8)) :
    firstDiff bs0 bs1 0 = 0 := rfl

@[simp] theorem firstDiff_succ (bs0 bs1 : List (BitVec 8)) (n : Nat) :
    firstDiff bs0 bs1 (n + 1) =
      (if firstDiff bs0 bs1 n < n then firstDiff bs0 bs1 n
       else if bs0.getD n 0 ≠ bs1.getD n 0 then n else n + 1) := by
  conv_lhs => rw [firstDiff]

theorem firstDiff_le (bs0 bs1 : List (BitVec 8)) : ∀ n, firstDiff bs0 bs1 n ≤ n
  | 0 => Nat.zero_le _
  | n + 1 => by
    rw [firstDiff_succ]
    by_cases h : firstDiff bs0 bs1 n < n
    · rw [if_pos h]; omega
    · rw [if_neg h]; split <;> omega

theorem firstDiff_all_eq (bs0 bs1 : List (BitVec 8)) (n : Nat)
    (h : ∀ j, j < n → bs0.getD j 0 = bs1.getD j 0) :
    firstDiff bs0 bs1 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstDiff_succ, ih (fun j hj => h j (by omega))]
    have hnn : ¬(n < n) := by omega
    rw [if_neg hnn]
    by_cases hne : bs0.getD n 0 ≠ bs1.getD n 0
    · exact absurd hne (fun h2 => h2 (h n (by omega)))
    · rw [if_neg hne]

theorem firstDiff_ne (bs0 bs1 : List (BitVec 8)) (i : Nat)
    (hprev : ∀ j, j < i → bs0.getD j 0 = bs1.getD j 0)
    (hne : bs0.getD i 0 ≠ bs1.getD i 0) :
    firstDiff bs0 bs1 (i + 1) = i := by
  rw [firstDiff_succ, firstDiff_all_eq _ _ _ hprev, if_neg (Nat.lt_irrefl _),
    if_pos hne]

-- ============================================================================
-- readAt focus relations for the two input buffers
-- ============================================================================

/-- Focus relation for reading from a0 (x10): the region bytes are `bs0`
    at the pointer pinned in `x6` (= a0 + i); the remainder holds `bs1`
    at `a1`.  At loop header `i`, `x6 = a0 + i`, so the focus is at
    `⟨x6, bs0.drop i⟩` (the bytes from index `i` onward). -/
def eqScanRoA0 (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) (i : Nat) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rst =>
    rf.get .x6 = a0 + BitVec.ofNat 64 i ∧ rob = bs0.drop i ∧
    rst = bytesRegion a1 bs1

/-- Focus relation for reading from a1 (x11): the region bytes are `bs1`
    at the pointer pinned in `x7` (= a1 + i); the remainder holds `bs0`
    at `a0`. -/
def eqScanRoA1 (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) (i : Nat) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rst =>
    rf.get .x7 = a1 + BitVec.ofNat 64 i ∧ rob = bs1.drop i ∧
    rst = bytesRegion a0 bs0

-- ============================================================================
-- Loop invariant + post
-- ============================================================================

/-- Loop invariant at header evaluation `i`: counter `x5 = 32-i`,
    cursors `x6 = a0+i`, `x7 = a1+i`, and the first `i` bytes of both
    buffers are pairwise equal. -/
def bnfEqScanInv (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ _ =>
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    rf.get .x6 = a0 + BitVec.ofNat 64 i ∧
    rf.get .x7 = a1 + BitVec.ofNat 64 i ∧
    (∀ j, j < i → bs0.getD j 0 = bs1.getD j 0) ∧
    bs0.length = 32 ∧ bs1.length = 32 ∧
    a0.toNat + 32 < 2 ^ 64 ∧ a1.toNat + 32 < 2 ^ 64

/-- `whileBreak` post: scan stopped at `firstDiff`. -/
def bnfEqScanPost (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ =>
    rf.get .x5 = BitVec.ofNat 64 (32 - firstDiff bs0 bs1 32) ∧
    rf.get .x6 = a0 + BitVec.ofNat 64 (firstDiff bs0 bs1 32) ∧
    rf.get .x7 = a1 + BitVec.ofNat 64 (firstDiff bs0 bs1 32) ∧
    bs0.length = 32 ∧ bs1.length = 32 ∧
    a0.toNat + 32 < 2 ^ 64 ∧ a1.toNat + 32 < 2 ^ 64

-- ============================================================================
-- The SAsm body
-- ============================================================================

/-- `bnf_eq32` body: init counter/cursors, scan-and-break (reading each
    buffer via `readAt`), then derive the result from the counter. -/
def bnfEq32Body (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (32 : Word), .MV .x6 .x10, .MV .x7 .x11] ;;;
  .«whileBreak» "scan" (.bne .x5 .x0) 32
    (bnfEqScanInv a0 a1 bs0 bs1) (bnfEqScanPost a0 a1 bs0 bs1)
    (.readAt "ra0" .x6 (eqScanRoA0 a0 a1 bs0 bs1 0) [.LBU .x28 .x6 (0 : BitVec 12)]
     ;;;
     .readAt "ra1" .x7 (eqScanRoA1 a0 a1 bs0 bs1 0) [.LBU .x29 .x7 (0 : BitVec 12)])
    (.bne .x28 .x29)
    (.block "next" [.ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (1 : BitVec 12),
                    .ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "res1" [.LI .x10 (1 : Word)] ;;;
  .when "clr" (.bne .x5 .x0) (.block "clr0" [.LI .x10 (0 : Word)])

-- ============================================================================
-- The Fn
-- ============================================================================

/-- Verified `Fn` for `bnf_eq32`: `x10 := if (32 bytes at a0 = 32 bytes at a1)
    then 1 else 0`.  Two read-only inputs held as ambient `bytesRegion` atoms
    (read via `readAt`); no writable region. -/
def bnfEq32Fn (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) : Fn where
  name := "bnfEq32"
  region := Region.empty
  rw := RwRegion.empty
  pre := fun rf _ A =>
    rf.get .x10 = a0 ∧ rf.get .x11 = a1 ∧
    A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1) ∧ A.pcFree
  post := fun rf _ A =>
    (rf.get .x10 = if firstDiff bs0 bs1 32 = 32 then (1 : Word) else (0 : Word)) ∧
    A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
  body := bnfEq32Body a0 a1 bs0 bs1

-- ============================================================================
-- Re-emitted drop-in program (position-independent, call-free)
-- ============================================================================

/-- Re-emitted drop-in: the SAsm-modeled `bnfEq32Body` flatten + `ret`.
    NOT byte-identical to `bnfEq32_prog` (two-exit scan → single-exit
    whileBreak + counter-derive); this is a to-be-verified functional
    drop-in that changes guest bytes. Needs EEST A/B before replacing
    the guest. -/
def bnfEq32_dropin_prog : Program :=
  (bnfEq32Body 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]

-- Position independence: no PC-relative instructions.
#guard (bnfEq32Body 0 0 [] []).flatten 0 = (bnfEq32Body 0 0 [] []).flatten 0x80000000

-- The drop-in body is call-free (no JAL/callRegS).
#guard (bnfEq32Body 0 0 [] []).callFree = true

-- ============================================================================

end EvmAsm.Codegen
