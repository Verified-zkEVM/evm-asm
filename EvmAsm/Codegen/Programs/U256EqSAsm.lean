/-
  EvmAsm.Codegen.Programs.U256EqSAsm

  SAsm model for `u256_eq` (bead evm-asm-i6mdy.1): compare two
  32-byte big-endian buffers at `a0`/`a1` and return `a0 = 1` iff they are
  byte-identical.  The source routine has two real `ret` tails, so this module
  is intended for the return-terminating `Stmt.retSound` path rather than the
  legacy single-exit `Fn.Spec` epilogue path.
-/

import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256EqSAsm

/-- Loop invariant for the `u256_eq` byte scan.  At loop header `x5` is the
    next byte index; all earlier bytes are known equal. -/
def u256EqInv (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧
    rf.get .x10 = ptr1 ∧
    rf.get .x11 = ptr2 ∧
    rf.get .x31 = (32 : Word) ∧
    (∀ j, j < i → bs1.getD j 0 = bs2.getD j 0) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Focus relation for the second read-only input. -/
def u256EqReadA1 (ptr2 : Word) (bs2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x11 = ptr2 ∧ rob = bs2 ∧ rest = empAssertion

/-- `u256_eq` as a return-terminating SAsm body, byte-for-byte identical to
    `u256Eq_prog`. -/
def u256EqBody (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .LI .x31 (32 : Word)] ;;;
  .retWhileBreak "scan" (.bne .x5 .x31) 32 (u256EqInv ptr1 ptr2 bs1 bs2)
    (.block "before1" [.ADD .x6 .x10 .x5, .ADD .x7 .x11 .x5, .LBU .x28 .x6 (0 : BitVec 12)] ;;;
     .readAt "before2" .x11 (u256EqReadA1 ptr2 bs2) [.LBU .x29 .x7 (0 : BitVec 12)])
    (.bne .x28 .x29)
    (.block "after" [.ADDI .x5 .x5 (1 : BitVec 12)])
    (.block "eq" [.LI .x10 (1 : Word)] ;;; .ret "ret_eq")
    (.block "ne" [.LI .x10 (0 : Word)] ;;; .ret "ret_ne")

/-- Entry condition: `a0`/`a1` point at the two read-only 32-byte buffers. -/
def u256EqPre (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Reach :=
  fun rf _ A =>
    rf.get .x10 = ptr1 ∧ rf.get .x11 = ptr2 ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    (ptr1.toNat + 32 ≤ ptr2.toNat ∨ ptr2.toNat + 32 ≤ ptr1.toNat) ∧
    A = bytesRegion ptr2 bs2

/-- Return condition: `a0 = 1` iff all 32 bytes matched. -/
def u256EqPost (ptr1 ptr2 : Word) (bs1 bs2 : List (BitVec 8)) : Reach :=
  fun rf _ A =>
    rf.get .x10 = (if firstDiff bs1 bs2 32 = 32 then (1 : Word) else (0 : Word)) ∧
    bs1.length = 32 ∧ bs2.length = 32 ∧
    ptr1.toNat + 32 < 2 ^ 64 ∧ ptr2.toNat + 32 < 2 ^ 64 ∧
    A = bytesRegion ptr2 bs2


-- Byte-identity to the existing emitted `u256_eq` program.
#guard (u256EqBody 0 0 [] []).flatten 0 = u256Eq_prog
#guard (u256EqBody 0 0 [] []).retOffsetsOk
#guard !(u256EqBody 0 0 [] []).offsetsOk

end U256EqSAsm
end EvmAsm.Codegen
