/-
  EvmAsm.Codegen.Programs.U256AddBeSAsm

  SAsm model for `u256_add_be`: add two 32-byte big-endian buffers, write the
  32-byte result, and return the final carry in `a0`.

  This proof uses the first additive bottom-break loop node (`Stmt.doWhileBreak`)
  from PR #9902.  The SAsm memory contract is intentionally separated: both
  inputs are ambient read-only `bytesRegion`s and the output is the sole
  writable window, so this theorem covers the non-overlapping ownership shape.
-/

import EvmAsm.Codegen.Programs.U256
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256AddBeSAsm

/-- One byte addition step with incoming carry `0` or `1`, computed exactly as
    the RV64 code does: widen both bytes, add carry, low byte is the result,
    `sum >>> 8` is the next carry. -/
def addCarryByte (a b : BitVec 8) (carry : Word) : BitVec 8 × Word :=
  let sum : Word := a.zeroExtend 64 + b.zeroExtend 64 + carry
  (sum.truncate 8, sum >>> (8 : Nat))

/-- Pure model of the loop after `k` processed bytes, starting at byte 31 and
    walking toward byte 0.  The state is `(outputBytes, carry)`. -/
def addCarryState (a b orig : List (BitVec 8)) : Nat → List (BitVec 8) × Word
  | 0 => (orig, 0)
  | k + 1 =>
      let st := addCarryState a b orig k
      let idx := 31 - k
      let step := addCarryByte (a.getD idx 0) (b.getD idx 0) st.2
      (st.1.set idx step.1, step.2)

/-- Final 32-byte big-endian result. -/
def u256AddBeBytes (a b orig : List (BitVec 8)) : List (BitVec 8) :=
  (addCarryState a b orig 32).1

/-- Final overflow carry returned in `a0`. -/
def u256AddBeCarry (a b orig : List (BitVec 8)) : Word :=
  (addCarryState a b orig 32).2

/-- Focus relation for the first read-only input at `a0`. -/
def roA (aPtr bPtr : Word) (aBytes bBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x10 = aPtr ∧ rob = aBytes ∧ rest = bytesRegion bPtr bBytes

/-- Focus relation for the second read-only input at `a1`. -/
def roB (aPtr bPtr : Word) (aBytes bBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x11 = bPtr ∧ rob = bBytes ∧ rest = bytesRegion aPtr aBytes

/-- Loop invariant at the entry to the `k`-th iteration. -/
def u256AddBeInv (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x10 = aPtr ∧
    rf.get .x11 = bPtr ∧
    rf.get .x12 = outPtr ∧
    rf.get .x5 = BitVec.ofNat 64 (31 - k) ∧
    rf.get .x6 = (addCarryState aBytes bBytes orig k).2 ∧
    ws = (addCarryState aBytes bBytes orig k).1 ∧
    k ≤ 31 ∧
    aBytes.length = 32 ∧ bBytes.length = 32 ∧ orig.length = 32 ∧
    aPtr.toNat + 32 < 2 ^ 64 ∧ bPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat) ∧
    (bPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ bPtr.toNat) ∧
    A = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)

/-- Loop post before the final `mv a0, carry`: all bytes processed. -/
def u256AddBeLoopPost (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = bPtr ∧ rf.get .x12 = outPtr ∧
    rf.get .x5 = 0 ∧ rf.get .x6 = u256AddBeCarry aBytes bBytes orig ∧
    ws = u256AddBeBytes aBytes bBytes orig ∧
    A = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)

/-- Function precondition: two read-only 32-byte inputs and one writable output
    window.  The explicit range disjointness hypotheses are the routing facts
    needed by the current SAsm read/write ownership model. -/
def u256AddBePre (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = bPtr ∧ rf.get .x12 = outPtr ∧
    ws = orig ∧
    aBytes.length = 32 ∧ bBytes.length = 32 ∧ orig.length = 32 ∧
    aPtr.toNat + 32 < 2 ^ 64 ∧ bPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat) ∧
    (bPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ bPtr.toNat) ∧
    A = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)

/-- Function postcondition: `a0` is the carry and the output window is the pure
    BE byte-add result. -/
def u256AddBePost (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = u256AddBeCarry aBytes bBytes orig ∧
    rf.get .x11 = bPtr ∧ rf.get .x12 = outPtr ∧
    ws = u256AddBeBytes aBytes bBytes orig ∧
    A = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes)

/-- Byte-identical structured body, excluding the final `ret` epilogue handled
    by `Fn.Spec`. -/
def u256AddBeBody (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (31 : Word), .LI .x6 (0 : Word)] ;;;
  .«doWhileBreak» "loop" 31 (u256AddBeInv aPtr bPtr outPtr aBytes bBytes orig)
    (u256AddBeLoopPost aPtr bPtr outPtr aBytes bBytes orig)
    (.block "addr" [.ADD .x7 .x10 .x5, .ADD .x28 .x11 .x5, .ADD .x29 .x12 .x5] ;;;
     .readAt "readA" .x10 (roA aPtr bPtr aBytes bBytes) [.LBU .x30 .x7 (0 : BitVec 12)] ;;;
     .readAt "readB" .x11 (roB aPtr bPtr aBytes bBytes) [.LBU .x31 .x28 (0 : BitVec 12)] ;;;
     .block "sumStore" [.ADD .x30 .x30 .x31,
       .ADD .x30 .x30 .x6,
       .SRLI .x6 .x30 (8 : BitVec 6),
       .ANDI .x30 .x30 (255 : BitVec 12),
       .SB .x29 .x30 (0 : BitVec 12)])
    (.beq .x5 .x0)
    (.block "dec" [.ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "retVal" [.MV .x10 .x6]

def u256AddBeFn (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Fn where
  name := "u256AddBe"
  region := Region.empty
  rw := ⟨outPtr, 32⟩
  pre := u256AddBePre aPtr bPtr outPtr aBytes bBytes orig
  post := u256AddBePost aPtr bPtr outPtr aBytes bBytes orig
  body := u256AddBeBody aPtr bPtr outPtr aBytes bBytes orig

#guard (u256AddBeBody 0 0 0 [] [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
  = u256AddBe_prog

#guard (u256AddBeBody 0 0 0 [] [] []).flatten 0 =
  (u256AddBeBody 0 0 0 [] [] []).flatten 0x80000000



/-! ## Local proof helpers -/

private theorem idx_lt_32 {i : Nat} (hi : i ≤ 31) : 31 - i < 32 := by
  omega

private theorem idx_toNat (i : Nat) (hi : i ≤ 31) :
    (BitVec.ofNat 64 (31 - i)).toNat = 31 - i := by
  rw [BitVec.toNat_ofNat]
  omega

private theorem add_idx_sub_self (ptr : Word) (i : Nat) (hi : i ≤ 31) :
    (ptr + BitVec.ofNat 64 (31 - i) - ptr).toNat = 31 - i := by
  have hidx : (BitVec.ofNat 64 (31 - i)).toNat = 31 - i := idx_toNat i hi
  rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]
  omega

private theorem add_idx_sub_base (ptr base : Word) (i : Nat) (hi : i ≤ 31) :
    (ptr + BitVec.ofNat 64 (31 - i) - base).toNat =
      (ptr.toNat + (31 - i) + (2 ^ 64 - base.toNat)) % 2 ^ 64 := by
  have hidx : (BitVec.ofNat 64 (31 - i)).toNat = 31 - i := idx_toNat i hi
  rw [BitVec.toNat_sub, BitVec.toNat_add, hidx]
  omega

private theorem not_inRw_disjoint32 (ptr outPtr : Word) (ws : List (BitVec 8))
    (i : Nat) (hi : i ≤ 31)
    (hws : ws.length = 32)
    (hptr : ptr.toNat + 32 < 2 ^ 64)
    (hout : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : ptr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ ptr.toNat) :
    ¬ inRw outPtr ws (ptr + BitVec.ofNat 64 (31 - i)) 1 := by
  unfold inRw
  rw [hws, add_idx_sub_base ptr outPtr i hi]
  intro hcontra
  rcases hdisj with hd | hd <;> omega

private theorem byteAt_idx (ptr : Word) (bytes : List (BitVec 8)) (i : Nat) (hi : i ≤ 31) :
    Region.byteAt ⟨ptr, bytes⟩ (ptr + BitVec.ofNat 64 (31 - i)) =
      bytes.getD (31 - i) 0 := by
  unfold Region.byteAt
  rw [add_idx_sub_self ptr i hi]

private theorem readLbu_blockVCs (ptr outPtr : Word) (rf : RegFile) (ws robytes : List (BitVec 8))
    (rd addrReg : Reg) (i : Nat) (hi : i ≤ 31)
    (haddr : rf.get addrReg = ptr + BitVec.ofNat 64 (31 - i))
    (hws : ws.length = 32)
    (hroLen : robytes.length = 32)
    (hptrBound : ptr.toNat + 32 < 2 ^ 64)
    (houtBound : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : ptr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ ptr.toNat) :
    blockVCs ⟨ptr, robytes⟩ outPtr rf ws [.LBU rd addrReg (0 : BitVec 12)] := by
  have haddr0 : rf.get addrReg + signExtend12 (0 : BitVec 12)
      = ptr + BitVec.ofNat 64 (31 - i) := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw outPtr ws (rf.get addrReg + signExtend12 (0 : BitVec 12)) 1
    then _ else Region.loadOk _ _ _)
  rw [haddr0, if_neg (not_inRw_disjoint32 ptr outPtr ws i hi hws hptrBound houtBound hdisj)]
  unfold Region.loadOk
  change 1 ∣ (ptr + BitVec.ofNat 64 (31 - i) - ptr).toNat ∧
    (ptr + BitVec.ofNat 64 (31 - i) - ptr).toNat + 1 ≤ robytes.length
  rw [add_idx_sub_self ptr i hi, hroLen]
  exact ⟨one_dvd _, by omega⟩

private theorem execBlock_lbu_get_ne (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs : Reg) (ofs : BitVec 12) (r : Reg)
    (hne : r ≠ rd) :
    (execBlock ro rwBase rf ws [.LBU rd rs ofs]).1.get r = rf.get r := by
  rw [execBlock_cons, execBlock_nil, execInstrRF]
  dsimp only [aluSem, loadSem]
  by_cases h : inRw rwBase ws (rf.get rs + signExtend12 ofs) 1
  · rw [if_pos h, RegFile.get_set_ne _ _ _ _ hne]
  · rw [if_neg h, RegFile.get_set_ne _ _ _ _ hne]

private theorem sumStore_blockVCs (outPtr : Word) (rf : RegFile) (ws : List (BitVec 8))
    (i : Nat) (hi : i ≤ 31)
    (hx29 : rf.get .x29 = outPtr + BitVec.ofNat 64 (31 - i))
    (hws : ws.length = 32) :
    blockVCs Region.empty outPtr rf ws
      [.ADD .x30 .x30 .x31, .ADD .x30 .x30 .x6,
       .SRLI .x6 .x30 (8 : BitVec 6), .ANDI .x30 .x30 (255 : BitVec 12),
       .SB .x29 .x30 (0 : BitVec 12)] := by
  simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF]
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, inRw]
  rw [hx29, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
  rw [show outPtr + BitVec.ofNat 64 (31 - i) + (0 : Word) =
      outPtr + BitVec.ofNat 64 (31 - i) by bv_omega]
  rw [add_idx_sub_self outPtr i hi, hws]
  simp only [one_dvd, and_true, true_and]
  omega

/-! ## Post bridge -/

/-- Final post bridge for `u256_add_be`: once the bottom-break loop has
    produced its loop post, the trailing `mv a0, t1` establishes the function
    post by returning the carry in `a0` while preserving the output window and
    ambient read-only inputs. -/
theorem u256AddBe_retVal_post (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) :
    ∀ rf ws A,
      sp Region.empty ⟨outPtr, 32⟩ (.block "retVal" [.MV .x10 .x6])
        (u256AddBeLoopPost aPtr bPtr outPtr aBytes bBytes orig) rf ws A →
      u256AddBePost aPtr bPtr outPtr aBytes bBytes orig rf ws A := by
  rintro rf ws A ⟨rf₀, ws₀, hws₀, hloop, hrf, hws⟩
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsBytes, hA⟩ := hloop
  subst hrf
  subst hws
  unfold u256AddBePost
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [RegFile.get_set_self _ _ _ (by decide), hx6]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]
  · exact hwsBytes
  · exact hA

end U256AddBeSAsm

end EvmAsm.Codegen
