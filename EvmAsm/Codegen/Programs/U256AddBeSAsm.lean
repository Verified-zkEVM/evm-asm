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

private theorem addCarryState_succ (a b orig : List (BitVec 8)) (k : Nat) :
    addCarryState a b orig (k + 1) =
      let st := addCarryState a b orig k
      let idx := 31 - k
      let step := addCarryByte (a.getD idx 0) (b.getD idx 0) st.2
      (st.1.set idx step.1, step.2) := by
  rfl

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

/-- Byte-identical loop body before the mid-body break test. -/
def u256AddBeBefore (aPtr bPtr _outPtr : Word)
    (aBytes bBytes _orig : List (BitVec 8)) : Stmt :=
  .block "addr" [.ADD .x7 .x10 .x5, .ADD .x28 .x11 .x5, .ADD .x29 .x12 .x5] ;;;
  .readAt "readA" .x10 (roA aPtr bPtr aBytes bBytes) [.LBU .x30 .x7 (0 : BitVec 12)] ;;;
  .readAt "readB" .x11 (roB aPtr bPtr aBytes bBytes) [.LBU .x31 .x28 (0 : BitVec 12)] ;;;
  .block "sumStore" [.ADD .x30 .x30 .x31,
    .ADD .x30 .x30 .x6,
    .SRLI .x6 .x30 (8 : BitVec 6),
    .ANDI .x30 .x30 (255 : BitVec 12),
    .SB .x29 .x30 (0 : BitVec 12)]

/-- Byte-identical structured body, excluding the final `ret` epilogue handled
    by `Fn.Spec`. -/
def u256AddBeBody (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (31 : Word), .LI .x6 (0 : Word)] ;;;
  .«doWhileBreak» "loop" 31 (u256AddBeInv aPtr bPtr outPtr aBytes bBytes orig)
    (u256AddBeLoopPost aPtr bPtr outPtr aBytes bBytes orig)
    (u256AddBeBefore aPtr bPtr outPtr aBytes bBytes orig)
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

private theorem execBlock_lbu_ws (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs : Reg) (ofs : BitVec 12) :
    (execBlock ro rwBase rf ws [.LBU rd rs ofs]).2 = ws := by
  rw [execBlock_cons, execBlock_nil, execInstrRF]
  dsimp only [aluSem, loadSem]

private theorem execBlock_lbu_get_ne (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs : Reg) (ofs : BitVec 12) (r : Reg)
    (hne : r ≠ rd) :
    (execBlock ro rwBase rf ws [.LBU rd rs ofs]).1.get r = rf.get r := by
  rw [execBlock_cons, execBlock_nil, execInstrRF]
  dsimp only [aluSem, loadSem]
  by_cases h : inRw rwBase ws (rf.get rs + signExtend12 ofs) 1
  · rw [if_pos h, RegFile.get_set_ne _ _ _ _ hne]
  · rw [if_neg h, RegFile.get_set_ne _ _ _ _ hne]

private theorem execBlock_lbu_ro_idx (ptr outPtr : Word) (rf : RegFile)
    (ws robytes : List (BitVec 8)) (rd addrReg : Reg) (i : Nat) (hi : i ≤ 31)
    (haddr : rf.get addrReg = ptr + BitVec.ofNat 64 (31 - i))
    (hws : ws.length = 32)
    (hptrBound : ptr.toNat + 32 < 2 ^ 64)
    (houtBound : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : ptr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ ptr.toNat) :
    execBlock ⟨ptr, robytes⟩ outPtr rf ws [.LBU rd addrReg (0 : BitVec 12)] =
      (rf.set rd ((robytes.getD (31 - i) 0).zeroExtend 64), ws) := by
  have haddr0 : rf.get addrReg + signExtend12 (0 : BitVec 12)
      = ptr + BitVec.ofNat 64 (31 - i) := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  rw [execBlock_cons, execInstrRF]
  dsimp only [aluSem, loadSem]
  rw [if_neg (by
    rw [haddr0]
    exact not_inRw_disjoint32 ptr outPtr ws i hi hws hptrBound houtBound hdisj)]
  rw [haddr0, byteAt_idx ptr robytes i hi, execBlock_nil]

private theorem andi255_truncate8 (x : Word) :
    (x &&& signExtend12 (255 : BitVec 12)).truncate 8 = x.truncate 8 := by
  have h255 : signExtend12 (255 : BitVec 12) = (255 : Word) := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro j
  rw [h255]
  by_cases hj : j < 8
  · have hmask : (255 : Word).getLsbD j = true := by
      interval_cases j <;> rfl
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, hj, decide_true, Bool.true_and]
    rw [hmask]
    simp
  · simp [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hj]

private theorem sumStore_effect (outPtr : Word) (rf : RegFile) (ws : List (BitVec 8))
    (i : Nat) (hi : i ≤ 31) (a b : BitVec 8) (carry : Word)
    (hx30 : rf.get .x30 = a.zeroExtend 64)
    (hx31 : rf.get .x31 = b.zeroExtend 64)
    (hx6 : rf.get .x6 = carry)
    (hx29 : rf.get .x29 = outPtr + BitVec.ofNat 64 (31 - i)) :
    let r := execBlock Region.empty outPtr rf ws
      [.ADD .x30 .x30 .x31, .ADD .x30 .x30 .x6,
       .SRLI .x6 .x30 (8 : BitVec 6), .ANDI .x30 .x30 (255 : BitVec 12),
       .SB .x29 .x30 (0 : BitVec 12)]
    r.1.get .x10 = rf.get .x10 ∧
    r.1.get .x11 = rf.get .x11 ∧
    r.1.get .x12 = rf.get .x12 ∧
    r.1.get .x5 = rf.get .x5 ∧
    r.1.get .x6 = (addCarryByte a b carry).2 ∧
    r.2 = ws.set (31 - i) (addCarryByte a b carry).1 := by
  dsimp only
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (31 - i) (by
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx29, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    rw [show outPtr + BitVec.ofNat 64 (31 - i) + (0 : Word) =
        outPtr + BitVec.ofNat 64 (31 - i) by bv_omega]
    exact add_idx_sub_self outPtr i hi)]
  rw [execBlock_nil]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]
  unfold addCarryByte
  simp only [hx30, hx31, hx6]
  refine ⟨trivial, trivial, trivial, trivial, rfl, ?_⟩
  rw [show setBytes ws (31 - i)
      [((BitVec.zeroExtend 64 a + BitVec.zeroExtend 64 b + carry) &&&
        signExtend12 (255 : BitVec 12)).truncate 8]
      = ws.set (31 - i)
        (((BitVec.zeroExtend 64 a + BitVec.zeroExtend 64 b + carry) &&&
          signExtend12 (255 : BitVec 12)).truncate 8) from rfl]
  rw [andi255_truncate8]

private theorem u256AddBeBefore_effect (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨outPtr, 32⟩ (u256AddBeBefore aPtr bPtr outPtr aBytes bBytes orig)
        (u256AddBeInv aPtr bPtr outPtr aBytes bBytes orig i) rf' ws' A' →
      rf'.get .x10 = aPtr ∧
      rf'.get .x11 = bPtr ∧
      rf'.get .x12 = outPtr ∧
      rf'.get .x5 = BitVec.ofNat 64 (31 - i) ∧
      rf'.get .x6 = (addCarryState aBytes bBytes orig (i + 1)).2 ∧
      ws' = (addCarryState aBytes bBytes orig (i + 1)).1 ∧
      i ≤ 31 ∧
      aBytes.length = 32 ∧ bBytes.length = 32 ∧ orig.length = 32 ∧
      aPtr.toNat + 32 < 2 ^ 64 ∧ bPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
      (aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat) ∧
      (bPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ bPtr.toNat) ∧
      A' = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
  intro rf' ws' A' hsp
  unfold u256AddBeBefore at hsp
  obtain ⟨rfS, wsS, hwsS, hreachB, hrf', hws'⟩ := hsp
  obtain ⟨rfB0, wsB0, AB, robB, restB, hlenBRead, hreachA, _hsatB,
    hroBrel, hrfB, hwsB, hAeqB⟩ := hreachB
  obtain ⟨rfA0, wsA0, AA, robA, restA, hlenARead, hreach0, _hsatA,
    hroArel, hrfA, hwsA, _hAeqA⟩ := hreachA
  obtain ⟨rf0, ws0, hws0, hinv, hrf0, hws0eq⟩ := hreach0
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hi, hlenA, hlenB, hlenO,
    hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hinv
  obtain ⟨hptrA, hrobA, hrestA⟩ := hroArel
  obtain ⟨hptrB, hrobB, hrestB⟩ := hroBrel
  dsimp only [u256AddBeFn] at hlenARead hlenBRead hrf0 hws0eq hrfA hwsA hrfB hwsB hrf' hws'
  have haddrA : rfA0.get .x7 = rfA0.get .x10 + BitVec.ofNat 64 (31 - i) := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx5]
  have hreadA : execBlock { base := rfA0.get .x10, bytes := robA } outPtr rfA0 wsA0
      [.LBU .x30 .x7 (0 : BitVec 12)] =
      (rfA0.set .x30 ((aBytes.getD (31 - i) 0).zeroExtend 64), wsA0) := by
    rw [hrobA]
    apply execBlock_lbu_ro_idx
    · exact hi
    · exact haddrA
    · exact hlenARead
    · rw [hptrA]
      exact hplA
    · exact hplO
    · rw [hptrA]
      exact hdisjA
  have hwsAeq : wsB0 = wsA0 := by
    rw [hwsA, execBlock_lbu_ws]
  have haddrB : rfB0.get .x28 = rfB0.get .x11 + BitVec.ofNat 64 (31 - i) := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx11, hx5]
  have hreadB : execBlock { base := rfB0.get .x11, bytes := robB } outPtr rfB0 wsB0
      [.LBU .x31 .x28 (0 : BitVec 12)] =
      (rfB0.set .x31 ((bBytes.getD (31 - i) 0).zeroExtend 64), wsB0) := by
    rw [hrobB]
    apply execBlock_lbu_ro_idx
    · exact hi
    · exact haddrB
    · rw [hwsAeq]
      exact hlenARead
    · rw [hptrB]
      exact hplB
    · exact hplO
    · rw [hptrB]
      exact hdisjB
  have hwsSeq : wsS = (addCarryState aBytes bBytes orig i).1 := by
    rw [hwsB, execBlock_lbu_ws, hwsAeq, hws0eq]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    exact hwsState
  have hx30S : rfS.get .x30 = (aBytes.getD (31 - i) 0).zeroExtend 64 := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x30 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_self _ _ _ (by decide)]
  have hx31S : rfS.get .x31 = (bBytes.getD (31 - i) 0).zeroExtend 64 := by
    rw [hrfB, hreadB, RegFile.get_set_self _ _ _ (by decide)]
  have hx6S : rfS.get .x6 = (addCarryState aBytes bBytes orig i).2 := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx6
  have hx29S : rfS.get .x29 = outPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx12, hx5]
  have hsum := sumStore_effect outPtr rfS wsS i hi
    (aBytes.getD (31 - i) 0) (bBytes.getD (31 - i) 0)
    (addCarryState aBytes bBytes orig i).2 hx30S hx31S hx6S hx29S
  dsimp only at hsum
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hsum
  have hAfinal : A' = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
    rw [hAeqB, hptrB, hrobB, hrestB]
    xperm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hi, hlenA, hlenB, hlenO, hplA, hplB, hplO,
    hdisjA, hdisjB, hAfinal⟩
  · rw [hrf', hsx10]
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrf', hsx11]
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  · rw [hrf', hsx12]
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12
  · rw [hrf', hsx5]
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx5
  · rw [hrf', hsx6]
    rw [addCarryState_succ]
  · rw [hws', hsws, hwsSeq]
    rw [addCarryState_succ]

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


theorem u256AddBe_spec (aPtr bPtr outPtr : Word)
    (aBytes bBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩)
    (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (base : Word) :
    (u256AddBeFn aPtr bPtr outPtr aBytes bBytes orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case u256AddBe.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hpre, hrf, hws⟩
    obtain ⟨hx10, hx11, hx12, hwsOrig, hlenA, hlenB, hlenO, hplA, hplB, hplO,
      hdisjA, hdisjB, hA⟩ := hpre
    have hws32 : ws₀.length = 32 := hws₀
    subst hrf
    subst hws
    unfold u256AddBeInv
    simp only [u256AddBeFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenA, hlenB, hlenO, hplA, hplB, hplO,
      hdisjA, hdisjB, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · exact hwsOrig
  case u256AddBe.loop.before.readA.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf, hws⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hinv
    dsimp only [u256AddBeFn] at hrf hws hws₀
    subst hrf
    subst hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true] at hhp ⊢
    refine ⟨aBytes, bytesRegion bPtr bBytes, ⟨?_, rfl, rfl⟩, ?_, bytesRegion_pcFree _ _, ?_⟩
    · exact hx10
    · rw [hA] at hhp
      rw [hx10]
      exact hhp
    · rw [hx10]
      exact hroA
  case u256AddBe.loop.before.readA.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf, hwsEq⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    dsimp only [u256AddBeFn] at hrf hws hws₀ hwsEq ⊢
    have hws32 : ws.length = 32 := hws
    subst hrf
    subst hwsEq
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true] at hptr hrob hrest ⊢
    have haddr : (((rf₀.set Reg.x7 (rf₀.get Reg.x10 + rf₀.get Reg.x5)).set Reg.x28
        (rf₀.get Reg.x11 + rf₀.get Reg.x5)).set Reg.x29
        (rf₀.get Reg.x12 + rf₀.get Reg.x5)).get Reg.x7 =
        rf₀.get Reg.x10 + BitVec.ofNat 64 (31 - i) := by
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx5]
    exact readLbu_blockVCs (rf₀.get .x10) outPtr _ ws robytes .x30 .x7 i hi haddr hws32
      (by rw [hrob]; exact hlenA) (by rw [hx10]; exact hplA) hplO
      (by rw [hx10]; exact hdisjA)
  case u256AddBe.loop.before.readB.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rf₀, ws₀, A₀, robA, restA, hlenARead, hreach0, hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreach
    obtain ⟨rfInit, wsInit, hwsInit, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hinv
    obtain ⟨hptrA, hrobA, hrestA⟩ := hroArel
    dsimp only [u256AddBeFn] at hrfA hrf0 hwsA hws0 hlenARead hwsInit
    have hx11' : rf.get .x11 = bPtr := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x11 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx11]
    have hAshape : A = (bytesRegion aPtr aBytes ** bytesRegion bPtr bBytes) := by
      rw [hAeqA, hptrA, hrobA, hrestA]
    refine ⟨bBytes, bytesRegion aPtr aBytes, ⟨hx11', rfl, rfl⟩, ?_, bytesRegion_pcFree _ _, ?_⟩
    · rw [hx11']
      rw [hAshape] at hhp
      xperm_hyp hhp
    · rw [hx11']
      exact hroB
  case u256AddBe.loop.before.readB.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rf₀, ws₀, A₀, robA, restA, hlenARead, hreach0, hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreach
    obtain ⟨rfInit, wsInit, hwsInit, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    dsimp only [u256AddBeFn] at hrfA hrf0 hwsA hws0 hlenARead hws hwsInit ⊢
    have hws32 : ws.length = 32 := hws
    have haddr : rf.get .x28 = rf.get .x11 + BitVec.ofNat 64 (31 - i) := by
      rw [hrfA,
        execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x28 (by decide),
        execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x11 (by decide),
        hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx11, hx5]
    exact readLbu_blockVCs (rf.get .x11) outPtr rf ws robytes .x31 .x28 i hi haddr hws32
      (by rw [hrob]; exact hlenB) (by rw [hptr]; exact hplB) hplO
      (by rw [hptr]; exact hdisjB)
  case u256AddBe.loop.before.sumStore.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rfB, wsB, AB, robB, restB, hlenBRead, hreachA, hsatB,
      hroBrel, hrfB, hwsB, hAeqB⟩ := hreach
    obtain ⟨rfA, wsA, AA, robA, restA, hlenARead, hreach0, hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreachA
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hinv
    dsimp only [u256AddBeFn] at hrf0 hws0 hlenARead hlenBRead hrfA hrfB hwsA hwsB hws₀ hws ⊢
    have hws32 : ws.length = 32 := hws
    have hx29 : rf.get .x29 = outPtr + BitVec.ofNat 64 (31 - i) := by
      rw [hrfB, execBlock_lbu_get_ne _ _ _ _ .x31 .x28 (0 : BitVec 12) .x29 (by decide),
        hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x29 (by decide),
        hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx12, hx5]
    exact sumStore_blockVCs outPtr rf ws i hi hx29 hws32
  case u256AddBe.loop.inv_step =>
    rintro i hiLt rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, _hnbreak⟩, hrf', hws'⟩ := hsp
    have hb := u256AddBeBefore_effect aPtr bPtr outPtr aBytes bBytes orig i rfa wsa A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hb
    subst hrf'
    subst hws'
    unfold u256AddBeInv
    simp only [u256AddBeFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenA, hlenB, hlenO, hplA, hplB, hplO,
      hdisjA, hdisjB, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5), hx6]
    · exact hwsState
  case u256AddBe.loop.exhausted =>
    rintro rf' ws' A' hspbb
    have hb := u256AddBeBefore_effect aPtr bPtr outPtr aBytes bBytes orig 31 rf' ws' A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hb
    simp only [Cond.holds]
    rw [hx5]
    rfl
  case u256AddBe.loop.break =>
    rintro i hi rf' ws' A' hspbb hbreak
    have hb := u256AddBeBefore_effect aPtr bPtr outPtr aBytes bBytes orig i rf' ws' A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB, hlenO,
      hplA, hplB, hplO, hdisjA, hdisjB, hA⟩ := hb
    simp only [Cond.holds, RegFile.get_x0] at hbreak
    have hi31 : i = 31 := by
      rw [hx5] at hbreak
      have hto := congrArg BitVec.toNat hbreak
      rw [idx_toNat i hik] at hto
      change 31 - i = 0 at hto
      omega
    subst hi31
    unfold u256AddBeLoopPost u256AddBeCarry u256AddBeBytes
    refine ⟨hx10, hx11, hx12, ?_, ?_, ?_, hA⟩
    · rw [hx5]
      rfl
    · exact hx6
    · exact hwsState
  case u256AddBe.post =>
    intro rf ws A h
    exact u256AddBe_retVal_post aPtr bPtr outPtr aBytes bBytes orig rf ws A h

/-! ## Alias-safe in-place contract (`aPtr = outPtr`) -/

private theorem getD_set_ne {l : List (BitVec 8)} {i j : Nat}
    {b d : BitVec 8} (h : i ≠ j) :
    (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

private theorem addCarryState_length (a b orig : List (BitVec 8)) (k : Nat) :
    (addCarryState a b orig k).1.length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [addCarryState_succ]
      simp only
      rw [List.length_set, ih]

private theorem addCarryState_unprocessed (a b : List (BitVec 8))
    (k j : Nat) (hj : j < 32 - k) :
    (addCarryState a b a k).1.getD j 0 = a.getD j 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [addCarryState_succ]
      rw [getD_set_ne (by omega : 31 - k ≠ j)]
      apply ih
      omega

def roBInPlace (bPtr : Word) (bBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest =>
    rf.get .x11 = bPtr ∧ rob = bBytes ∧ rest = empAssertion

def u256AddBeInPlaceInv (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = bPtr ∧ rf.get .x12 = aPtr ∧
    rf.get .x5 = BitVec.ofNat 64 (31 - k) ∧
    rf.get .x6 = (addCarryState aBytes bBytes aBytes k).2 ∧
    ws = (addCarryState aBytes bBytes aBytes k).1 ∧ k ≤ 31 ∧
    aBytes.length = 32 ∧ bBytes.length = 32 ∧
    aPtr.toNat + 32 < 2 ^ 64 ∧ bPtr.toNat + 32 < 2 ^ 64 ∧
    (bPtr.toNat + 32 ≤ aPtr.toNat ∨ aPtr.toNat + 32 ≤ bPtr.toNat) ∧
    A = bytesRegion bPtr bBytes

def u256AddBeInPlaceLoopPost (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = bPtr ∧ rf.get .x12 = aPtr ∧
    rf.get .x5 = 0 ∧ rf.get .x6 = u256AddBeCarry aBytes bBytes aBytes ∧
    ws = u256AddBeBytes aBytes bBytes aBytes ∧ A = bytesRegion bPtr bBytes

def u256AddBeBeforeInPlace (_aPtr bPtr : Word)
    (_aBytes bBytes : List (BitVec 8)) : Stmt :=
  .block "addr" [.ADD .x7 .x10 .x5, .ADD .x28 .x11 .x5, .ADD .x29 .x12 .x5] ;;;
  .block "readA" [.LBU .x30 .x7 (0 : BitVec 12)] ;;;
  .readAt "readB" .x11 (roBInPlace bPtr bBytes) [.LBU .x31 .x28 (0 : BitVec 12)] ;;;
  .block "sumStore" [.ADD .x30 .x30 .x31,
    .ADD .x30 .x30 .x6, .SRLI .x6 .x30 (8 : BitVec 6),
    .ANDI .x30 .x30 (255 : BitVec 12), .SB .x29 .x30 (0 : BitVec 12)]

def u256AddBeInPlaceBody (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (31 : Word), .LI .x6 (0 : Word)] ;;;
  .«doWhileBreak» "loop" 31 (u256AddBeInPlaceInv aPtr bPtr aBytes bBytes)
    (u256AddBeInPlaceLoopPost aPtr bPtr aBytes bBytes)
    (u256AddBeBeforeInPlace aPtr bPtr aBytes bBytes)
    (.beq .x5 .x0)
    (.block "dec" [.ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "retVal" [.MV .x10 .x6]

def u256AddBeInPlaceFn (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) : Fn where
  name := "u256AddBeInPlace"
  region := Region.empty
  rw := ⟨aPtr, 32⟩
  pre := fun rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = bPtr ∧ rf.get .x12 = aPtr ∧
    ws = aBytes ∧ aBytes.length = 32 ∧ bBytes.length = 32 ∧
    aPtr.toNat + 32 < 2 ^ 64 ∧ bPtr.toNat + 32 < 2 ^ 64 ∧
    (bPtr.toNat + 32 ≤ aPtr.toNat ∨ aPtr.toNat + 32 ≤ bPtr.toNat) ∧
    A = bytesRegion bPtr bBytes
  post := fun rf ws A =>
    rf.get .x10 = u256AddBeCarry aBytes bBytes aBytes ∧
    rf.get .x11 = bPtr ∧ rf.get .x12 = aPtr ∧
    ws = u256AddBeBytes aBytes bBytes aBytes ∧ A = bytesRegion bPtr bBytes
  body := u256AddBeInPlaceBody aPtr bPtr aBytes bBytes

#guard (u256AddBeInPlaceBody 0 0 [] []).flatten 0 ++
  [Instr.JALR .x0 .x1 (0 : BitVec 12)] = u256AddBe_prog

private theorem execBlock_lbu_rw_current (aPtr : Word) (rf : RegFile)
    (ws aBytes bBytes : List (BitVec 8)) (i : Nat) (hi : i ≤ 31)
    (haddr : rf.get .x7 = aPtr + BitVec.ofNat 64 (31 - i))
    (hws : ws = (addCarryState aBytes bBytes aBytes i).1)
    (hlen : aBytes.length = 32) :
    execBlock Region.empty aPtr rf ws [.LBU .x30 .x7 (0 : BitVec 12)] =
      (rf.set .x30 ((aBytes.getD (31 - i) 0).zeroExtend 64), ws) := by
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ (31 - i)
    (by
      rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      have := add_idx_sub_self aPtr i hi
      bv_omega)
    (by
      rw [hws, addCarryState_length, hlen]
      omega),
    execBlock_nil]
  rw [hws, addCarryState_unprocessed aBytes bBytes i (31 - i) (by omega)]

private theorem readLbuRwInPlace_blockVCs (aPtr : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i ≤ 31)
    (haddr : rf.get .x7 = aPtr + BitVec.ofNat 64 (31 - i))
    (hws : ws.length = 32) :
    blockVCs Region.empty aPtr rf ws [.LBU .x30 .x7 (0 : BitVec 12)] := by
  have haddr0 : rf.get .x7 + signExtend12 (0 : BitVec 12) =
      aPtr + BitVec.ofNat 64 (31 - i) := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw aPtr ws (rf.get .x7 + signExtend12 (0 : BitVec 12)) 1
    then _ else Region.empty.loadOk _ _)
  rw [haddr0, if_pos]
  · unfold Region.loadOk
    change 1 ∣ (aPtr + BitVec.ofNat 64 (31 - i) - aPtr).toNat ∧
      (aPtr + BitVec.ofNat 64 (31 - i) - aPtr).toNat + 1 ≤ ws.length
    rw [add_idx_sub_self aPtr i hi, hws]
    exact ⟨one_dvd _, by omega⟩
  · unfold inRw
    rw [add_idx_sub_self aPtr i hi, hws]
    omega

private theorem u256AddBeBeforeInPlace_effect (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨aPtr, 32⟩
        (u256AddBeBeforeInPlace aPtr bPtr aBytes bBytes)
        (u256AddBeInPlaceInv aPtr bPtr aBytes bBytes i) rf' ws' A' →
      rf'.get .x10 = aPtr ∧ rf'.get .x11 = bPtr ∧ rf'.get .x12 = aPtr ∧
      rf'.get .x5 = BitVec.ofNat 64 (31 - i) ∧
      rf'.get .x6 = (addCarryState aBytes bBytes aBytes (i + 1)).2 ∧
      ws' = (addCarryState aBytes bBytes aBytes (i + 1)).1 ∧
      i ≤ 31 ∧ aBytes.length = 32 ∧ bBytes.length = 32 ∧
      aPtr.toNat + 32 < 2 ^ 64 ∧ bPtr.toNat + 32 < 2 ^ 64 ∧
      (bPtr.toNat + 32 ≤ aPtr.toNat ∨ aPtr.toNat + 32 ≤ bPtr.toNat) ∧
      A' = bytesRegion bPtr bBytes := by
  intro rf' ws' A' hsp
  unfold u256AddBeBeforeInPlace at hsp
  obtain ⟨rfS, wsS, hwsS, hreachB, hrf', hws'⟩ := hsp
  obtain ⟨rfB0, wsB0, AB, robB, restB, hlenBRead, hreachA, _hsatB,
    hroBrel, hrfB, hwsB, hAeqB⟩ := hreachB
  obtain ⟨rfA0, wsA0, hlenARead, hreach0, hrfA, hwsA⟩ := hreachA
  obtain ⟨rf0, ws0, hws0, hinv, hrf0, hws0eq⟩ := hreach0
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hi, hlenA, hlenB,
    hplA, hplB, hdisjB, hA⟩ := hinv
  obtain ⟨hptrB, hrobB, hrestB⟩ := hroBrel
  dsimp only [u256AddBeInPlaceFn] at hlenARead hlenBRead hrf0 hws0eq hrfA hwsA hrfB hwsB hrf' hws'
  have haddrA : rfA0.get .x7 = aPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, hx10, hx5]
  have hreadA : execBlock Region.empty aPtr rfA0 wsA0
      [.LBU .x30 .x7 (0 : BitVec 12)] =
      (rfA0.set .x30 ((aBytes.getD (31 - i) 0).zeroExtend 64), wsA0) := by
    apply execBlock_lbu_rw_current aPtr rfA0 wsA0 aBytes bBytes i hi haddrA
    · rw [hws0eq]
      exact hwsState
    · exact hlenA
  have hwsAeq : wsB0 = wsA0 := by
    rw [hwsA, execBlock_lbu_ws]
  have haddrB : rfB0.get .x28 = bPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
      hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, hx11, hx5]
  have hreadB : execBlock { base := rfB0.get .x11, bytes := robB } aPtr rfB0 wsB0
      [.LBU .x31 .x28 (0 : BitVec 12)] =
      (rfB0.set .x31 ((bBytes.getD (31 - i) 0).zeroExtend 64), wsB0) := by
    rw [hrobB]
    apply execBlock_lbu_ro_idx
    · exact hi
    · rw [hptrB]
      exact haddrB
    · exact hlenBRead
    · rw [hptrB]
      exact hplB
    · exact hplA
    · rw [hptrB]
      exact hdisjB
  have hwsSeq : wsS = (addCarryState aBytes bBytes aBytes i).1 := by
    rw [hwsB, execBlock_lbu_ws, hwsAeq, hws0eq]
    exact hwsState
  have hx30S : rfS.get .x30 = (aBytes.getD (31 - i) 0).zeroExtend 64 := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x30 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_self _ _ _ (by decide)]
  have hx31S : rfS.get .x31 = (bBytes.getD (31 - i) 0).zeroExtend 64 := by
    rw [hrfB, hreadB, RegFile.get_set_self _ _ _ (by decide)]
  have hx6S : rfS.get .x6 = (addCarryState aBytes bBytes aBytes i).2 := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30),
      hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx6
  have hx29S : rfS.get .x29 = aPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30),
      hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, hx12, hx5]
  have hsum := sumStore_effect aPtr rfS wsS i hi
    (aBytes.getD (31 - i) 0) (bBytes.getD (31 - i) 0)
    (addCarryState aBytes bBytes aBytes i).2 hx30S hx31S hx6S hx29S
  dsimp only at hsum
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hsum
  have hAfinal : A' = bytesRegion bPtr bBytes := by
    rw [hAeqB, hptrB, hrobB, hrestB, sepConj_emp_right']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hi, hlenA, hlenB, hplA, hplB,
    hdisjB, hAfinal⟩
  · rw [hrf', hsx10, hrfB, hreadB,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrf', hsx11, hrfB, hreadB,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  · rw [hrf', hsx12, hrfB, hreadB,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12
  · rw [hrf', hsx5, hrfB, hreadB,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x31), hrfA, hreadA,
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx5
  · rw [hrf', hsx6, addCarryState_succ]
  · rw [hws', hsws, hwsSeq, addCarryState_succ]

private theorem u256AddBeInPlace_retVal_post (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8)) :
    ∀ rf ws A,
      sp Region.empty ⟨aPtr, 32⟩ (.block "retVal" [.MV .x10 .x6])
        (u256AddBeInPlaceLoopPost aPtr bPtr aBytes bBytes) rf ws A →
      (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).post rf ws A := by
  rintro rf ws A ⟨rf₀, ws₀, hws₀, hloop, hrf, hws⟩
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsBytes, hA⟩ := hloop
  subst hrf
  subst hws
  simp only [u256AddBeInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, hwsBytes, hA⟩
  · rw [RegFile.get_set_self _ _ _ (by decide), hx6]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]

theorem u256AddBeInPlace_spec (aPtr bPtr : Word)
    (aBytes bBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨aPtr, 32⟩) (hroB : Region.wf ⟨bPtr, bBytes⟩)
    (base : Word) :
    (u256AddBeInPlaceFn aPtr bPtr aBytes bBytes).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case u256AddBeInPlace.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hpre, hrf, hws⟩
    obtain ⟨hx10, hx11, hx12, hwsOrig, hlenA, hlenB, hplA, hplB, hdisjB, hA⟩ := hpre
    subst hrf
    subst hws
    unfold u256AddBeInPlaceInv
    simp only [u256AddBeInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hwsOrig, by omega, hlenA, hlenB, hplA, hplB,
      hdisjB, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
  case u256AddBeInPlace.loop.inv_step =>
    rintro i hiLt rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, _hnbreak⟩, hrf', hws'⟩ := hsp
    have hb := u256AddBeBeforeInPlace_effect aPtr bPtr aBytes bBytes i rfa wsa A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB,
      hplA, hplB, hdisjB, hA⟩ := hb
    subst hrf'
    subst hws'
    unfold u256AddBeInPlaceInv
    simp only [u256AddBeInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hwsState, by omega, hlenA, hlenB, hplA, hplB,
      hdisjB, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5), hx6]
  case u256AddBeInPlace.loop.exhausted =>
    rintro rf' ws' A' hspbb
    have hb := u256AddBeBeforeInPlace_effect aPtr bPtr aBytes bBytes 31 rf' ws' A' hspbb
    obtain ⟨_, _, _, hx5, _⟩ := hb
    simp only [Cond.holds]
    rw [hx5]
    rfl
  case u256AddBeInPlace.loop.break =>
    rintro i hi rf' ws' A' hspbb hbreak
    have hb := u256AddBeBeforeInPlace_effect aPtr bPtr aBytes bBytes i rf' ws' A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, _hlenA, _hlenB,
      _hplA, _hplB, _hdisjB, hA⟩ := hb
    simp only [Cond.holds, RegFile.get_x0] at hbreak
    have hi31 : i = 31 := by
      rw [hx5] at hbreak
      have hto := congrArg BitVec.toNat hbreak
      rw [idx_toNat i hik] at hto
      change 31 - i = 0 at hto
      omega
    subst hi31
    unfold u256AddBeInPlaceLoopPost u256AddBeCarry u256AddBeBytes
    refine ⟨hx10, hx11, hx12, ?_, hx6, hwsState, hA⟩
    rw [hx5]
    rfl
  case u256AddBeInPlace.loop.before.readA.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf, hwsEq⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB,
      hplA, hplB, hdisjB, hA⟩ := hinv
    dsimp only [u256AddBeInPlaceFn] at hrf hws hws₀ hwsEq ⊢
    have hws32 : ws.length = 32 := hws
    subst hrf
    subst hwsEq
    have haddr : (((rf₀.set Reg.x7 (rf₀.get Reg.x10 + rf₀.get Reg.x5)).set Reg.x28
        (rf₀.get Reg.x11 + rf₀.get Reg.x5)).set Reg.x29
        (rf₀.get Reg.x12 + rf₀.get Reg.x5)).get Reg.x7 =
        aPtr + BitVec.ofNat 64 (31 - i) := by
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10, hx5]
    exact readLbuRwInPlace_blockVCs aPtr _ ws i hi haddr hws32
  case u256AddBeInPlace.loop.before.readB.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rfA, wsA, hlenARead, hreach0, hrfA, hwsA⟩ := hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB,
      hplA, hplB, hdisjB, hA⟩ := hinv
    dsimp only [u256AddBeInPlaceFn] at hrfA hrf0 hwsA hws0 hlenARead hws₀
    have hx11' : rf.get .x11 = bPtr := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x11
        (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx11]
    refine ⟨bBytes, empAssertion, ⟨hx11', rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · rw [hA] at hhp
      rw [hx11', sepConj_emp_right']
      exact hhp
    · rw [hx11']
      exact hroB
  case u256AddBeInPlace.loop.before.readB.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rfA, wsA, hlenARead, hreach0, hrfA, hwsA⟩ := hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB,
      hplA, hplB, hdisjB, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    dsimp only [u256AddBeInPlaceFn] at hrfA hrf0 hwsA hws0 hlenARead hws hws₀ ⊢
    have hws32 : ws.length = 32 := hws
    have haddr : rf.get .x28 = rf.get .x11 + BitVec.ofNat 64 (31 - i) := by
      rw [hrfA,
        execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x28 (by decide),
        execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x11 (by decide),
        hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx11, hx5]
    exact readLbu_blockVCs (rf.get .x11) aPtr rf ws robytes .x31 .x28 i hi haddr hws32
      (by rw [hrob]; exact hlenB) (by rw [hptr]; exact hplB) hplA
      (by rw [hptr]; exact hdisjB)
  case u256AddBeInPlace.loop.before.sumStore.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rfB, wsB, AB, robB, restB, hlenBRead, hreachA, hsatB,
      hroBrel, hrfB, hwsB, hAeqB⟩ := hreach
    obtain ⟨rfA, wsA, hlenARead, hreach0, hrfA, hwsA⟩ := hreachA
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenB,
      hplA, hplB, hdisjB, hA⟩ := hinv
    dsimp only [u256AddBeInPlaceFn] at hrf0 hws0 hlenARead hlenBRead hrfA hrfB hwsA hwsB hws₀ hws ⊢
    have hws32 : ws.length = 32 := hws
    have hx29 : rf.get .x29 = aPtr + BitVec.ofNat 64 (31 - i) := by
      rw [hrfB,
        execBlock_lbu_get_ne _ _ _ _ .x31 .x28 (0 : BitVec 12) .x29 (by decide),
        hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x29
          (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx12, hx5]
    exact sumStore_blockVCs aPtr rf ws i hi hx29 hws32
  case u256AddBeInPlace.post =>
    intro rf ws A h
    exact u256AddBeInPlace_retVal_post aPtr bPtr aBytes bBytes rf ws A h

#print axioms u256AddBe_spec
#print axioms u256AddBeInPlace_spec

end U256AddBeSAsm

end EvmAsm.Codegen
