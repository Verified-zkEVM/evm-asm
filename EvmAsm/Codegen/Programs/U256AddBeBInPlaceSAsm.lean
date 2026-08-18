/-
  The K73 call shape for `u256_add_be` has the second operand and output
  aliased.  This is a separate contract from `u256AddBeInPlace`, whose first
  operand is the output.  The emitted loop walks from byte 31 down to byte 0,
  so it reads the aliased byte before overwriting it and the alias is safe.
-/

import EvmAsm.Codegen.GuestLayout
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.U256AddBeSAsm
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256AddBeBInPlaceSAsm

open U256AddBeSAsm

def u256AddBeBInPlaceInv (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = outPtr ∧ rf.get .x12 = outPtr ∧
    rf.get .x5 = BitVec.ofNat 64 (31 - k) ∧
    rf.get .x6 = (addCarryState aBytes orig orig k).2 ∧
    ws = (addCarryState aBytes orig orig k).1 ∧ k ≤ 31 ∧
    aBytes.length = 32 ∧ orig.length = 32 ∧
    aPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat) ∧
    A = bytesRegion aPtr aBytes

def u256AddBeBInPlaceLoopPost (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = outPtr ∧ rf.get .x12 = outPtr ∧
    rf.get .x5 = 0 ∧ rf.get .x6 = u256AddBeCarry aBytes orig orig ∧
    ws = u256AddBeBytes aBytes orig orig ∧ A = bytesRegion aPtr aBytes

def roAInPlace (aPtr : Word) (aBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rest => rf.get .x10 = aPtr ∧ rob = aBytes ∧ rest = empAssertion

def u256AddBeBInPlaceBefore (aPtr _outPtr : Word)
    (aBytes _orig : List (BitVec 8)) : Stmt :=
  .block "addr" [.ADD .x7 .x10 .x5, .ADD .x28 .x11 .x5,
    .ADD .x29 .x12 .x5] ;;;
  .readAt "readA" .x10 (roAInPlace aPtr aBytes)
    [.LBU .x30 .x7 (0 : BitVec 12)] ;;;
  .block "readB" [.LBU .x31 .x28 (0 : BitVec 12)] ;;;
  .block "sumStore" [.ADD .x30 .x30 .x31,
    .ADD .x30 .x30 .x6, .SRLI .x6 .x30 (8 : BitVec 6),
    .ANDI .x30 .x30 (255 : BitVec 12), .SB .x29 .x30 (0 : BitVec 12)]

def u256AddBeBInPlaceBody (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (31 : Word), .LI .x6 (0 : Word)] ;;;
  .«doWhileBreak» "loop" 31 (u256AddBeBInPlaceInv aPtr outPtr aBytes orig)
    (u256AddBeBInPlaceLoopPost aPtr outPtr aBytes orig)
    (u256AddBeBInPlaceBefore aPtr outPtr aBytes orig)
    (.beq .x5 .x0)
    (.block "dec" [.ADDI .x5 .x5 (-1 : BitVec 12)]) ;;;
  .block "retVal" [.MV .x10 .x6]

def u256AddBeBInPlaceFn (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8)) : Fn where
  name := "u256AddBeBInPlace"
  region := Region.empty
  rw := ⟨outPtr, 32⟩
  pre := fun rf ws A =>
    rf.get .x10 = aPtr ∧ rf.get .x11 = outPtr ∧ rf.get .x12 = outPtr ∧
    ws = orig ∧ aBytes.length = 32 ∧ orig.length = 32 ∧
    aPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
    (aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat) ∧
    A = bytesRegion aPtr aBytes
  post := fun rf ws A =>
    rf.get .x10 = u256AddBeCarry aBytes orig orig ∧
    rf.get .x11 = outPtr ∧ rf.get .x12 = outPtr ∧
    ws = u256AddBeBytes aBytes orig orig ∧ A = bytesRegion aPtr aBytes
  body := u256AddBeBInPlaceBody aPtr outPtr aBytes orig

theorem u256AddBeBInPlaceBody_flatten (L : GuestLayout) :
    (u256AddBeBInPlaceBody 0 0 [] []).flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = u256AddBe_prog_of L := rfl

private theorem addCarryState_unprocessed_orig (a b orig : List (BitVec 8))
    (k j : Nat) (hj : j < 32 - k) :
    (addCarryState a b orig k).1.getD j 0 = orig.getD j 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [addCarryState_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne]
      · apply ih
        omega
      · omega

private theorem execBlock_lbu_rw_b (outPtr : Word) (rf : RegFile)
    (ws aBytes orig : List (BitVec 8)) (i : Nat) (hi : i ≤ 31)
    (haddr : rf.get .x28 = outPtr + BitVec.ofNat 64 (31 - i))
    (hws : ws = (addCarryState aBytes orig orig i).1)
    (hlen : orig.length = 32) :
    execBlock Region.empty outPtr rf ws
      [.LBU .x31 .x28 (0 : BitVec 12)] =
      (rf.set .x31 ((orig.getD (31 - i) 0).zeroExtend 64), ws) := by
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ (31 - i)
    (by
      rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      have hidx := add_idx_sub_self outPtr i hi
      bv_omega)
    (by
      rw [hws, addCarryState_length, hlen]
      omega), execBlock_nil]
  rw [hws, addCarryState_unprocessed_orig aBytes orig orig i (31 - i) (by omega)]

private theorem readLbuRwBInPlace_blockVCs (outPtr : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i ≤ 31)
    (haddr : rf.get .x28 = outPtr + BitVec.ofNat 64 (31 - i))
    (hws : ws.length = 32) :
    blockVCs Region.empty outPtr rf ws
      [.LBU .x31 .x28 (0 : BitVec 12)] := by
  have haddr0 : rf.get .x28 + signExtend12 (0 : BitVec 12) =
      outPtr + BitVec.ofNat 64 (31 - i) := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw outPtr ws (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1
    then _ else Region.empty.loadOk _ _)
  rw [haddr0, if_pos]
  · unfold Region.loadOk
    change 1 ∣ (outPtr + BitVec.ofNat 64 (31 - i) - outPtr).toNat ∧
      (outPtr + BitVec.ofNat 64 (31 - i) - outPtr).toNat + 1 ≤ ws.length
    rw [add_idx_sub_self outPtr i hi, hws]
    exact ⟨one_dvd _, by omega⟩
  · unfold inRw
    rw [add_idx_sub_self outPtr i hi, hws]
    omega

private theorem u256AddBeBInPlaceBefore_effect (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨outPtr, 32⟩
        (u256AddBeBInPlaceBefore aPtr outPtr aBytes orig)
        (u256AddBeBInPlaceInv aPtr outPtr aBytes orig i) rf' ws' A' →
      rf'.get .x10 = aPtr ∧ rf'.get .x11 = outPtr ∧ rf'.get .x12 = outPtr ∧
      rf'.get .x5 = BitVec.ofNat 64 (31 - i) ∧
      rf'.get .x6 = (addCarryState aBytes orig orig (i + 1)).2 ∧
      ws' = (addCarryState aBytes orig orig (i + 1)).1 ∧
      i ≤ 31 ∧ aBytes.length = 32 ∧ orig.length = 32 ∧
      aPtr.toNat + 32 < 2 ^ 64 ∧ outPtr.toNat + 32 < 2 ^ 64 ∧
      (aPtr.toNat + 32 ≤ outPtr.toNat ∨ outPtr.toNat + 32 ≤ aPtr.toNat) ∧
      A' = bytesRegion aPtr aBytes := by
  intro rf' ws' A' hsp
  unfold u256AddBeBInPlaceBefore at hsp
  obtain ⟨rfS, wsS, hwsS, hreachB, hrf', hws'⟩ := hsp
  obtain ⟨rfB, wsB, hwsB0, hreachA, hrfB, hwsB⟩ := hreachB
  obtain ⟨rfA, wsA, AA, robA, restA, hlenARead, hreach0, _hsatA,
    hroArel, hrfA, hwsA, hAeqA⟩ := hreachA
  obtain ⟨rf0, ws0, hws0, hinv, hrf0, hws0eq⟩ := hreach0
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hi, hlenA, hlenO,
    hplA, hplO, hdisjA, hA⟩ := hinv
  obtain ⟨hptrA, hrobA, hrestA⟩ := hroArel
  dsimp only [u256AddBeBInPlaceFn] at hlenARead hrf0 hws0eq hrfA hwsA hrfB hwsB hrf' hws'
  have haddrA : rfA.get .x7 = aPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, hx10, hx5]
  have hreadA : execBlock { base := rfA.get .x10, bytes := robA } outPtr rfA wsA
      [.LBU .x30 .x7 (0 : BitVec 12)] =
      (rfA.set .x30 ((aBytes.getD (31 - i) 0).zeroExtend 64), wsA) := by
    rw [hrobA]
    apply execBlock_lbu_ro_idx
    · exact hi
    · rw [haddrA, hptrA]
    · exact hlenARead
    · rw [hptrA]
      exact hplA
    · exact hplO
    · rw [hptrA]
      exact hdisjA
  have hwsAeq : wsB = wsA := by
    rw [hwsA, execBlock_lbu_ws]
  have haddrB : rfB.get .x28 = outPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, hx11, hx5]
  have hreadB : execBlock Region.empty outPtr rfB wsB
      [.LBU .x31 .x28 (0 : BitVec 12)] =
      (rfB.set .x31 ((orig.getD (31 - i) 0).zeroExtend 64), wsB) := by
    apply execBlock_lbu_rw_b outPtr rfB wsB aBytes orig i hi haddrB
    · rw [hwsAeq, hws0eq]
      exact hwsState
    · exact hlenO
  have hwsSeq : wsS = (addCarryState aBytes orig orig i).1 := by
    rw [hwsB, hwsAeq, hws0eq]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    exact hwsState
  have hx30S : rfS.get .x30 = (aBytes.getD (31 - i) 0).zeroExtend 64 := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x30 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_self _ _ _ (by decide)]
  have hx31S : rfS.get .x31 = (orig.getD (31 - i) 0).zeroExtend 64 := by
    rw [hrfB, hreadB, RegFile.get_set_self _ _ _ (by decide)]
  have hx6S : rfS.get .x6 = (addCarryState aBytes orig orig i).2 := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx6
  have hx29S : rfS.get .x29 = outPtr + BitVec.ofNat 64 (31 - i) := by
    rw [hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, hx12, hx5]
  have hsum := sumStore_effect outPtr rfS wsS i hi
    (aBytes.getD (31 - i) 0) (orig.getD (31 - i) 0)
    (addCarryState aBytes orig orig i).2 hx30S hx31S hx6S hx29S
  dsimp only at hsum
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hsum
  have hAfinal : A' = bytesRegion aPtr aBytes := by
    rw [hAeqA, hptrA, hrobA, hrestA, sepConj_emp_right']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hi, hlenA, hlenO, hplA, hplO, hdisjA,
    hAfinal⟩
  · rw [hrf', hsx10, hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrf', hsx11, hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  · rw [hrf', hsx12, hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12
  · rw [hrf', hsx5, hrfB, hreadB, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x31),
      hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30), hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx5
  · rw [hrf', hsx6, addCarryState_succ]
  · rw [hws', hsws, hwsSeq, addCarryState_succ]

theorem u256AddBeBInPlace_retVal_post (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8)) :
    ∀ rf ws A,
      sp Region.empty ⟨outPtr, 32⟩ (.block "retVal" [.MV .x10 .x6])
        (u256AddBeBInPlaceLoopPost aPtr outPtr aBytes orig) rf ws A →
      (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).post rf ws A := by
  rintro rf ws A ⟨rf₀, ws₀, hws₀, hloop, hrf, hws⟩
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsBytes, hA⟩ := hloop
  subst hrf
  subst hws
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [RegFile.get_set_self _ _ _ (by decide), hx6]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]
  · exact hwsBytes
  · exact hA

theorem u256AddBeBInPlace_spec (aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩)
    (base : Word) :
    (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case u256AddBeBInPlace.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hws₀, hpre, hrf, hws⟩
    obtain ⟨hx10, hx11, hx12, hwsOrig, hlenA, hlenO, hplA, hplO, hdisjA, hA⟩ := hpre
    subst hrf
    subst hws
    unfold u256AddBeBInPlaceInv
    simp only [u256AddBeBInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hwsOrig, by omega, hlenA, hlenO, hplA, hplO,
      hdisjA, hA⟩
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
  case u256AddBeBInPlace.loop.inv_step =>
    rintro i hiLt rf' ws' A' hsp
    obtain ⟨rfa, wsa, hwsa, ⟨hspbb, _hnbreak⟩, hrf', hws'⟩ := hsp
    have hb := u256AddBeBInPlaceBefore_effect aPtr outPtr aBytes orig i rfa wsa A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hb
    subst hrf'
    subst hws'
    unfold u256AddBeBInPlaceInv
    simp only [u256AddBeBInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, hwsState, by omega, hlenA, hlenO, hplA, hplO,
      hdisjA, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      bv_omega
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5), hx6]
  case u256AddBeBInPlace.loop.exhausted =>
    rintro rf' ws' A' hspbb
    have hb := u256AddBeBInPlaceBefore_effect aPtr outPtr aBytes orig 31 rf' ws' A' hspbb
    obtain ⟨_, _, _, hx5, _⟩ := hb
    simp only [Cond.holds]
    rw [hx5]
    rfl
  case u256AddBeBInPlace.loop.break =>
    rintro i hi rf' ws' A' hspbb hbreak
    have hb := u256AddBeBInPlaceBefore_effect aPtr outPtr aBytes orig i rf' ws' A' hspbb
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, _hlenA, _hlenO,
      _hplA, _hplO, _hdisjA, hA⟩ := hb
    simp only [Cond.holds, RegFile.get_x0] at hbreak
    have hi31 : i = 31 := by
      rw [hx5] at hbreak
      have hto := congrArg BitVec.toNat hbreak
      rw [idx_toNat i hik] at hto
      change 31 - i = 0 at hto
      omega
    subst hi31
    unfold u256AddBeBInPlaceLoopPost u256AddBeCarry u256AddBeBytes
    refine ⟨hx10, hx11, hx12, ?_, hx6, hwsState, hA⟩
    rw [hx5]
    rfl
  case u256AddBeBInPlace.loop.before.readA.focus =>
    rintro rf ws A hreach hApc hp hhp
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf, hws⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hinv
    dsimp only [u256AddBeBInPlaceFn] at hrf hws hws₀
    subst hrf
    subst hws
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true] at hhp ⊢
    refine ⟨aBytes, empAssertion, ⟨?_, rfl, rfl⟩, ?_, pcFree_emp, ?_⟩
    · exact hx10
    · rw [hA] at hhp
      rw [hx10, sepConj_emp_right']
      exact hhp
    · rw [hx10]
      exact hroA
  case u256AddBeBInPlace.loop.before.readA.mem =>
    rintro rf ws A robytes rest hws hreach hro hsat
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf, hwsEq⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hinv
    obtain ⟨hptr, hrob, hrest⟩ := hro
    dsimp only [u256AddBeBInPlaceFn] at hrf hws hws₀ hwsEq ⊢
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
      (by rw [hrob]; exact hlenA) (by rw [hptr]; exact hplA) hplO
      (by rw [hptr]; exact hdisjA)
  case u256AddBeBInPlace.loop.before.readB.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rfA, wsA, AA, robA, restA, hlenARead, hreach0, _hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hinv
    dsimp only [u256AddBeBInPlaceFn] at hrfA hrf0 hwsA hws0 hlenARead hws₀ hws ⊢
    have hws32 : ws.length = 32 := hws
    have haddr : rf.get .x28 = rf.get .x11 + BitVec.ofNat 64 (31 - i) := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x28 (by decide),
        execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x11 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx11, hx5]
    have hx11r : rf.get .x11 = outPtr := by
      rw [hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x11
        (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx11]
    have haddr' : rf.get .x28 = outPtr + BitVec.ofNat 64 (31 - i) := by
      rw [haddr, hx11r]
    exact readLbuRwBInPlace_blockVCs outPtr rf ws i hi haddr' hws32
  case u256AddBeBInPlace.loop.before.sumStore.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rfB, wsB, hwsB, hreachA, hrfB, hwsB'⟩ := hreach
    obtain ⟨rfA, wsA, AA, robA, restA, hlenARead, hreach0, _hsatA,
      hroArel, hrfA, hwsA, hAeqA⟩ := hreachA
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv⟩, hrf0, hws0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hlenA, hlenO,
      hplA, hplO, hdisjA, hA⟩ := hinv
    dsimp only [u256AddBeBInPlaceFn] at hrf0 hws0 hlenARead hrfA hrfB hwsA hwsB' hws₀ hws ⊢
    have hws32 : ws.length = 32 := hws
    have hx29 : rf.get .x29 = outPtr + BitVec.ofNat 64 (31 - i) := by
      rw [hrfB, execBlock_lbu_get_ne _ _ _ _ .x31 .x28 (0 : BitVec 12) .x29 (by decide),
        hrfA, execBlock_lbu_get_ne _ _ _ _ .x30 .x7 (0 : BitVec 12) .x29 (by decide), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true, hx12, hx5]
    exact sumStore_blockVCs outPtr rf ws i hi hx29 hws32
  case u256AddBeBInPlace.post =>
    intro rf ws A h
    exact u256AddBeBInPlace_retVal_post aPtr outPtr aBytes orig rf ws A h

def u256AddBeBInPlaceCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.u256_add_be : Word) (u256AddBe_prog_of .zero)

def u256AddBeBInPlaceScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_u256AddB (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
        (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf u256AddBeBInPlaceScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [u256AddBeBInPlaceScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem u256AddB_args_notin_scratch :
    ∀ r ∈ u256AddBeBInPlaceScratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide

theorem u256AddBeBInPlaceFlat_spec (ret aPtr outPtr : Word)
    (aBytes orig : List (BitVec 8))
    (hrw : RwRegion.wf ⟨outPtr, 32⟩)
    (hroA : Region.wf ⟨aPtr, aBytes⟩)
    (hlenA : aBytes.length = 32)
    (hlenOrig : orig.length = 32)
    (hovA : aPtr.toNat + 32 < 2 ^ 64)
    (hovOut : outPtr.toNat + 32 < 2 ^ 64)
    (hdisj : aPtr.toNat + 32 ≤ outPtr.toNat ∨
      outPtr.toNat + 32 ≤ aPtr.toNat)
    (hsz : 4 * ((u256AddBeBInPlaceFn aPtr outPtr aBytes orig).body.size + 1)
      ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((u256AddBeBInPlaceFn aPtr outPtr aBytes orig).body.steps + 1)
      (GuestAddrs.u256_add_be : Word) ret u256AddBeBInPlaceCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ aPtr) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch ** bytesRegion outPtr orig **
        bytesRegion aPtr aBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        (.x10 ↦ᵣ u256AddBeCarry aBytes orig orig) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        regOwns u256AddBeBInPlaceScratch **
        bytesRegion outPtr (u256AddBeBytes aBytes orig orig) **
        bytesRegion aPtr aBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns u256AddBeBInPlaceScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ aPtr) **
        (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) ** bytesRegion outPtr orig **
        bytesRegion aPtr aBytes)
      (fun vf => ?_))
  have hpre : (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).pre
      (fun r => if r = .x10 then aPtr else
        if r = .x11 then outPtr else if r = .x12 then outPtr else vf r)
      orig (bytesRegion aPtr aBytes) := by
    refine ⟨?_, ?_, ?_, rfl, hlenA, hlenOrig, hovA, hovOut, hdisj, rfl⟩
    · show RegFile.get _ .x10 = aPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = outPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = outPtr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (u256AddBeBInPlaceFn aPtr outPtr aBytes orig)
    (GuestAddrs.u256_add_be : Word)
    (u256AddBeBInPlace_spec aPtr outPtr aBytes orig hrw hroA
      (GuestAddrs.u256_add_be : Word))
    hsz ret halign
    (fun r => if r = .x10 then aPtr else
      if r = .x11 then outPtr else if r = .x12 then outPtr else vf r)
    orig (bytesRegion aPtr aBytes)
    (bytesRegion_pcFree aPtr aBytes)
    (by exact hlenOrig) hpre
    (Q := (((.x10 ↦ᵣ u256AddBeCarry aBytes orig orig) **
          (.x11 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
          regOwns u256AddBeBInPlaceScratch) **
        bytesRegion outPtr (u256AddBeBytes aBytes orig orig)) **
      bytesRegion aPtr aBytes)
    (fun _ _ _ hpost => hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hx10', hx11', hx12', hws', _hA⟩ := hpost
      subst ws'
      have g10 : rf' .x10 = u256AddBeCarry aBytes orig orig := by
        rw [← hx10', RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have g11 : rf' .x11 = outPtr := by
        rw [← hx11', RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      have g12 : rf' .x12 = outPtr := by
        rw [← hx12', RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_u256AddB, g10, g11, g12] at hh
      rw [show (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).rw.base = outPtr
        from rfl] at hh
      have hh1 :
          (((((((.x10 : Reg) ↦ᵣ u256AddBeCarry aBytes orig orig) **
            (.x11 ↦ᵣ outPtr)) ** (.x12 ↦ᵣ outPtr)) **
            bytesRegion outPtr (u256AddBeBytes aBytes orig orig)) **
            bytesRegion aPtr aBytes) **
            regAtomsOf (fun r => rf' r) u256AddBeBInPlaceScratch) hp := by
        xperm_hyp hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) u256AddBeBInPlaceScratch) hp hh1
      xperm_hyp hh2)
  rw [show (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).programRet
      (GuestAddrs.u256_add_be : Word) = u256AddBe_prog_of .zero from rfl] at had
  rw [show (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).region = Region.empty from rfl,
    show (u256AddBeBInPlaceFn aPtr outPtr aBytes orig).rw.base = outPtr from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_u256AddB,
    show (if (Reg.x10 : Reg) = .x10 then aPtr else _) = aPtr
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then aPtr else
      if (Reg.x11 : Reg) = .x11 then outPtr else _) = outPtr from by
      rw [if_neg (by decide), if_pos rfl],
    show (if (Reg.x12 : Reg) = .x10 then aPtr else
      if (Reg.x12 : Reg) = .x11 then outPtr else
      if (Reg.x12 : Reg) = .x12 then outPtr else _) = outPtr from by
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl],
    regAtomsOf_congr
      (fun r => if r = .x10 then aPtr else
        if r = .x11 then outPtr else if r = .x12 then outPtr else vf r)
      vf u256AddBeBInPlaceScratch
      (fun r hr => by
        obtain ⟨h10, h11, h12⟩ := u256AddB_args_notin_scratch r hr
        show (if r = .x10 then aPtr else
          if r = .x11 then outPtr else if r = .x12 then outPtr else vf r) = vf r
        rw [if_neg h10, if_neg h11, if_neg h12])] at had
  simp only [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end U256AddBeBInPlaceSAsm

end EvmAsm.Codegen
