/-
  EvmAsm.Codegen.Programs.Bls12Fq12ZeroSAsm

  Verified SAsm port of `blq_zero`: zero the 576-byte BLS12-381 FQ12 buffer at `a0`.  The emitted routine is a bottom-test dword loop:
  initialize `x5 = 12`, store a zero dword, advance `a0`, decrement `x5`, and
  branch back while `x5 != 0`.

  The postcondition is the genuine buffer effect: all 576 bytes are zero.  The
  structured `doWhile` body is byte-identical to `blqZero_prog` including
  the trailing `ret` drift guard below.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bls12Fq12

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bls12Fq12Zero576SAsm

def zeroWin576 (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate (8 * i) (0 : BitVec 8) ++ orig.drop (8 * i)

theorem zeroWin576_zero (orig : List (BitVec 8)) : zeroWin576 orig 0 = orig := by
  simp [zeroWin576]

theorem zeroWin576_72_eq (orig : List (BitVec 8)) (h : orig.length = 576) :
    zeroWin576 orig 72 = List.replicate 576 (0 : BitVec 8) := by
  simp only [zeroWin576, Nat.reduceMul,
    List.drop_eq_nil_of_le (by omega : orig.length <= 576), List.append_nil]

theorem length_zeroWin576 (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 576) (hi : i <= 72) : (zeroWin576 orig i).length = 576 := by
  simp only [zeroWin576, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWin576_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 576) (hi : i < 72) :
    setBytes (zeroWin576 orig i) (8 * i) (dwordBytes (0 : Word)) = zeroWin576 orig (i + 1) := by
  rw [zeroWin576]
  rw [setBytes_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hsuf : (orig.drop (8 * i)).length = 576 - 8 * i := by simp [h]
  have hfit : 0 + (dwordBytes (0 : Word)).length <= (orig.drop (8 * i)).length := by
    rw [length_dwordBytes, hsuf]
    omega
  have hslot := setBytes_slot (orig.drop (8 * i)) (dwordBytes (0 : Word)) 0 hfit
  rw [List.drop_zero, length_dwordBytes] at hslot
  have hdrop : (setBytes (orig.drop (8 * i)) 0 (dwordBytes (0 : Word))).drop 8
      = (orig.drop (8 * i)).drop 8 := by
    simpa [length_dwordBytes] using
      (setBytes_drop_of_le (dwordBytes (0 : Word)) (orig.drop (8 * i)) 0 8 (by
        rw [length_dwordBytes]))
  have hset : setBytes (List.drop (8 * i) orig) 0 (dwordBytes (0 : Word))
      = dwordBytes (0 : Word) ++ (List.drop (8 * i) orig).drop 8 := by
    conv_lhs =>
      rw [<- List.take_append_drop 8 (setBytes (List.drop (8 * i) orig) 0 (dwordBytes 0))]
    rw [hslot, hdrop]
  rw [hset]
  rw [show (List.drop (8 * i) orig).drop 8 = orig.drop (8 * (i + 1)) from by
    rw [List.drop_drop]
    congr 1]
  rw [show dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) from by decide]
  simp only [zeroWin576]
  rw [<- List.append_assoc]
  congr 1
  rw [List.replicate_append_replicate]
  congr

def zeroStepBlock : List Instr :=
  [.SD .x10 .x0 (0 : BitVec 12),
   .ADDI .x10 .x10 (8 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x10 (rf.get .x10 + signExtend12 (8 : BitVec 12))
  r1.set .x7 (r1.get .x7 + signExtend12 (-1 : BitVec 12))

theorem zeroStepRf_get_x10 (rf : RegFile) :
    (zeroStepRf rf).get .x10 = rf.get .x10 + signExtend12 (8 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zeroStepRf_get_x7 (rf : RegFile) :
    (zeroStepRf rf).get .x7 =
      rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 72)
    (hx10 : rf.get .x10 = dst + BitVec.ofNat 64 (8 * i)) :
    execBlock reg dst rf ws zeroStepBlock
      = (zeroStepRf rf, setBytes ws (8 * i) (dwordBytes (0 : Word))) := by
  have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  . rfl
  . show setBytes ws ((rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat)
        (dwordBytes (rf.get .x0)) = setBytes ws (8 * i) (dwordBytes (0 : Word))
    rw [haddr, RegFile.get_x0]

def zeroInv (dst : Word) (orig : List (BitVec 8)) :
    Nat -> RegFile -> List (BitVec 8) -> Assertion -> Prop :=
  fun i rf ws _ =>
    rf.get .x10 = dst + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x7 = BitVec.ofNat 64 (72 - (i + 1)) ∧
    i < 72 ∧ orig.length = 576 ∧ ws = zeroWin576 orig (i + 1)

def blqZeroBody (dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x7 (72 : Word)] ;;;
  .doWhile "loop" (.bne .x7 .x0) 71 (zeroInv dst orig)
    (.block "zero" zeroStepBlock)

def blqZeroFn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "blqZero"
  rw := ⟨dst, 576⟩
  pre := fun rf ws _ => rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 576
  post := fun _ ws _ => ws = List.replicate 576 (0 : BitVec 8)
  body := blqZeroBody dst orig

def blqZero_verified : Program :=
  (blqZeroBody 0 []).flatten 0

#guard (blqZero_verified : List Instr).length = 5
#guard (blqZeroBody 0 []).flatten 0 = (blqZeroBody 0 []).flatten 0x80000000
#guard (blqZeroBody 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = blqZero_prog

theorem blqZeroFn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 576⟩) (base : Word) :
    (blqZeroFn dst orig).Spec base := by
  have hbase : (blqZeroFn dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case blqZero.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, rfl, hlen⟩
    simp only [hbase]
    have hx10Init : (execBlock (blqZeroFn dst ws0).region dst rfInit ws0
        [Instr.LI Reg.x7 72]).1.get .x10 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    rw [zero_engine _ dst _ ws0 0 (by omega) (by simpa using hx10Init)]
    refine ⟨?_, ?_, by omega, hlen, ?_⟩
    · rw [zeroStepRf_get_x10, hx10Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [zeroStepRf_get_x7]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
    · change setBytes ws0 (8 * 0) (dwordBytes (0 : Word)) = zeroWin576 ws0 (0 + 1)
      simpa [zeroWin576_zero ws0] using zeroWin576_step ws0 0 hlen (by omega)
  case blqZero.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx5, hlt, hlen, hws₀⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase]
    rw [zero_engine _ dst rf₀ ws₀ (i + 1) (by omega) hx10]
    refine ⟨?_, ?_, by omega, hlen, ?_⟩
    · rw [zeroStepRf_get_x10, hx10, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [zeroStepRf_get_x7, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, zeroWin576_step orig (i + 1) hlen (by omega)]
  case blqZero.loop.exhausted =>
    rintro rf ws A ⟨-, hx5, -, -, -⟩
    simp only [Cond.holds, hx5, not_not, RegFile.get_x0]
    decide
  case blqZero.loop.body.zero.mem =>
    rintro rf ws A hlen (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, -, ⟨hx10, rfl, horiglen⟩, rfl, rfl⟩
      have hlen576 : ws.length = 576 := by
        change ws.length = 576 at hlen
        exact hlen
      have haddr0 : (dst + signExtend12 (0 : BitVec 12) - dst).toNat = 0 := by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      simp only [zeroStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        inRw, hbase, execBlock_cons, execBlock_nil, RegFile.get_set_ne, ne_eq,
        reduceCtorEq, not_false_eq_true, hx10, hlen576, haddr0, and_true]
      constructor
      · omega
      · exact Nat.dvd_zero 8
    · rcases hloop with ⟨i, hi, ⟨hx10, hx5, hlt, horiglen, hws⟩, hcond⟩
      have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * (i + 1) := by
        rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      have hlen576 : ws.length = 576 := by
        change ws.length = 576 at hlen
        exact hlen
      simp only [zeroStepBlock, blockVCs, loadSem, storeSem, inRw, hbase, haddr, hlen576,
        and_true]
      constructor
      · omega
      · exact Nat.dvd_mul_right 8 (i + 1)
  case blqZero.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx5, hlt, hlen, hws⟩, hncond⟩
    have hi71 : i = 71 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi71
    rw [hws, zeroWin576_72_eq orig hlen]
    rfl

end Bls12Fq12Zero576SAsm

end EvmAsm.Codegen
