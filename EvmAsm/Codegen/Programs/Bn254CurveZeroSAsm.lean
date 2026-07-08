/-
  EvmAsm.Codegen.Programs.Bn254CurveZeroSAsm

  Verified SAsm port of `bnc_zero64`: zero a 64-byte BN254 affine point
  buffer using the emitted alignment-free byte loop.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Curve

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254CurveZeroSAsm

/-- The 64-byte destination window after zeroing the first `i` bytes. -/
def zeroWin64 (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate i (0 : BitVec 8) ++ orig.drop i

theorem zeroWin64_zero (orig : List (BitVec 8)) : zeroWin64 orig 0 = orig := by
  simp [zeroWin64]

theorem zeroWin64_64_eq (orig : List (BitVec 8)) (h : orig.length = 64) :
    zeroWin64 orig 64 = List.replicate 64 (0 : BitVec 8) := by
  simp only [zeroWin64, List.drop_eq_nil_of_le (by omega : orig.length <= 64), List.append_nil]

theorem length_zeroWin64 (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 64) (hi : i <= 64) : (zeroWin64 orig i).length = 64 := by
  simp only [zeroWin64, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWin64_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 64) (hi : i < 64) :
    setBytes (zeroWin64 orig i) i [(0 : BitVec 8)] = zeroWin64 orig (i + 1) := by
  rw [setBytes_singleton]
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [zeroWin64]
  rw [hdrop]
  simp only [List.set_append_right, List.length_replicate, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero]
  rw [show List.replicate i (0 : BitVec 8) ++ 0 :: List.drop (i + 1) orig =
      (List.replicate i 0 ++ [0]) ++ List.drop (i + 1) orig from by simp]
  rw [show List.replicate i (0 : BitVec 8) ++ [0] = List.replicate (i + 1) 0 from by
    rw [← List.replicate_append_replicate]
    congr]

def zeroStepBlock : List Instr :=
  [.SB .x10 .x0 (0 : BitVec 12),
   .ADDI .x10 .x10 (1 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x10 (rf.get .x10 + signExtend12 (1 : BitVec 12))
  r1.set .x5 (r1.get .x5 + signExtend12 (-1 : BitVec 12))

theorem zeroStepRf_get_x10 (rf : RegFile) :
    (zeroStepRf rf).get .x10 = rf.get .x10 + signExtend12 (1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem zeroStepRf_get_x5 (rf : RegFile) :
    (zeroStepRf rf).get .x5 = rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 64)
    (hx10 : rf.get .x10 = dst + BitVec.ofNat 64 i) :
    execBlock reg dst rf ws zeroStepBlock =
      (zeroStepRf rf, setBytes ws i [(0 : BitVec 8)]) := by
  have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  rw [show zeroStepBlock = [.SB .x10 .x0 0, .ADDI .x10 .x10 1,
      .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i haddr]
  dsimp only
  rw [RegFile.get_x0]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold zeroStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10)]
  rfl

def zeroInv (dst : Word) (orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = dst + BitVec.ofNat 64 i ∧
    rf.get .x5 = BitVec.ofNat 64 (64 - i) ∧
    i <= 64 ∧ orig.length = 64 ∧ ws = zeroWin64 orig i

def bncZero64Body (dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (64 : Word)] ;;;
  .while "loop" (.bne .x5 .x0) 64 (zeroInv dst orig)
    (.block "zero" zeroStepBlock)

def bncZero64Fn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "bncZero64"
  rw := ⟨dst, 64⟩
  pre := fun rf ws _ => rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 64
  post := fun _ ws _ => ws = List.replicate 64 (0 : BitVec 8)
  body := bncZero64Body dst orig

def bncZero64_verified : Program := (bncZero64Body 0 []).flatten 0

#guard (bncZero64_verified : List Instr).length = 6
#guard (bncZero64Body 0 []).flatten 0 = (bncZero64Body 0 []).flatten 0x80000000
#guard (bncZero64Body 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = bncZero64_prog

theorem bncZero64Fn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 64⟩) (base : Word) :
    (bncZero64Fn dst orig).Spec base := by
  have hbase : (bncZero64Fn dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case bncZero64.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, hws0, hlen⟩
    simp only [hbase]
    refine ⟨?_, ?_, by omega, hlen, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true, hx10]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
    · exact hws0.trans (zeroWin64_zero orig).symm
  case bncZero64.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx5, hle, hlen, hws₀⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase]
    have hlt : i < 64 := by
      by_contra hnot
      have hi64 : i = 64 := by omega
      subst hi64
      exact hcond (by simp [hx5])
    rw [zero_engine _ dst rf₀ ws₀ i hlt hx10]
    refine ⟨?_, ?_, by omega, hlen, ?_⟩
    · rw [zeroStepRf_get_x10, hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [zeroStepRf_get_x5, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, zeroWin64_step orig i hlen hlt]
  case bncZero64.loop.exhausted =>
    rintro rf ws A ⟨-, hx5, -, -, -⟩
    simp [Cond.holds, hx5]
  case bncZero64.loop.body.zero.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx10, hx5, hle, horiglen, hws⟩, hcond⟩
    have hlt : i < 64 := by
      by_contra hnot
      have hi64 : i = 64 := by omega
      subst hi64
      exact hcond (by simp [hx5])
    have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hlen64 : ws.length = 64 := by
      change ws.length = 64 at hlen
      exact hlen
    simp only [zeroStepBlock, blockVCs, loadSem, storeSem, inRw, hbase, haddr, hlen64,
      and_true]
    omega
  case bncZero64.post =>
    rintro rf ws A ⟨⟨i, hi, hx10, hx5, hle, hlen, hws⟩, hncond⟩
    have hi64 : i = 64 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi64
    rw [hws, zeroWin64_64_eq orig hlen]
    rfl

end Bn254CurveZeroSAsm

end EvmAsm.Codegen
