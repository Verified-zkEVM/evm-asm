/-
  EvmAsm.Codegen.Programs.RunningBloomZeroSAsm

  Verified SAsm port for `running_bloom_zero`.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bloom

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace RunningBloomZeroSAsm

/-- The 256-byte bloom window after zeroing the first `i` dwords. -/
def zeroWin256 (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate (8 * i) (0 : BitVec 8) ++ orig.drop (8 * i)

theorem zeroWin256_zero (orig : List (BitVec 8)) : zeroWin256 orig 0 = orig := by
  simp [zeroWin256]

theorem zeroWin256_32_eq (orig : List (BitVec 8)) (h : orig.length = 256) :
    zeroWin256 orig 32 = List.replicate 256 (0 : BitVec 8) := by
  simp only [zeroWin256, Nat.reduceMul,
    List.drop_eq_nil_of_le (by omega : orig.length <= 256), List.append_nil]

theorem length_zeroWin256 (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 256) (hi : i <= 32) : (zeroWin256 orig i).length = 256 := by
  simp only [zeroWin256, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWin256_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 256) (hi : i < 32) :
    setBytes (zeroWin256 orig i) (8 * i) (dwordBytes (0 : Word)) = zeroWin256 orig (i + 1) := by
  rw [zeroWin256]
  rw [setBytes_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hsuf : (orig.drop (8 * i)).length = 256 - 8 * i := by simp [h]
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
  simp only [zeroWin256]
  rw [<- List.append_assoc]
  congr 1
  rw [List.replicate_append_replicate]
  congr

def zeroStepBlock : List Instr :=
  [.SD .x6 .x0 (0 : BitVec 12),
   .ADDI .x6 .x6 (8 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x6 (rf.get .x6 + signExtend12 (8 : BitVec 12))
  r1.set .x5 (r1.get .x5 + signExtend12 (-1 : BitVec 12))

theorem zeroStepRf_get_x6 (rf : RegFile) :
    (zeroStepRf rf).get .x6 = rf.get .x6 + signExtend12 (8 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zeroStepRf_get_x5 (rf : RegFile) :
    (zeroStepRf rf).get .x5 = rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (8 * i)) :
    execBlock reg dst rf ws zeroStepBlock
      = (zeroStepRf rf, setBytes ws (8 * i) (dwordBytes (0 : Word))) := by
  have haddr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  · rfl
  · show setBytes ws ((rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat)
        (dwordBytes (rf.get .x0)) = setBytes ws (8 * i) (dwordBytes (0 : Word))
    rw [haddr, RegFile.get_x0]

def zeroInv (dst : Word) (orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x6 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    i <= 32 ∧ orig.length = 256 ∧ ws = zeroWin256 orig i

def runningBloomZeroBody (dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (32 : Word), .MV .x6 .x10] ;;;
  .while "loop" (.bne .x5 .x0) 32 (zeroInv dst orig)
    (.block "zero" zeroStepBlock) ;;;
  .block "done" [.LI .x10 (0 : Word)]

def runningBloomZeroFn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "runningBloomZero"
  rw := ⟨dst, 256⟩
  pre := fun rf ws _ => rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 256
  post := fun rf ws _ => rf.get .x10 = 0 ∧ ws = List.replicate 256 (0 : BitVec 8)
  body := runningBloomZeroBody dst orig

def runningBloomZero_verified : Program :=
  (runningBloomZeroBody 0 []).flatten 0

#guard (runningBloomZero_verified : List Instr).length = 8
#guard (runningBloomZeroBody 0 []).flatten 0 = (runningBloomZeroBody 0 []).flatten 0x80000000
#guard (runningBloomZeroBody 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = runningBloomZero_prog

theorem runningBloomZeroFn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 256⟩) (base : Word) :
    (runningBloomZeroFn dst orig).Spec base := by
  have hbase : (runningBloomZeroFn dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case runningBloomZero.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, hws0, hlen⟩
    simp only [hbase]
    refine ⟨?_, ?_, by omega, hlen, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rfl
    · exact hws0.trans (zeroWin256_zero orig).symm
  case runningBloomZero.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx6, hx5, hle, hlen, hws₀⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase]
    have hlt : i < 32 := by
      by_contra hnot
      have hi32 : i = 32 := by omega
      subst hi32
      exact hcond (by simp [hx5])
    rw [zero_engine _ dst rf₀ ws₀ i hlt hx6]
    refine ⟨?_, ?_, by omega, hlen, ?_⟩
    · rw [zeroStepRf_get_x6, hx6, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [zeroStepRf_get_x5, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, zeroWin256_step orig i hlen hlt]
  case runningBloomZero.loop.exhausted =>
    rintro rf ws A ⟨-, hx5, -, -, -⟩
    simp [Cond.holds, hx5]
  case runningBloomZero.loop.body.zero.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx6, hx5, hle, horiglen, hws⟩, hcond⟩
    have hlt : i < 32 := by
      by_contra hnot
      have hi32 : i = 32 := by omega
      subst hi32
      exact hcond (by simp [hx5])
    have haddr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
      rw [hx6, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega
    have hlen256 : ws.length = 256 := by
      change ws.length = 256 at hlen
      exact hlen
    simp only [zeroStepBlock, blockVCs, loadSem, storeSem, inRw, hbase, haddr, hlen256,
      and_true]
    constructor
    · omega
    · exact Nat.dvd_mul_right 8 i
  case runningBloomZero.post =>
    rintro rf ws A ⟨rf₀, ws₀, -, ⟨⟨i, hi, hx6, hx5, hle, hlen, hws⟩, hncond⟩, rfl, rfl⟩
    have hi32 : i = 32 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi32
    refine ⟨?_, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [hws, zeroWin256_32_eq orig hlen]

end RunningBloomZeroSAsm

end EvmAsm.Codegen
