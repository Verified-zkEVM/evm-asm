/-
  EvmAsm.Codegen.Programs.Secp256k1PointCopy64SAsm

  Verified SAsm port of `secp256k1_point_copy64`: copy a 64-byte secp256k1 affine point
  buffer from `a0` to `a1` using the emitted alignment-free byte loop.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Secp256k1Curve

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Secp256k1PointCopy64SAsm

def frameOk64 (src dst : Word) : Prop :=
  src.toNat + 64 < 2 ^ 64 ∧ dst.toNat + 64 < 2 ^ 64 ∧
    (src.toNat + 64 ≤ dst.toNat ∨ dst.toNat + 64 ≤ src.toNat)

def copyWin64 (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take i ++ orig.drop i

theorem copyWin64_zero (srcBytes orig : List (BitVec 8)) :
    copyWin64 srcBytes orig 0 = orig := by
  simp [copyWin64]

theorem copyWin64_64_eq (srcBytes orig : List (BitVec 8))
    (hs : srcBytes.length = 64) (ho : orig.length = 64) :
    copyWin64 srcBytes orig 64 = srcBytes := by
  simp only [copyWin64]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem length_copyWin64 (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 64) (ho : orig.length = 64) (hi : i ≤ 64) :
    (copyWin64 srcBytes orig i).length = 64 := by
  simp only [copyWin64, List.length_append, List.length_take, List.length_drop, hs, ho]
  omega

theorem copyWin64_step (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 64) (ho : orig.length = 64) (hi : i < 64) :
    setBytes (copyWin64 srcBytes orig i) i [srcBytes.getD i 0] =
      copyWin64 srcBytes orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : (srcBytes.take i).length = i := by simp only [List.length_take, hs]; omega
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [copyWin64]
  rw [hdrop]
  have hgetD : srcBytes.getD i 0 = srcBytes.get ⟨i, by omega⟩ := by
    unfold List.getD
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  have hone : (srcBytes.drop i).take 1 = [srcBytes.getD i 0] := by
    rw [List.take_one_drop_eq_of_lt_length (l := srcBytes) (n := i) (by omega), hgetD]
  have hsrc : srcBytes.take (i + 1) = srcBytes.take i ++ [srcBytes.getD i 0] := by
    rw [List.take_add, hone]
  rw [hsrc]
  simp only [List.set_append_right, hpre, Nat.le_refl, Nat.sub_self, List.set_cons_zero,
    List.singleton_append, List.append_assoc]

private theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

private theorem src_miss1 (src dst : Word) (ws : List (BitVec 8)) (i : Nat)
    (hi : i < 64) (hws : ws.length = 64) (hfr : frameOk64 src dst) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 i) 1 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

private theorem src_byteAt (src : Word) (srcBytes : List (BitVec 8)) (i : Nat)
    (hi : i < 64) :
    Region.byteAt ⟨src, srcBytes⟩ (src + BitVec.ofNat 64 i) = srcBytes.getD i 0 := by
  unfold Region.byteAt
  have hi64 : i < 2 ^ 64 := by omega
  rw [show (src + BitVec.ofNat 64 i - src).toNat = i by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]

def copyStepBlock : List Instr :=
  [.LBU .x6 .x10 (0 : BitVec 12), .SB .x11 .x6 (0 : BitVec 12),
   .ADDI .x10 .x10 (1 : BitVec 12), .ADDI .x11 .x11 (1 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

def copyStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x6 (b.zeroExtend 64)
  let r2 := r1.set .x10 (r1.get .x10 + signExtend12 (1 : BitVec 12))
  let r3 := r2.set .x11 (r2.get .x11 + signExtend12 (1 : BitVec 12))
  r3.set .x5 (r3.get .x5 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x10 = rf.get .x10 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x11 = rf.get .x11 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x5 = rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem copy_engine (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 64)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 i)
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 i)
    (hws : ws.length = 64) (hfr : frameOk64 src dst) :
    execBlock ⟨src, srcBytes⟩ dst rf ws copyStepBlock =
      (copyStepRf rf (srcBytes.getD i 0), setBytes ws i [srcBytes.getD i 0]) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x10 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 i := by
    rw [hx10, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 i) 1 := src_miss1 src dst ws i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x6 ((srcBytes.getD i 0).zeroExtend 64)).get .x11
      + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), hx11, hse0]
    bv_omega
  rw [show copyStepBlock = [.LBU .x6 .x10 0, .SB .x11 .x6 0,
      .ADDI .x10 .x10 1, .ADDI .x11 .x11 1, .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ .x6 .x10 (0 : BitVec 12) hmissExact,
    hloadAddr, src_byteAt src srcBytes i hi]
  dsimp only
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i hstoreAddr]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0), truncate_zeroExtend_byte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold copyStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6)]

private theorem copy_blockVCs (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 64)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 i)
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 i)
    (hws : ws.length = 64) (hs : srcBytes.length = 64) (hfr : frameOk64 src dst) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws copyStepBlock := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x10 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 i := by
    rw [hx10, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 i) 1 := src_miss1 src dst ws i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x6 ((Region.byteAt ⟨src, srcBytes⟩
        (rf.get .x10 + signExtend12 (0 : BitVec 12))).zeroExtend 64)).get .x11
      + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), hx11, hse0]
    bv_omega
  have hsrcOff : (src + BitVec.ofNat 64 i - src).toNat = i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [show copyStepBlock = [.LBU .x6 .x10 0, .SB .x11 .x6 0,
      .ADDI .x10 .x10 1, .ADDI .x11 .x11 1, .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
  refine ⟨?_, ?_⟩
  · show (if inRw dst ws (rf.get .x10 + signExtend12 0) 1 then _ else Region.loadOk _ _ _)
    rw [if_neg hmissExact]
    rw [hloadAddr]
    unfold Region.loadOk
    constructor
    · simp
    · change (src + BitVec.ofNat 64 i - src).toNat + 1 ≤ srcBytes.length
      rw [hsrcOff, hs]
      omega
  · rw [execInstrRF_lbu_ro _ _ _ _ .x6 .x10 (0 : BitVec 12) hmissExact]
    simp only [blockVCs, loadSem, storeSem]
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [hstoreAddr, hws]
      omega
    · exact ⟨trivial, trivial, trivial, trivial⟩

def copyInv (src dst : Word) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = src + BitVec.ofNat 64 i ∧
    rf.get .x11 = dst + BitVec.ofNat 64 i ∧
    rf.get .x5 = BitVec.ofNat 64 (64 - i) ∧
    i ≤ 64 ∧ srcBytes.length = 64 ∧ orig.length = 64 ∧ frameOk64 src dst ∧
    ws = copyWin64 srcBytes orig i

def secp256k1PointCopy64Body (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (64 : Word)] ;;;
  .while "loop" (.bne .x5 .x0) 64 (copyInv src dst srcBytes orig)
    (.block "copy" copyStepBlock)

def secp256k1PointCopy64Fn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "secp256k1PointCopy64"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 64⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧
    srcBytes.length = 64 ∧ orig.length = 64 ∧ frameOk64 src dst
  post := fun _ ws _ => ws = srcBytes
  body := secp256k1PointCopy64Body src dst srcBytes orig

def secp256k1PointCopy64_verified : Program := (secp256k1PointCopy64Body 0 0 [] []).flatten 0

#guard (secp256k1PointCopy64_verified : List Instr).length = 8
#guard (secp256k1PointCopy64Body 0 0 [] []).flatten 0 = (secp256k1PointCopy64Body 0 0 [] []).flatten 0x80000000
#guard (secp256k1PointCopy64Body 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = secp256k1PointCopy64_prog

theorem secp256k1PointCopy64Fn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 64⟩) (base : Word) :
    (secp256k1PointCopy64Fn src dst srcBytes orig).Spec base := by
  have hbase : (secp256k1PointCopy64Fn src dst srcBytes orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case secp256k1PointCopy64.loop.inv_init =>
    rintro rf' ws' A' ⟨rf₀, ws₀, -, ⟨hx10, hx11, hws0, hs, ho, hfr⟩, rfl, rfl⟩
    simp only [hbase]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx10]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx11]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
    · exact hws0.trans (copyWin64_zero srcBytes orig).symm
  case secp256k1PointCopy64.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx11, hx5, hle, hs, ho, hfr, hws₀⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase, show (secp256k1PointCopy64Fn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl]
    have hlt : i < 64 := by
      by_contra hnot
      have hi64 : i = 64 := by omega
      subst hi64
      exact hcond (by simp [hx5])
    have hwsLen : ws₀.length = 64 := by
      rw [hws₀]
      exact length_copyWin64 srcBytes orig i hs ho hle
    rw [copy_engine src dst srcBytes rf₀ ws₀ i hlt hx10 hx11 hwsLen hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_⟩
    · rw [copyStepRf_get_x10, hx10, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [copyStepRf_get_x11, hx11, show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from by decide]
      omega
    · rw [copyStepRf_get_x5, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, copyWin64_step srcBytes orig i hs ho hlt]
  case secp256k1PointCopy64.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx5, -, -, -, -, -⟩
    simp [Cond.holds, hx5]
  case secp256k1PointCopy64.loop.body.copy.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx10, hx11, hx5, hle, hs, ho, hfr, hws⟩, hcond⟩
    have hlt : i < 64 := by
      by_contra hnot
      have hi64 : i = 64 := by omega
      subst hi64
      exact hcond (by simp [hx5])
    have hlen64 : ws.length = 64 := by
      change ws.length = 64 at hlen
      exact hlen
    exact copy_blockVCs src dst srcBytes rf ws i hlt hx10 hx11 hlen64 hs hfr
  case secp256k1PointCopy64.post =>
    rintro rf ws A ⟨⟨i, hi, hx10, hx11, hx5, hle, hs, ho, hfr, hws⟩, hncond⟩
    have hi64 : i = 64 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi64
    rw [hws, copyWin64_64_eq srcBytes orig hs ho]
    rfl

end Secp256k1PointCopy64SAsm

end EvmAsm.Codegen
