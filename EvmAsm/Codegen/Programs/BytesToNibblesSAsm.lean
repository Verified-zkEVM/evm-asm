/-
  Verified byte-identical SAsm port of `bytes_to_nibbles`.

  Each source byte is expanded to two output bytes, high nibble first and low
  nibble second.  The source is read-only; the `2 * len` destination window is
  the sole writable region.
-/

import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BytesToNibblesSAsm

def highNibble (b : BitVec 8) : BitVec 8 :=
  BitVec.truncate 8 (b.zeroExtend 64 >>> 4)

def lowNibble (b : BitVec 8) : BitVec 8 :=
  BitVec.truncate 8 (b.zeroExtend 64 &&& signExtend12 (15 : BitVec 12))

def nibblePair (b : BitVec 8) : List (BitVec 8) := [highNibble b, lowNibble b]

def nibblePrefix (srcBytes : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => []
  | i + 1 => nibblePrefix srcBytes i ++ nibblePair (srcBytes.getD i 0)

def bytesToNibblesBytes (srcBytes : List (BitVec 8)) (len : Nat) : List (BitVec 8) :=
  nibblePrefix srcBytes len

def nibbleWin (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  nibblePrefix srcBytes i ++ orig.drop (2 * i)

#guard bytesToNibblesBytes [0xab, 0x04, 0xff] 3 = [10, 11, 0, 4, 15, 15]

theorem length_nibblePair (b : BitVec 8) : (nibblePair b).length = 2 := by rfl

theorem length_nibblePrefix (srcBytes : List (BitVec 8)) (i : Nat) :
    (nibblePrefix srcBytes i).length = 2 * i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [nibblePrefix, List.length_append, length_nibblePair, ih]; omega

theorem nibbleWin_zero (srcBytes orig : List (BitVec 8)) :
    nibbleWin srcBytes orig 0 = orig := by
  simp [nibbleWin, nibblePrefix]

theorem length_nibbleWin (srcBytes orig : List (BitVec 8)) (len i : Nat)
    (h_orig : orig.length = 2 * len) (h_i : i ≤ len) :
    (nibbleWin srcBytes orig i).length = 2 * len := by
  simp only [nibbleWin, List.length_append, length_nibblePrefix, List.length_drop, h_orig]
  omega

theorem nibbleWin_step (srcBytes orig : List (BitVec 8)) (len i : Nat)
    (h_orig : orig.length = 2 * len) (h_i : i < len) :
    setBytes (nibbleWin srcBytes orig i) (2 * i) (nibblePair (srcBytes.getD i 0)) =
      nibbleWin srcBytes orig (i + 1) := by
  unfold nibbleWin
  have hpre : (nibblePrefix srcBytes i).length = 2 * i := length_nibblePrefix _ _
  rw [setBytes_append_right _ _ _ _ (by omega), hpre, Nat.sub_self]
  have hfit : (nibblePair (srcBytes.getD i 0)).length ≤ (orig.drop (2 * i)).length := by
    simp only [length_nibblePair, List.length_drop, h_orig]
    omega
  have hslot := setBytes_slot (orig.drop (2 * i)) (nibblePair (srcBytes.getD i 0)) 0
    (by simpa using hfit)
  rw [List.drop_zero, length_nibblePair] at hslot
  have hdrop :
      (setBytes (orig.drop (2 * i)) 0 (nibblePair (srcBytes.getD i 0))).drop 2 =
        (orig.drop (2 * i)).drop 2 := by
    simpa [length_nibblePair] using
      (setBytes_drop_of_le (nibblePair (srcBytes.getD i 0)) (orig.drop (2 * i)) 0 2
        (by rw [length_nibblePair]))
  have hset : setBytes (orig.drop (2 * i)) 0 (nibblePair (srcBytes.getD i 0)) =
      nibblePair (srcBytes.getD i 0) ++ orig.drop (2 * (i + 1)) := by
    conv_lhs =>
      rw [← List.take_append_drop 2
        (setBytes (orig.drop (2 * i)) 0 (nibblePair (srcBytes.getD i 0)))]
    rw [hslot, hdrop, List.drop_drop]
    congr 2
  rw [hset, nibblePrefix, List.append_assoc]

theorem nibbleWin_len (srcBytes orig : List (BitVec 8)) (len : Nat)
    (h_orig : orig.length = 2 * len) :
    nibbleWin srcBytes orig len = bytesToNibblesBytes srcBytes len := by
  unfold nibbleWin bytesToNibblesBytes
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]

def bytesToNibblesInitBlock : List Instr :=
  [.MV .x5 .x10, .MV .x6 .x12, .MV .x7 .x11, .LI .x31 0]

def bytesToNibblesStepBlock : List Instr :=
  [.LBU .x28 .x5 0,
   .SRLI .x29 .x28 4,
   .ANDI .x30 .x28 15,
   .SB .x6 .x29 0,
   .SB .x6 .x30 1,
   .ADDI .x5 .x5 1,
   .ADDI .x6 .x6 2,
   .ADDI .x7 .x7 (-1 : BitVec 12),
   .ADDI .x31 .x31 2]

def bytesToNibblesInv (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = src + BitVec.ofNat 64 i ∧
    rf.get .x6 = dst + BitVec.ofNat 64 (2 * i) ∧
    rf.get .x7 = BitVec.ofNat 64 (len - i) ∧
    rf.get .x31 = BitVec.ofNat 64 (2 * i) ∧
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧ rf.get .x12 = dst ∧
    i ≤ len ∧ len ≤ srcBytes.length ∧ orig.length = 2 * len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + 2 * len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + 2 * len ≤ src.toNat) ∧
    ws = nibbleWin srcBytes orig i ∧ A = empAssertion

def bytesToNibblesBody (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" bytesToNibblesInitBlock ;;;
  .«while» "loop" (.bne .x7 .x0) len
    (bytesToNibblesInv src dst len srcBytes orig)
    (.block "step" bytesToNibblesStepBlock) ;;;
  .block "done" [.MV .x10 .x31]

def bytesToNibblesFn (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bytesToNibbles"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 2 * len⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧ rf.get .x12 = dst ∧
    ws = orig ∧ len ≤ srcBytes.length ∧ orig.length = 2 * len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + 2 * len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + 2 * len ≤ src.toNat) ∧
    A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = BitVec.ofNat 64 (2 * len) ∧
    ws = bytesToNibblesBytes srcBytes len ∧ A = empAssertion
  body := bytesToNibblesBody src dst len srcBytes orig

#guard (bytesToNibblesBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] =
  bytesToNibbles_prog

/-- An `LBU` that misses the writable destination reads the source region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs) =
      (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

def stepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x28 (b.zeroExtend 64)
  let r2 := r1.set .x29 (r1.get .x28 >>> 4)
  let r3 := r2.set .x30 (r2.get .x28 &&& signExtend12 (15 : BitVec 12))
  let r4 := r3.set .x5 (r3.get .x5 + signExtend12 (1 : BitVec 12))
  let r5 := r4.set .x6 (r4.get .x6 + signExtend12 (2 : BitVec 12))
  let r6 := r5.set .x7 (r5.get .x7 + signExtend12 (-1 : BitVec 12))
  r6.set .x31 (r6.get .x31 + signExtend12 (2 : BitVec 12))

private theorem setBytes_pair (ws : List (BitVec 8)) (k : Nat) (a b : BitVec 8) :
    setBytes (setBytes ws k [a]) (k + 1) [b] = setBytes ws k [a, b] := by
  rfl

theorem stepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold stepRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem stepRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x6 = rf.get .x6 + signExtend12 (2 : BitVec 12) := by
  unfold stepRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem stepRf_get_x7 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold stepRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem stepRf_get_x31 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x31 = rf.get .x31 + signExtend12 (2 : BitVec 12) := by
  unfold stepRf
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem stepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x10 = rf.get .x10 := by
  unfold stepRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem stepRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x11 = rf.get .x11 := by
  unfold stepRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem stepRf_get_x12 (rf : RegFile) (b : BitVec 8) :
    (stepRf rf b).get .x12 = rf.get .x12 := by
  unfold stepRf
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem step_engine (src dst : Word) (len i : Nat) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = src + BitVec.ofNat 64 i)
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (2 * i))
    (h_i : i < len) (h_src : src.toNat + len < 2 ^ 64)
    (h_dst : dst.toNat + 2 * len < 2 ^ 64)
    (h_disj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + 2 * len ≤ src.toNat)
    (h_ws : ws.length = 2 * len) :
    execBlock ⟨src, srcBytes⟩ dst rf ws bytesToNibblesStepBlock =
      (stepRf rf (srcBytes.getD i 0),
        setBytes ws (2 * i) (nibblePair (srcBytes.getD i 0))) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hiNat : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat]
    omega
  have hloadAddr : rf.get .x5 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 i := by rw [hx5, hse0]; simp
  have hmiss : ¬ inRw dst ws (rf.get .x5 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadAddr]
    unfold inRw
    rw [h_ws]
    have hsub : (src + BitVec.ofNat 64 i - dst).toNat =
        (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hiNat]
      congr 1
      omega
    rw [hsub]
    rcases h_disj with hd | hd <;> omega
  have hbyte : (Region.byteAt ⟨src, srcBytes⟩
      (rf.get .x5 + signExtend12 (0 : BitVec 12))) = srcBytes.getD i 0 := by
    rw [hloadAddr]
    show srcBytes.getD ((src + BitVec.ofNat 64 i - src).toNat) 0 = _
    rw [show (src + BitVec.ofNat 64 i - src).toNat = i by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hiNat]
      omega]
  have hstore0 : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = 2 * i := by
    rw [hx6, hse0]
    bv_omega
  have hstore1 : (rf.get .x6 + signExtend12 (1 : BitVec 12) - dst).toNat = 2 * i + 1 := by
    rw [hx6, hse1]
    bv_omega
  rw [show bytesToNibblesStepBlock =
      [.LBU .x28 .x5 0, .SRLI .x29 .x28 4, .ANDI .x30 .x28 15,
       .SB .x6 .x29 0, .SB .x6 .x30 1, .ADDI .x5 .x5 1, .ADDI .x6 .x6 2,
       .ADDI .x7 .x7 (-1 : BitVec 12), .ADDI .x31 .x31 2] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss, hbyte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (2 * i) (by
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hstore0)]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ (2 * i + 1) (by
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hstore1)]
  repeat' first | rw [execBlock_cons] | dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold stepRf nibblePair highNibble lowNibble
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, show (4 : BitVec 6).toNat = 4 by decide]
  rw [setBytes_pair]

theorem bytesToNibblesFn_spec (src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8))
    (h_src_wf : (Region.mk src srcBytes).wf)
    (h_dst_wf : RwRegion.wf ⟨dst, 2 * len⟩) (base : Word) :
    (bytesToNibblesFn src dst len srcBytes orig).Spec base := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hse1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse2 : signExtend12 (2 : BitVec 12) = (2 : Word) := by decide
  have hsem1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  vcgen
  case region => exact ⟨h_src_wf, h_dst_wf⟩
  case bytesToNibbles.loop.inv_init =>
    rintro rf ws A ⟨rf0, ws0, -,
      ⟨hx10, hx11, hx12, rfl, hlenSrc, hlenOrig, hsrc, hdst, hdisj, hA⟩,
      rfl, rfl⟩
    simp only [bytesToNibblesInitBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenSrc, hlenOrig,
      hsrc, hdst, hdisj, nibbleWin_zero srcBytes ws, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide), hx10]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
    · rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x31),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
  case bytesToNibbles.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx7, -, -, -, -, -, -, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not, hx7]
    rw [show len - len = 0 by omega]
    rfl
  case bytesToNibbles.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf0, ws0, -,
      ⟨⟨hx5, hx6, hx7, hx31, hx10, hx11, hx12, hile, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hwin, hA⟩, -⟩, rfl, rfl⟩
    have hwslen : ws0.length = 2 * len := by
      rw [hwin]
      exact length_nibbleWin srcBytes orig len i hlenOrig (by omega)
    simp only [show (bytesToNibblesFn src dst len srcBytes orig).rw.base = dst from rfl,
      show (bytesToNibblesFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl]
    rw [step_engine src dst len i srcBytes rf0 ws0 hx5 hx6 hi hsrc hdst hdisj hwslen]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hlenSrc, hlenOrig,
      hsrc, hdst, hdisj, ?_, hA⟩
    · rw [stepRf_get_x5, hx5, hse1]
      bv_omega
    · rw [stepRf_get_x6, hx6, hse2]
      bv_omega
    · rw [stepRf_get_x7, hx7, hsem1]
      bv_omega
    · rw [stepRf_get_x31, hx31, hse2]
      bv_omega
    · rw [stepRf_get_x10, hx10]
    · rw [stepRf_get_x11, hx11]
    · rw [stepRf_get_x12, hx12]
    · rw [hwin, nibbleWin_step srcBytes orig len i hlenOrig hi]
  case bytesToNibbles.loop.body.step.mem =>
    rintro rf ws A hwslen ⟨i, hi,
      ⟨hx5, hx6, hx7, hx31, hx10, hx11, hx12, hile, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hwin, hA⟩, -⟩
    change ws.length = 2 * len at hwslen
    have hiNat : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      omega
    have hloadAddr : rf.get .x5 + signExtend12 (0 : BitVec 12) =
        src + BitVec.ofNat 64 i := by rw [hx5, hse0]; simp
    have hmiss : ¬ inRw dst ws (rf.get .x5 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hloadAddr]
      unfold inRw
      rw [hwslen]
      have hsub : (src + BitVec.ofNat 64 i - dst).toNat =
          (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hiNat]
        congr 1
        omega
      rw [hsub]
      rcases hdisj with hd | hd <;> omega
    have hloadIndex : (src + BitVec.ofNat 64 i - src).toNat = i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hiNat]
      omega
    have hstore0 : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = 2 * i := by
      rw [hx6, hse0]
      bv_omega
    have hstore1 : (rf.get .x6 + signExtend12 (1 : BitVec 12) - dst).toNat = 2 * i + 1 := by
      rw [hx6, hse1]
      bv_omega
    rw [show (bytesToNibblesFn src dst len srcBytes orig).region = ⟨src, srcBytes⟩ from rfl,
      show (bytesToNibblesFn src dst len srcBytes orig).rw.base = dst from rfl,
      show bytesToNibblesStepBlock =
        [.LBU .x28 .x5 0, .SRLI .x29 .x28 4, .ANDI .x30 .x28 15,
         .SB .x6 .x29 0, .SB .x6 .x30 1, .ADDI .x5 .x5 1, .ADDI .x6 .x6 2,
         .ADDI .x7 .x7 (-1 : BitVec 12), .ADDI .x31 .x31 2] from rfl]
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hmiss]
      unfold Region.loadOk
      rw [hloadAddr, hloadIndex]
      refine ⟨Nat.one_dvd _, ?_⟩
      change i + 1 ≤ srcBytes.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hmiss]
      simp only [blockVCs, execInstrRF, aluSem, storeSem, loadSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      refine ⟨trivial, trivial, ?_, ?_, trivial, trivial, trivial, trivial, trivial⟩
      · refine ⟨?_, Nat.one_dvd _⟩
        unfold inRw
        rw [hwslen, hstore0]
        omega
      · refine ⟨?_, Nat.one_dvd _⟩
        unfold inRw
        rw [length_setBytes, hwslen, hstore1]
        omega
  case bytesToNibbles.post =>
    rintro rf ws A ⟨rf0, ws0, -, ⟨⟨i, hile,
      ⟨hx5, hx6, hx7, hx31, hx10, hx11, hx12, hi_le, hlenSrc, hlenOrig,
        hsrc, hdst, hdisj, hwin, hA⟩⟩, hncond⟩, rfl, rfl⟩
    have hi_len : i = len := by
      simp only [Cond.holds, not_not, RegFile.get_x0] at hncond
      rw [hx7] at hncond
      have hto := congrArg BitVec.toNat hncond
      rw [BitVec.toNat_ofNat] at hto
      change (len - i) % 2 ^ 64 = 0 at hto
      omega
    subst hi_len
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, hA⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx31]
    · rw [hwin, nibbleWin_len srcBytes orig i hlenOrig]

#print axioms bytesToNibblesFn_spec

end BytesToNibblesSAsm

end EvmAsm.Codegen
