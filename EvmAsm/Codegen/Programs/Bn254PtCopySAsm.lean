/-
  EvmAsm.Codegen.Programs.Bn254PtCopySAsm

  Verified SAsm port of `bnq_pt_copy`: copy the 1152-byte BN254 FQ12 projective point from
  `a0` to the writable destination at `a1`.  The emitted routine is a
  bottom-test dword loop over 144 limbs.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Pairing

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254PtCopySAsm

def frameOk1152 (src dst : Word) : Prop :=
  src.toNat + 1152 < 2 ^ 64 ∧ dst.toNat + 1152 < 2 ^ 64 ∧
    (src.toNat + 1152 ≤ dst.toNat ∨ dst.toNat + 1152 ≤ src.toNat)

def copyWin1152 (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take (8 * i) ++ orig.drop (8 * i)

theorem copyWin1152_zero (srcBytes orig : List (BitVec 8)) :
    copyWin1152 srcBytes orig 0 = orig := by
  simp [copyWin1152]

theorem copyWin1152_144_eq (srcBytes orig : List (BitVec 8))
    (hs : srcBytes.length = 1152) (ho : orig.length = 1152) :
    copyWin1152 srcBytes orig 144 = srcBytes := by
  simp only [copyWin1152, Nat.reduceMul]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem length_copyWin1152 (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 1152) (ho : orig.length = 1152) (hi : i ≤ 144) :
    (copyWin1152 srcBytes orig i).length = 1152 := by
  simp only [copyWin1152, List.length_append, List.length_take, List.length_drop, hs, ho]
  omega

theorem copyWin1152_step (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 1152) (ho : orig.length = 1152) (hi : i < 144) :
    setBytes (copyWin1152 srcBytes orig i) (8 * i)
      (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8))) =
    copyWin1152 srcBytes orig (i + 1) := by
  have htake : (srcBytes.take (8 * i)).length = 8 * i := by
    simp only [List.length_take, hs]
    omega
  have hseglen : ((srcBytes.drop (8 * i)).take 8).length = 8 := by
    simp only [List.length_take, List.length_drop, hs]
    omega
  have hpayload : dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)) =
      (srcBytes.drop (8 * i)).take 8 := by
    exact dwordBytes_packBytes _ hseglen
  rw [hpayload]
  rw [copyWin1152]
  rw [setBytes_append_right _ _ _ _ (by rw [htake])]
  rw [htake, Nat.sub_self]
  have hfit : 0 + ((srcBytes.drop (8 * i)).take 8).length ≤ (orig.drop (8 * i)).length := by
    rw [hseglen]
    simp only [List.length_drop, ho]
    omega
  have hslot := setBytes_slot (orig.drop (8 * i)) ((srcBytes.drop (8 * i)).take 8) 0 hfit
  rw [List.drop_zero, hseglen] at hslot
  have hdrop : (setBytes (orig.drop (8 * i)) 0 ((srcBytes.drop (8 * i)).take 8)).drop 8
      = (orig.drop (8 * i)).drop 8 := by
    simpa [hseglen] using
      (setBytes_drop_of_le ((srcBytes.drop (8 * i)).take 8) (orig.drop (8 * i)) 0 8 (by
        rw [hseglen]))
  have hset : setBytes (orig.drop (8 * i)) 0 ((srcBytes.drop (8 * i)).take 8)
      = (srcBytes.drop (8 * i)).take 8 ++ (orig.drop (8 * i)).drop 8 := by
    conv_lhs =>
      rw [← List.take_append_drop 8
        (setBytes (orig.drop (8 * i)) 0 ((srcBytes.drop (8 * i)).take 8))]
    rw [hslot, hdrop]
  rw [hset]
  rw [show (orig.drop (8 * i)).drop 8 = orig.drop (8 * (i + 1)) from by
    rw [List.drop_drop]
    congr 1]
  simp only [copyWin1152]
  rw [← List.append_assoc]
  congr 1
  rw [show srcBytes.take (8 * i) ++ (srcBytes.drop (8 * i)).take 8 =
      srcBytes.take (8 * (i + 1)) from by
    rw [← List.take_add]
    congr 1]

def copyStepBlock : List Instr :=
  [.LD .x28 .x10 (0 : BitVec 12),
   .SD .x11 .x28 (0 : BitVec 12),
   .ADDI .x10 .x10 (8 : BitVec 12),
   .ADDI .x11 .x11 (8 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def copyStepRf (rf : RegFile) (v : Word) : RegFile :=
  let r1 := rf.set .x28 v
  let r2 := r1.set .x10 (r1.get .x10 + signExtend12 (8 : BitVec 12))
  let r3 := r2.set .x11 (r2.get .x11 + signExtend12 (8 : BitVec 12))
  r3.set .x7 (r3.get .x7 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x10 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x10 = rf.get .x10 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x11 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x11 = rf.get .x11 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x7 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem ld_romiss (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwb ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF reg rwb rf ws (.LD rd rs1 ofs)
      = (rf.set rd (reg.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

private theorem src_miss8 (src dst : Word) (ws : List (BitVec 8)) (k : Nat)
    (hk : k < 144) (hws : ws.length = 1152) (hfr : frameOk1152 src dst) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

private theorem src_dwordAt (src : Word) (srcBytes : List (BitVec 8)) (k : Nat)
    (hk : k < 144) :
    Region.dwordAt ⟨src, srcBytes⟩ (src + BitVec.ofNat 64 (8 * k)) =
      packBytes ((srcBytes.drop (8 * k)).take 8) := by
  unfold Region.dwordAt
  have hk64 : 8 * k < 2 ^ 64 := by omega
  rw [show (src + BitVec.ofNat 64 (8 * k) - src).toNat = 8 * k by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]

private theorem copy_engine (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 144)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (8 * i))
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 1152) (hfr : frameOk1152 src dst) :
    execBlock ⟨src, srcBytes⟩ dst rf ws copyStepBlock =
      (copyStepRf rf (packBytes ((srcBytes.drop (8 * i)).take 8)),
       setBytes ws (8 * i) (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)))) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x10 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by
    rw [hx10, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 :=
    src_miss8 src dst ws i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x28 (packBytes ((srcBytes.drop (8 * i)).take 8))).get .x11
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28), hx11, hse0]
    bv_omega
  rw [show copyStepBlock = [.LD .x28 .x10 0, .SD .x11 .x28 0,
      .ADDI .x10 .x10 8, .ADDI .x11 .x11 8, .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, ld_romiss _ _ _ _ .x28 .x10 (0 : BitVec 12) hmissExact,
    hloadAddr, src_dwordAt src srcBytes i hi]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ (8 * i) hstoreAddr]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x28 ≠ .x0)]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold copyStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]

private theorem copy_blockVCs (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 144)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (8 * i))
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 1152) (hs : srcBytes.length = 1152) (hfr : frameOk1152 src dst) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws copyStepBlock := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x10 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by
    rw [hx10, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 :=
    src_miss8 src dst ws i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x28 (Region.dwordAt ⟨src, srcBytes⟩
        (rf.get .x10 + signExtend12 (0 : BitVec 12)))).get .x11
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28), hx11, hse0]
    bv_omega
  have hsrcOff : (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [show copyStepBlock = [.LD .x28 .x10 0, .SD .x11 .x28 0,
      .ADDI .x10 .x10 8, .ADDI .x11 .x11 8, .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl]
  refine ⟨?_, ?_⟩
  · show (if inRw dst ws (rf.get .x10 + signExtend12 0) 8 then _ else Region.loadOk _ _ _)
    rw [if_neg hmissExact]
    rw [hloadAddr]
    unfold Region.loadOk
    constructor
    · rw [hsrcOff]
      exact Nat.dvd_mul_right 8 i
    · change (src + BitVec.ofNat 64 (8 * i) - src).toNat + 8 ≤ srcBytes.length
      rw [hsrcOff, hs]
      omega
  · rw [ld_romiss _ _ _ _ .x28 .x10 (0 : BitVec 12) hmissExact]
    simp only [blockVCs, loadSem, storeSem]
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [hstoreAddr, hws]
      omega
    · exact ⟨trivial, trivial, trivial, trivial⟩

def copyInv (src dst : Word) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x10 = src + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x11 = dst + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x7 = BitVec.ofNat 64 (144 - (i + 1)) ∧
    i < 144 ∧ srcBytes.length = 1152 ∧ orig.length = 1152 ∧ frameOk1152 src dst ∧
    ws = copyWin1152 srcBytes orig (i + 1)

def bnqPtCopyBody (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x7 (144 : Word)] ;;;
  .doWhile "loop" (.bne .x7 .x0) 143 (copyInv src dst srcBytes orig)
    (.block "copy" copyStepBlock)

def bnqPtCopyFn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bnqPtCopy"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 1152⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧
    srcBytes.length = 1152 ∧ orig.length = 1152 ∧ frameOk1152 src dst
  post := fun _ ws _ => ws = srcBytes
  body := bnqPtCopyBody src dst srcBytes orig

def bnqPtCopy_verified : Program :=
  (bnqPtCopyBody 0 0 [] []).flatten 0

#guard (bnqPtCopy_verified : List Instr).length = 7
#guard (bnqPtCopyBody 0 0 [] []).flatten 0 = (bnqPtCopyBody 0 0 [] []).flatten 0x80000000
#guard (bnqPtCopyBody 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = bnqPtCopy_prog

theorem bnqPtCopyFn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 1152⟩) (base : Word) :
    (bnqPtCopyFn src dst srcBytes orig).Spec base := by
  have hbase : (bnqPtCopyFn src dst srcBytes orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case bnqPtCopy.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, hx11, rfl, hs, ho, hfr⟩
    dsimp only [bnqPtCopyFn] at hbase ⊢
    have hx10Init : (execBlock ⟨src, srcBytes⟩ dst rfInit ws0
        [Instr.LI Reg.x7 144]).1.get .x10 = src := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    have hx11Init : (execBlock ⟨src, srcBytes⟩ dst rfInit ws0
        [Instr.LI Reg.x7 144]).1.get .x11 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx11]
    have hx7Init : (execBlock ⟨src, srcBytes⟩ dst rfInit ws0
        [Instr.LI Reg.x7 144]).1.get .x7 = (144 : Word) := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    rw [copy_engine src dst srcBytes _ ws0 0 (by omega) (by simpa using hx10Init)
      (by simpa using hx11Init) ho hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_⟩
    · rw [copyStepRf_get_x10, hx10Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x11, hx11Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x7, hx7Init, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      decide
    · change setBytes ws0 (8 * 0)
        (dwordBytes (packBytes ((srcBytes.drop (8 * 0)).take 8))) =
        copyWin1152 srcBytes ws0 (0 + 1)
      simpa [copyWin1152_zero srcBytes ws0] using
        copyWin1152_step srcBytes ws0 0 hs ho (by omega)
  case bnqPtCopy.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx11, hx7, hlt, hs, ho, hfr, hws₀⟩, hcond⟩, rfl, rfl⟩
    dsimp only [bnqPtCopyFn] at hbase ⊢
    have hwsLen : ws₀.length = 1152 := by
      rw [hws₀]
      exact length_copyWin1152 srcBytes orig (i + 1) hs ho (by omega)
    rw [copy_engine src dst srcBytes rf₀ ws₀ (i + 1) (by omega) hx10 hx11 hwsLen hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_⟩
    · rw [copyStepRf_get_x10, hx10, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [copyStepRf_get_x11, hx11, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [copyStepRf_get_x7, hx7, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, copyWin1152_step srcBytes orig (i + 1) hs ho (by omega)]
  case bnqPtCopy.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx7, -, -, -, -, -⟩
    simp only [Cond.holds, hx7, not_not, RegFile.get_x0]
    decide
  case bnqPtCopy.loop.body.copy.mem =>
    rintro rf ws A hlen (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, -, ⟨hx10, hx11, rfl, hs, ho, hfr⟩, rfl, rfl⟩
      have hlen1152 : ws.length = 1152 := by
        change ws.length = 1152 at hlen
        exact hlen
      exact copy_blockVCs src dst srcBytes _ ws 0 (by omega)
        (by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
            ne_eq, reduceCtorEq, not_false_eq_true, hx10]
          bv_omega)
        (by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
            ne_eq, reduceCtorEq, not_false_eq_true, hx11]
          bv_omega) hlen1152 hs hfr
    · rcases hloop with ⟨i, hi, ⟨hx10, hx11, hx7, hlt, hs, ho, hfr, hws⟩, hcond⟩
      have hlen1152 : ws.length = 1152 := by
        change ws.length = 1152 at hlen
        exact hlen
      exact copy_blockVCs src dst srcBytes rf ws (i + 1) (by omega) hx10 hx11 hlen1152 hs hfr
  case bnqPtCopy.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx11, hx7, hlt, hs, ho, hfr, hws⟩, hncond⟩
    have hi143 : i = 143 := by
      simp only [Cond.holds, hx7, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi143
    rw [hws, copyWin1152_144_eq srcBytes orig hs ho]
    rfl


end Bn254PtCopySAsm

end EvmAsm.Codegen
