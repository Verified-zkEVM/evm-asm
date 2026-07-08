/-
  EvmAsm.Codegen.Programs.RunningBloomCopySAsm

  Verified SAsm port for `running_bloom_copy`.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bloom

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace RunningBloomCopySAsm

def frameOk256 (src dst : Word) : Prop :=
  src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)

/-- The 256-byte destination window after copying the first `i` dwords. -/
def copyWin256 (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take (8 * i) ++ orig.drop (8 * i)

theorem copyWin256_zero (srcBytes orig : List (BitVec 8)) :
    copyWin256 srcBytes orig 0 = orig := by
  simp [copyWin256]

theorem copyWin256_32_eq (srcBytes orig : List (BitVec 8))
    (hs : srcBytes.length = 256) (ho : orig.length = 256) :
    copyWin256 srcBytes orig 32 = srcBytes := by
  simp only [copyWin256, Nat.reduceMul]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem length_copyWin256 (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 256) (ho : orig.length = 256) (hi : i ≤ 32) :
    (copyWin256 srcBytes orig i).length = 256 := by
  simp only [copyWin256, List.length_append, List.length_take, List.length_drop, hs, ho]
  omega

theorem copyWin256_step (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 256) (ho : orig.length = 256) (hi : i < 32) :
    setBytes (copyWin256 srcBytes orig i) (8 * i)
      (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8))) =
    copyWin256 srcBytes orig (i + 1) := by
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
  rw [copyWin256]
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
  simp only [copyWin256]
  rw [← List.append_assoc]
  congr 1
  rw [show srcBytes.take (8 * i) ++ (srcBytes.drop (8 * i)).take 8 =
      srcBytes.take (8 * (i + 1)) from by
    rw [← List.take_add]
    congr 1]

def copyStepBlock : List Instr :=
  [.LD .x28 .x7 (0 : BitVec 12),
   .SD .x6 .x28 (0 : BitVec 12),
   .ADDI .x6 .x6 (8 : BitVec 12),
   .ADDI .x7 .x7 (8 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

def copyStepRf (rf : RegFile) (v : Word) : RegFile :=
  let r1 := rf.set .x28 v
  let r2 := r1.set .x6 (r1.get .x6 + signExtend12 (8 : BitVec 12))
  let r3 := r2.set .x7 (r2.get .x7 + signExtend12 (8 : BitVec 12))
  r3.set .x5 (r3.get .x5 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x6 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x6 = rf.get .x6 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x7 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x7 = rf.get .x7 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x5 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x5 = rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
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
    (hk : k < 32) (hws : ws.length = 256) (hfr : frameOk256 src dst) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

private theorem src_dwordAt (src : Word) (srcBytes : List (BitVec 8)) (k : Nat)
    (hk : k < 32) :
    Region.dwordAt ⟨src, srcBytes⟩ (src + BitVec.ofNat 64 (8 * k)) =
      packBytes ((srcBytes.drop (8 * k)).take 8) := by
  unfold Region.dwordAt
  have hk64 : 8 * k < 2 ^ 64 := by omega
  rw [show (src + BitVec.ofNat 64 (8 * k) - src).toNat = 8 * k by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]

private theorem copy_engine (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx7 : rf.get .x7 = src + BitVec.ofNat 64 (8 * i))
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 256) (hfr : frameOk256 src dst) :
    execBlock ⟨src, srcBytes⟩ dst rf ws copyStepBlock =
      (copyStepRf rf (packBytes ((srcBytes.drop (8 * i)).take 8)),
       setBytes ws (8 * i) (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)))) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x7 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by
    rw [hx7, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 :=
    src_miss8 src dst ws i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x7 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x28 (packBytes ((srcBytes.drop (8 * i)).take 8))).get .x6
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hx6, hse0]
    bv_omega
  rw [show copyStepBlock = [.LD .x28 .x7 0, .SD .x6 .x28 0,
      .ADDI .x6 .x6 8, .ADDI .x7 .x7 8, .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, ld_romiss _ _ _ _ .x28 .x7 (0 : BitVec 12) hmissExact,
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
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]

private theorem copy_blockVCs (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (hx7 : rf.get .x7 = src + BitVec.ofNat 64 (8 * i))
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 256) (hs : srcBytes.length = 256) (hfr : frameOk256 src dst) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws copyStepBlock := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x7 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by
    rw [hx7, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 :=
    src_miss8 src dst ws i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x7 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x28 (Region.dwordAt ⟨src, srcBytes⟩
        (rf.get .x7 + signExtend12 (0 : BitVec 12)))).get .x6
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hx6, hse0]
    bv_omega
  have hsrcOff : (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [show copyStepBlock = [.LD .x28 .x7 0, .SD .x6 .x28 0,
      .ADDI .x6 .x6 8, .ADDI .x7 .x7 8, .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
  refine ⟨?_, ?_⟩
  · show (if inRw dst ws (rf.get .x7 + signExtend12 0) 8 then _ else Region.loadOk _ _ _)
    rw [if_neg hmissExact]
    rw [hloadAddr]
    unfold Region.loadOk
    constructor
    · rw [hsrcOff]
      exact Nat.dvd_mul_right 8 i
    · change (src + BitVec.ofNat 64 (8 * i) - src).toNat + 8 ≤ srcBytes.length
      rw [hsrcOff, hs]
      omega
  · rw [ld_romiss _ _ _ _ .x28 .x7 (0 : BitVec 12) hmissExact]
    simp only [blockVCs, loadSem, storeSem]
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [hstoreAddr, hws]
      omega
    · exact ⟨trivial, trivial, trivial, trivial⟩

def copyInv (src dst : Word) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x7 = src + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x6 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    i ≤ 32 ∧ srcBytes.length = 256 ∧ orig.length = 256 ∧ frameOk256 src dst ∧
    ws = copyWin256 srcBytes orig i

def runningBloomCopyBody (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (32 : Word), .MV .x6 .x10, .MV .x7 .x11] ;;;
  .while "loop" (.bne .x5 .x0) 32 (copyInv src dst srcBytes orig)
    (.block "copy" copyStepBlock) ;;;
  .block "done" [.LI .x10 (0 : Word)]

def runningBloomCopyFn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "runningBloomCopy"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 256⟩
  pre := fun rf ws _ =>
    rf.get .x10 = dst ∧ rf.get .x11 = src ∧ ws = orig ∧
    srcBytes.length = 256 ∧ orig.length = 256 ∧ frameOk256 src dst
  post := fun rf ws _ => rf.get .x10 = 0 ∧ ws = srcBytes
  body := runningBloomCopyBody src dst srcBytes orig

def runningBloomCopy_verified : Program :=
  (runningBloomCopyBody 0 0 [] []).flatten 0

#guard (runningBloomCopy_verified : List Instr).length = 11
#guard (runningBloomCopyBody 0 0 [] []).flatten 0 =
  (runningBloomCopyBody 0 0 [] []).flatten 0x80000000
#guard (runningBloomCopyBody 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] =
  runningBloomCopy_prog

theorem runningBloomCopyFn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 256⟩) (base : Word) :
    (runningBloomCopyFn src dst srcBytes orig).Spec base := by
  have hbase : (runningBloomCopyFn src dst srcBytes orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case runningBloomCopy.loop.inv_init =>
    rintro rf' ws' A' ⟨rf₀, ws₀, -, ⟨hx10, hx11, hws0, hs, ho, hfr⟩, rfl, rfl⟩
    simp only [hbase]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx11]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true, hx10]
      bv_omega
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rfl
    · exact hws0.trans (copyWin256_zero srcBytes orig).symm
  case runningBloomCopy.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx7, hx6, hx5, hle, hs, ho, hfr, hws₀⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase, show (runningBloomCopyFn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl]
    have hlt : i < 32 := by
      by_contra hnot
      have hi32 : i = 32 := by omega
      subst hi32
      exact hcond (by simp [hx5])
    have hwsLen : ws₀.length = 256 := by
      rw [hws₀]
      exact length_copyWin256 srcBytes orig i hs ho hle
    rw [copy_engine src dst srcBytes rf₀ ws₀ i hlt hx7 hx6 hwsLen hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_⟩
    · rw [copyStepRf_get_x7, hx7, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [copyStepRf_get_x6, hx6, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [copyStepRf_get_x5, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, copyWin256_step srcBytes orig i hs ho hlt]
  case runningBloomCopy.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx5, -, -, -, -, -⟩
    simp [Cond.holds, hx5]
  case runningBloomCopy.loop.body.copy.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx7, hx6, hx5, hle, hs, ho, hfr, hws⟩, hcond⟩
    have hlt : i < 32 := by
      by_contra hnot
      have hi32 : i = 32 := by omega
      subst hi32
      exact hcond (by simp [hx5])
    have hlen256 : ws.length = 256 := by
      change ws.length = 256 at hlen
      exact hlen
    exact copy_blockVCs src dst srcBytes rf ws i hlt hx7 hx6 hlen256 hs hfr
  case runningBloomCopy.post =>
    rintro rf ws A ⟨rf₀, ws₀, -, ⟨⟨i, hi, hx7, hx6, hx5, hle, hs, ho, hfr, hws⟩, hncond⟩, rfl, rfl⟩
    have hi32 : i = 32 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi32
    refine ⟨?_, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [hws, copyWin256_32_eq srcBytes orig hs ho]

end RunningBloomCopySAsm

end EvmAsm.Codegen
