/-
  EvmAsm.Codegen.Programs.Bn254Fq12CopySAsm

  Verified SAsm port of `bnq_copy`: copy the 384-byte BN254 FQ12 buffer from
  `a0` to the writable destination at `a1`.  The emitted routine is a
  bottom-test dword loop over 48 limbs.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Fq12
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254Fq12CopySAsm

def frameOk384 (src dst : Word) : Prop :=
  src.toNat + 384 < 2 ^ 64 ∧ dst.toNat + 384 < 2 ^ 64 ∧
    (src.toNat + 384 ≤ dst.toNat ∨ dst.toNat + 384 ≤ src.toNat)

def copyWin384 (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take (8 * i) ++ orig.drop (8 * i)

theorem copyWin384_zero (srcBytes orig : List (BitVec 8)) :
    copyWin384 srcBytes orig 0 = orig := by
  simp [copyWin384]

theorem copyWin384_48_eq (srcBytes orig : List (BitVec 8))
    (hs : srcBytes.length = 384) (ho : orig.length = 384) :
    copyWin384 srcBytes orig 48 = srcBytes := by
  simp only [copyWin384, Nat.reduceMul]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem length_copyWin384 (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 384) (ho : orig.length = 384) (hi : i ≤ 48) :
    (copyWin384 srcBytes orig i).length = 384 := by
  simp only [copyWin384, List.length_append, List.length_take, List.length_drop, hs, ho]
  omega

theorem copyWin384_step (srcBytes orig : List (BitVec 8)) (i : Nat)
    (hs : srcBytes.length = 384) (ho : orig.length = 384) (hi : i < 48) :
    setBytes (copyWin384 srcBytes orig i) (8 * i)
      (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8))) =
    copyWin384 srcBytes orig (i + 1) := by
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
  rw [copyWin384]
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
  simp only [copyWin384]
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
    (hk : k < 48) (hws : ws.length = 384) (hfr : frameOk384 src dst) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

private theorem src_dwordAt (src : Word) (srcBytes : List (BitVec 8)) (k : Nat)
    (hk : k < 48) :
    Region.dwordAt ⟨src, srcBytes⟩ (src + BitVec.ofNat 64 (8 * k)) =
      packBytes ((srcBytes.drop (8 * k)).take 8) := by
  unfold Region.dwordAt
  have hk64 : 8 * k < 2 ^ 64 := by omega
  rw [show (src + BitVec.ofNat 64 (8 * k) - src).toNat = 8 * k by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]

private theorem copy_engine (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 48)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (8 * i))
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 384) (hfr : frameOk384 src dst) :
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
    (rf : RegFile) (ws : List (BitVec 8)) (i : Nat) (hi : i < 48)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (8 * i))
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 384) (hs : srcBytes.length = 384) (hfr : frameOk384 src dst) :
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
  fun i rf ws A =>
    rf.get .x10 = src + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x11 = dst + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x7 = BitVec.ofNat 64 (48 - (i + 1)) ∧
    i < 48 ∧ srcBytes.length = 384 ∧ orig.length = 384 ∧ frameOk384 src dst ∧
    ws = copyWin384 srcBytes orig (i + 1) ∧ A = empAssertion

def bnqCopyBody (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x7 (48 : Word)] ;;;
  .doWhile "loop" (.bne .x7 .x0) 47 (copyInv src dst srcBytes orig)
    (.block "copy" copyStepBlock)

def bnqCopyFn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bnqCopy"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 384⟩
  -- ⚠️ Ambient PINNED: both flat adapters need the post to DETERMINE it (#12244).
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧
    srcBytes.length = 384 ∧ orig.length = 384 ∧ frameOk384 src dst ∧ A = empAssertion
  post := fun _ ws A => ws = srcBytes ∧ A = empAssertion
  body := bnqCopyBody src dst srcBytes orig

def bnqCopy_verified : Program :=
  (bnqCopyBody 0 0 [] []).flatten 0

#guard (bnqCopy_verified : List Instr).length = 7
#guard (bnqCopyBody 0 0 [] []).flatten 0 = (bnqCopyBody 0 0 [] []).flatten 0x80000000
#guard (bnqCopyBody 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = bnqCopy_prog

theorem bnqCopyFn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 384⟩) (base : Word) :
    (bnqCopyFn src dst srcBytes orig).Spec base := by
  have hbase : (bnqCopyFn src dst srcBytes orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case bnqCopy.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, hx11, rfl, hs, ho, hfr, hA⟩
    dsimp only [bnqCopyFn] at hbase ⊢
    have hx10Init : (execBlock ⟨src, srcBytes⟩ dst rfInit ws0
        [Instr.LI Reg.x7 48]).1.get .x10 = src := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    have hx11Init : (execBlock ⟨src, srcBytes⟩ dst rfInit ws0
        [Instr.LI Reg.x7 48]).1.get .x11 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx11]
    have hx7Init : (execBlock ⟨src, srcBytes⟩ dst rfInit ws0
        [Instr.LI Reg.x7 48]).1.get .x7 = (48 : Word) := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
    rw [copy_engine src dst srcBytes _ ws0 0 (by omega) (by simpa using hx10Init)
      (by simpa using hx11Init) ho hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_, hA⟩
    · rw [copyStepRf_get_x10, hx10Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x11, hx11Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [copyStepRf_get_x7, hx7Init, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      decide
    · change setBytes ws0 (8 * 0)
        (dwordBytes (packBytes ((srcBytes.drop (8 * 0)).take 8))) =
        copyWin384 srcBytes ws0 (0 + 1)
      simpa [copyWin384_zero srcBytes ws0] using
        copyWin384_step srcBytes ws0 0 hs ho (by omega)
  case bnqCopy.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx10, hx11, hx7, hlt, hs, ho, hfr, hws₀, hA⟩, hcond⟩, rfl, rfl⟩
    dsimp only [bnqCopyFn] at hbase ⊢
    have hwsLen : ws₀.length = 384 := by
      rw [hws₀]
      exact length_copyWin384 srcBytes orig (i + 1) hs ho (by omega)
    rw [copy_engine src dst srcBytes rf₀ ws₀ (i + 1) (by omega) hx10 hx11 hwsLen hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_, hA⟩
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
    · rw [hws₀, copyWin384_step srcBytes orig (i + 1) hs ho (by omega)]
  case bnqCopy.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx7, -, -, -, -, -, -⟩
    simp only [Cond.holds, hx7, not_not, RegFile.get_x0]
    decide
  case bnqCopy.loop.body.copy.mem =>
    rintro rf ws A hlen (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, -, ⟨hx10, hx11, rfl, hs, ho, hfr, -⟩, rfl, rfl⟩
      have hlen384 : ws.length = 384 := by
        change ws.length = 384 at hlen
        exact hlen
      exact copy_blockVCs src dst srcBytes _ ws 0 (by omega)
        (by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
            ne_eq, reduceCtorEq, not_false_eq_true, hx10]
          bv_omega)
        (by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
            ne_eq, reduceCtorEq, not_false_eq_true, hx11]
          bv_omega) hlen384 hs hfr
    · rcases hloop with ⟨i, hi, ⟨hx10, hx11, hx7, hlt, hs, ho, hfr, hws, -⟩, hcond⟩
      have hlen384 : ws.length = 384 := by
        change ws.length = 384 at hlen
        exact hlen
      exact copy_blockVCs src dst srcBytes rf ws (i + 1) (by omega) hx10 hx11 hlen384 hs hfr
  case bnqCopy.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx11, hx7, hlt, hs, ho, hfr, hws, hA⟩, hncond⟩
    have hi47 : i = 47 := by
      simp only [Cond.holds, hx7, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi47
    -- conjunction now: window equality, then the pinned ambient
    exact ⟨by rw [hws, copyWin384_48_eq srcBytes orig hs ho], hA⟩

/-! ## Flat linked-entry contract (#12244)

    Same recipe as `bncZero64Flat_spec`, on the COPIER shape. ⚠️ One structural
    difference from the zeroers: `region := ⟨src, srcBytes⟩` is NON-EMPTY, so the
    read-only source window rides through the adapter as an outer conjunct and the
    `Region.empty` collapse the zeroer lifts use does not apply here. -/

def bnqCopyCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bnq_copy : Word) bnqCopy_prog

/-- The exposed registers other than `a0`/`a1`. -/
def bnqCopyScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_bnqCopy (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf bnqCopyScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bnqCopyScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_bnqCopy_scratch : (.x10 : Reg) ∉ bnqCopyScratch := by decide
private theorem x11_notin_bnqCopy_scratch : (.x11 : Reg) ∉ bnqCopyScratch := by decide

/-- **`bnq_copy`, whole-routine flat triple at the guest entry.**

    Copies the 384 bytes at `a0` to `a1`. Anchored over
    `bnqCopyCr = CodeReq.ofProg (GuestAddrs.bnq_copy) bnqCopy_prog`, the `GuestImageEntries`
    pairing, so this IS the image claim and is rowable.

    DETERMINISTIC post: the destination becomes exactly `srcBytes`, and the SOURCE
    region is pinned INTACT.

    ⚠️ NOT total over its argument types: `frameOk384 src dst` unfolds to both bases
    non-overflowing AND the two windows DISJOINT, so the overlapping case is outside
    the domain rather than handled. -/
theorem bnqCopyFlat_spec (ret src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwfR : Region.wf ⟨src, srcBytes⟩) (hrww : RwRegion.wf ⟨dst, 384⟩)
    (hs : srcBytes.length = 384) (ho : orig.length = 384)
    (hfr : frameOk384 src dst)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bnqCopyFn src dst srcBytes orig).body.steps + 1)
      (GuestAddrs.bnq_copy : Word) ret bnqCopyCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) **
        regOwns bnqCopyScratch ** bytesRegion dst orig ** bytesRegion src srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst srcBytes ** bytesRegion src srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bnqCopyScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) **
        bytesRegion dst orig ** bytesRegion src srcBytes)
      (fun vf => ?_))
  have hpre : (bnqCopyFn src dst srcBytes orig).pre
      (fun r => if r = .x10 then src else if r = .x11 then dst else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, rfl, hs, ho, hfr, rfl⟩
    · show RegFile.get _ .x10 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlat (bnqCopyFn src dst srcBytes orig)
    (GuestAddrs.bnq_copy : Word)
    (bnqCopyFn_spec src dst srcBytes orig hwfR hrww (GuestAddrs.bnq_copy : Word))
    -- literal, not `body.size`: a `show` mentioning the arguments leaves free
    -- variables and `decide` refuses.
    (by show 4 * (7 + 1) ≤ 2 ^ 64; decide)
    ret halign
    (fun r => if r = .x10 then src else if r = .x11 then dst else vf r)
    orig ho hpre
    (fun _ _ _ hpost => hpost.2)
    (Q := regOwns exposedRegs ** bytesRegion dst srcBytes)
    (fun rf' ws' _ hpost' hp hh => by
      obtain ⟨hws', -⟩ := hpost'
      subst ws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (bnqCopyFn src dst srcBytes orig).programRet (GuestAddrs.bnq_copy : Word)
      = bnqCopy_prog from rfl] at had
  rw [show (bnqCopyFn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl,
      show (bnqCopyFn src dst srcBytes orig).rw.base = dst from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_bnqCopy,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then dst else vf .x10) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then dst else vf .x11) = dst from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else if r = .x11 then dst else vf r)
      vf bnqCopyScratch
      (fun r hr => by
        show (if r = .x10 then src else if r = .x11 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_bnqCopy_scratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_bnqCopy_scratch (hc ▸ hr))])] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end Bn254Fq12CopySAsm

end EvmAsm.Codegen
