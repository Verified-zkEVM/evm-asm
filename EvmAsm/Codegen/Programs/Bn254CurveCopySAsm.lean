/-
  EvmAsm.Codegen.Programs.Bn254CurveCopySAsm

  Verified SAsm port of `bnc_copy64`: copy a 64-byte BN254 affine point
  buffer from `a0` to `a1` using the emitted alignment-free byte loop.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Curve
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254CurveCopySAsm

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
  fun i rf ws A =>
    rf.get .x10 = src + BitVec.ofNat 64 i ∧
    rf.get .x11 = dst + BitVec.ofNat 64 i ∧
    rf.get .x5 = BitVec.ofNat 64 (64 - i) ∧
    i ≤ 64 ∧ srcBytes.length = 64 ∧ orig.length = 64 ∧ frameOk64 src dst ∧
    ws = copyWin64 srcBytes orig i ∧ A = empAssertion

def bncCopy64Body (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (64 : Word)] ;;;
  .while "loop" (.bne .x5 .x0) 64 (copyInv src dst srcBytes orig)
    (.block "copy" copyStepBlock)

def bncCopy64Fn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bncCopy64"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 64⟩
  -- ⚠️ Ambient PINNED in pre and post: both flat adapters need the post to DETERMINE
  -- it (`hpostEmp` / `hpostAmb`). See `bncZero64Fn` (#12244) for the worked precedent.
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧
    srcBytes.length = 64 ∧ orig.length = 64 ∧ frameOk64 src dst ∧ A = empAssertion
  post := fun _ ws A => ws = srcBytes ∧ A = empAssertion
  body := bncCopy64Body src dst srcBytes orig

def bncCopy64_verified : Program := (bncCopy64Body 0 0 [] []).flatten 0

#guard (bncCopy64_verified : List Instr).length = 8
#guard (bncCopy64Body 0 0 [] []).flatten 0 = (bncCopy64Body 0 0 [] []).flatten 0x80000000
#guard (bncCopy64Body 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = bncCopy64_prog

theorem bncCopy64Fn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 64⟩) (base : Word) :
    (bncCopy64Fn src dst srcBytes orig).Spec base := by
  have hbase : (bncCopy64Fn src dst srcBytes orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case bncCopy64.loop.inv_init =>
    rintro rf' ws' A' ⟨rf₀, ws₀, -, ⟨hx10, hx11, hws0, hs, ho, hfr, hA⟩, rfl, rfl⟩
    simp only [hbase]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_, hA⟩
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
  case bncCopy64.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx10, hx11, hx5, hle, hs, ho, hfr, hws₀, hA⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase, show (bncCopy64Fn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl]
    have hlt : i < 64 := by
      by_contra hnot
      have hi64 : i = 64 := by omega
      subst hi64
      exact hcond (by simp [hx5])
    have hwsLen : ws₀.length = 64 := by
      rw [hws₀]
      exact length_copyWin64 srcBytes orig i hs ho hle
    rw [copy_engine src dst srcBytes rf₀ ws₀ i hlt hx10 hx11 hwsLen hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_, hA⟩
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
  case bncCopy64.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx5, -, -, -, -, -, -⟩
    simp [Cond.holds, hx5]
  case bncCopy64.loop.body.copy.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx10, hx11, hx5, hle, hs, ho, hfr, hws, -⟩, hcond⟩
    have hlt : i < 64 := by
      by_contra hnot
      have hi64 : i = 64 := by omega
      subst hi64
      exact hcond (by simp [hx5])
    have hlen64 : ws.length = 64 := by
      change ws.length = 64 at hlen
      exact hlen
    exact copy_blockVCs src dst srcBytes rf ws i hlt hx10 hx11 hlen64 hs hfr
  case bncCopy64.post =>
    rintro rf ws A ⟨⟨i, hi, hx10, hx11, hx5, hle, hs, ho, hfr, hws, hA⟩, hncond⟩
    have hi64 : i = 64 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi64
    -- the post is a conjunction now: window equality, then the pinned ambient
    exact ⟨by rw [hws, copyWin64_64_eq srcBytes orig hs ho], hA⟩

/-! ## Flat linked-entry contract (#12244)

    Same recipe as `bncZero64Flat_spec`, on the COPIER shape. ⚠️ One structural
    difference from the zeroers: `region := ⟨src, srcBytes⟩` is NON-EMPTY, so the
    read-only source window rides through the adapter as an outer conjunct and the
    `Region.empty` collapse the zeroer lifts use does not apply here. -/

def bncCopy64Cr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bnc_copy64 : Word) bncCopy64_prog

/-- The exposed registers other than `a0`/`a1`. -/
def bncCopy64Scratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_bncCopy64 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** regAtomsOf vf bncCopy64Scratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bncCopy64Scratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_bncCopy64_scratch : (.x10 : Reg) ∉ bncCopy64Scratch := by decide
private theorem x11_notin_bncCopy64_scratch : (.x11 : Reg) ∉ bncCopy64Scratch := by decide

/-- **`bnc_copy64`, whole-routine flat triple at the guest entry.**

    Copies the 64 bytes at `a0` to `a1`. Anchored over
    `bncCopy64Cr = CodeReq.ofProg (GuestAddrs.bnc_copy64) bncCopy64_prog`, the `GuestImageEntries`
    pairing, so this IS the image claim and is rowable.

    DETERMINISTIC post: the destination becomes exactly `srcBytes`, and the SOURCE
    region is pinned INTACT.

    ⚠️ NOT total over its argument types: `frameOk64 src dst` unfolds to both bases
    non-overflowing AND the two windows DISJOINT, so the overlapping case is outside
    the domain rather than handled. -/
theorem bncCopy64Flat_spec (ret src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwfR : Region.wf ⟨src, srcBytes⟩) (hrww : RwRegion.wf ⟨dst, 64⟩)
    (hs : srcBytes.length = 64) (ho : orig.length = 64)
    (hfr : frameOk64 src dst)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bncCopy64Fn src dst srcBytes orig).body.steps + 1)
      (GuestAddrs.bnc_copy64 : Word) ret bncCopy64Cr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) **
        regOwns bncCopy64Scratch ** bytesRegion dst orig ** bytesRegion src srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst srcBytes ** bytesRegion src srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bncCopy64Scratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) **
        bytesRegion dst orig ** bytesRegion src srcBytes)
      (fun vf => ?_))
  have hpre : (bncCopy64Fn src dst srcBytes orig).pre
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
  have had := Fn.retSpecFlat (bncCopy64Fn src dst srcBytes orig)
    (GuestAddrs.bnc_copy64 : Word)
    (bncCopy64Fn_spec src dst srcBytes orig hwfR hrww (GuestAddrs.bnc_copy64 : Word))
    -- literal, not `body.size`: a `show` mentioning the arguments leaves free
    -- variables and `decide` refuses.
    (by show 4 * (8 + 1) ≤ 2 ^ 64; decide)
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
  rw [show (bncCopy64Fn src dst srcBytes orig).programRet (GuestAddrs.bnc_copy64 : Word)
      = bncCopy64_prog from rfl] at had
  rw [show (bncCopy64Fn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl,
      show (bncCopy64Fn src dst srcBytes orig).rw.base = dst from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_bncCopy64,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then dst else vf .x10) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then dst else vf .x11) = dst from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else if r = .x11 then dst else vf r)
      vf bncCopy64Scratch
      (fun r hr => by
        show (if r = .x10 then src else if r = .x11 then dst else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) => x10_notin_bncCopy64_scratch (hc ▸ hr)),
            if_neg (fun (hc : r = .x11) => x11_notin_bncCopy64_scratch (hc ▸ hr))])] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end Bn254CurveCopySAsm

end EvmAsm.Codegen
