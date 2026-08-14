/-
  EvmAsm.Codegen.Programs.Bls12FieldCopyQuadsSAsm

  Verified SAsm port of `blsf_copy_quads`: copy `a2` aligned 8-byte quads
  from `a0` to `a1`.  This leaf is used by the BLS12-381 LE point/field
  wrappers and accelerator probes.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bls12Field
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bls12FieldCopyQuadsSAsm

/-- Static range/non-overlap facts for copying `n` 8-byte quads. -/
def frameOkN (src dst : Word) (n : Nat) : Prop :=
  src.toNat + 8 * n < 2 ^ 64 ∧ dst.toNat + 8 * n < 2 ^ 64 ∧
    (src.toNat + 8 * n ≤ dst.toNat ∨ dst.toNat + 8 * n ≤ src.toNat)

def copyWinN (srcBytes orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  srcBytes.take (8 * i) ++ orig.drop (8 * i)

theorem copyWinN_zero (srcBytes orig : List (BitVec 8)) :
    copyWinN srcBytes orig 0 = orig := by
  simp [copyWinN]

theorem copyWinN_end (srcBytes orig : List (BitVec 8)) (n : Nat)
    (hs : srcBytes.length = 8 * n) (ho : orig.length = 8 * n) :
    copyWinN srcBytes orig n = srcBytes := by
  simp only [copyWinN]
  rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem length_copyWinN (srcBytes orig : List (BitVec 8)) (n i : Nat)
    (hs : srcBytes.length = 8 * n) (ho : orig.length = 8 * n) (hi : i ≤ n) :
    (copyWinN srcBytes orig i).length = 8 * n := by
  simp only [copyWinN, List.length_append, List.length_take, List.length_drop, hs, ho]
  omega

theorem copyWinN_step (srcBytes orig : List (BitVec 8)) (n i : Nat)
    (hs : srcBytes.length = 8 * n) (ho : orig.length = 8 * n) (hi : i < n) :
    setBytes (copyWinN srcBytes orig i) (8 * i)
      (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8))) =
    copyWinN srcBytes orig (i + 1) := by
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
  rw [copyWinN]
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
  simp only [copyWinN]
  rw [← List.append_assoc]
  congr 1
  rw [show srcBytes.take (8 * i) ++ (srcBytes.drop (8 * i)).take 8 =
      srcBytes.take (8 * (i + 1)) from by
    rw [← List.take_add]
    congr 1]

def copyStepBlock : List Instr :=
  [.LD .x5 .x10 (0 : BitVec 12),
   .SD .x11 .x5 (0 : BitVec 12),
   .ADDI .x10 .x10 (8 : BitVec 12),
   .ADDI .x11 .x11 (8 : BitVec 12),
   .ADDI .x12 .x12 (-1 : BitVec 12)]

def copyStepRf (rf : RegFile) (v : Word) : RegFile :=
  let r1 := rf.set .x5 v
  let r2 := r1.set .x10 (r1.get .x10 + signExtend12 (8 : BitVec 12))
  let r3 := r2.set .x11 (r2.get .x11 + signExtend12 (8 : BitVec 12))
  r3.set .x12 (r3.get .x12 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x10 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x10 = rf.get .x10 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x11 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x11 = rf.get .x11 + signExtend12 (8 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

theorem copyStepRf_get_x12 (rf : RegFile) (v : Word) :
    (copyStepRf rf v).get .x12 = rf.get .x12 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]


private theorem ptr_add8 (base : Word) (off : Nat) (_hfit : base.toNat + off + 8 < 2 ^ 64) :
    base + BitVec.ofNat 64 off + (8 : Word) = base + BitVec.ofNat 64 (off + 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show ((8 : Word)).toNat = 8 from by decide]
  omega

private theorem counter_dec (a : Nat) (hpos : 0 < a) (hlt : a < 2 ^ 64) :
    (BitVec.ofNat 64 a : Word) + (-1 : Word) = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 2 ^ 64 - 1 from by decide]
  omega

private theorem ld_romiss (reg : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwb ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF reg rwb rf ws (.LD rd rs1 ofs)
      = (rf.set rd (reg.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

private theorem src_miss8 (src dst : Word) (ws : List (BitVec 8)) (n k : Nat)
    (hk : k < n) (hws : ws.length = 8 * n) (hfr : frameOkN src dst n) :
    ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain ⟨hnws, hnwd, hdisj⟩ := hfr
  unfold inRw
  rw [hws]
  rcases hdisj with h | h <;> bv_omega

private theorem src_dwordAt (src dst : Word) (srcBytes : List (BitVec 8)) (n k : Nat)
    (hk : k < n) (hfr : frameOkN src dst n) :
    Region.dwordAt ⟨src, srcBytes⟩ (src + BitVec.ofNat 64 (8 * k)) =
      packBytes ((srcBytes.drop (8 * k)).take 8) := by
  unfold Region.dwordAt
  have hlt : src.toNat + 8 * k < 2 ^ 64 := by
    obtain ⟨hsr, _, _⟩ := hfr
    omega
  rw [show (src + BitVec.ofNat 64 (8 * k) - src).toNat = 8 * k by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega]

private theorem copy_engine (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (n i : Nat) (hi : i < n)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (8 * i))
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 8 * n) (hfr : frameOkN src dst n) :
    execBlock ⟨src, srcBytes⟩ dst rf ws copyStepBlock =
      (copyStepRf rf (packBytes ((srcBytes.drop (8 * i)).take 8)),
       setBytes ws (8 * i) (dwordBytes (packBytes ((srcBytes.drop (8 * i)).take 8)))) := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x10 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by
    rw [hx10, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 :=
    src_miss8 src dst ws n i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x5 (packBytes ((srcBytes.drop (8 * i)).take 8))).get .x11
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11, hse0]
    obtain ⟨_, hd, _⟩ := hfr
    bv_omega
  rw [show copyStepBlock = [.LD .x5 .x10 0, .SD .x11 .x5 0,
      .ADDI .x10 .x10 8, .ADDI .x11 .x11 8, .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, ld_romiss _ _ _ _ .x5 .x10 (0 : BitVec 12) hmissExact,
    hloadAddr]
  rw [src_dwordAt src dst srcBytes n i hi hfr]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ (8 * i) hstoreAddr]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x5 ≠ .x0)]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold copyStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]

private theorem copy_blockVCs (src dst : Word) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8)) (n i : Nat) (hi : i < n)
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 (8 * i))
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 (8 * i))
    (hws : ws.length = 8 * n) (hs : srcBytes.length = 8 * n) (hfr : frameOkN src dst n) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws copyStepBlock := by
  have hse0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hloadAddr : rf.get .x10 + signExtend12 (0 : BitVec 12) =
      src + BitVec.ofNat 64 (8 * i) := by
    rw [hx10, hse0]
    bv_omega
  have hmiss : ¬ inRw dst ws (src + BitVec.ofNat 64 (8 * i)) 8 :=
    src_miss8 src dst ws n i hi hws hfr
  have hmissExact : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hloadAddr]
    exact hmiss
  have hstoreAddr : ((rf.set .x5 (Region.dwordAt ⟨src, srcBytes⟩
        (rf.get .x10 + signExtend12 (0 : BitVec 12)))).get .x11
      + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11, hse0]
    obtain ⟨_, hd, _⟩ := hfr
    bv_omega
  have hsrcOff : (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i := by
    obtain ⟨hsr, _, _⟩ := hfr
    bv_omega
  rw [show copyStepBlock = [.LD .x5 .x10 0, .SD .x11 .x5 0,
      .ADDI .x10 .x10 8, .ADDI .x11 .x11 8, .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl]
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
  · rw [ld_romiss _ _ _ _ .x5 .x10 (0 : BitVec 12) hmissExact]
    simp only [blockVCs, loadSem, storeSem]
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [hstoreAddr, hws]
      omega
    · exact ⟨trivial, trivial, trivial, trivial⟩

def copyInv (src dst : Word) (n : Nat) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x10 = src + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x11 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x12 = BitVec.ofNat 64 (n - i) ∧
    i ≤ n ∧ srcBytes.length = 8 * n ∧ orig.length = 8 * n ∧ frameOkN src dst n ∧
    ws = copyWinN srcBytes orig i ∧ A = empAssertion

def blsfCopyQuadsBody (src dst : Word) (n : Nat) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .while "loop" (.bne .x12 .x0) n (copyInv src dst n srcBytes orig)
    (.block "copy" copyStepBlock)

def blsfCopyQuadsFn (src dst : Word) (n : Nat) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "blsfCopyQuads"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 8 * n⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ rf.get .x12 = BitVec.ofNat 64 n ∧
    ws = orig ∧ srcBytes.length = 8 * n ∧ orig.length = 8 * n ∧
      frameOkN src dst n ∧ A = empAssertion
  post := fun _ ws A => ws = srcBytes ∧ A = empAssertion
  body := blsfCopyQuadsBody src dst n srcBytes orig

def blsfCopyQuads_verified : Program := (blsfCopyQuadsBody 0 0 0 [] []).flatten 0

#guard (blsfCopyQuads_verified : List Instr).length = 7
#guard (blsfCopyQuadsBody 0 0 0 [] []).flatten 0 = (blsfCopyQuadsBody 0 0 0 [] []).flatten 0x80000000
#guard (blsfCopyQuadsBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = blsfCopyQuads_prog

theorem blsfCopyQuadsFn_spec (src dst : Word) (n : Nat) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 8 * n⟩) (base : Word) :
    (blsfCopyQuadsFn src dst n srcBytes orig).Spec base := by
  have hbase : (blsfCopyQuadsFn src dst n srcBytes orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case blsfCopyQuads.loop.inv_init =>
    rintro rf ws A ⟨hx10, hx11, hx12, hws, hs, ho, hfr, hA⟩
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_, hA⟩
    · rw [hx10]
      bv_omega
    · rw [hx11]
      bv_omega
    · exact hx12
    · exact hws.trans (copyWinN_zero srcBytes orig).symm
  case blsfCopyQuads.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx11, hx12, hle, hs, ho, hfr, hws₀, hA⟩, hcond⟩, rfl, rfl⟩
    have hlt : i < n := by
      by_contra hnot
      have hin : i = n := by omega
      subst hin
      exact hcond (by simp [hx12])
    have hwsLen : ws₀.length = 8 * n := by
      rw [hws₀]
      exact length_copyWinN srcBytes orig n i hs ho hle
    rw [show (blsfCopyQuadsFn src dst n srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl,
      show (blsfCopyQuadsFn src dst n srcBytes orig).rw.base = dst from rfl]
    rw [copy_engine src dst srcBytes rf₀ ws₀ n i hlt hx10 hx11 hwsLen hfr]
    refine ⟨?_, ?_, ?_, by omega, hs, ho, hfr, ?_, hA⟩
    · rw [copyStepRf_get_x10, hx10, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      rw [show 8 * (i + 1) = 8 * i + 8 from by omega]
      exact ptr_add8 src (8 * i) (by obtain ⟨hsr, _, _⟩ := hfr; omega)
    · rw [copyStepRf_get_x11, hx11, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      rw [show 8 * (i + 1) = 8 * i + 8 from by omega]
      exact ptr_add8 dst (8 * i) (by obtain ⟨_, hdst, _⟩ := hfr; omega)
    · rw [copyStepRf_get_x12, hx12, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      rw [counter_dec (n - i) (by omega) (by obtain ⟨hsr, _, _⟩ := hfr; omega)]
      rw [show n - i - 1 = n - (i + 1) from by omega]
    · rw [hws₀, copyWinN_step srcBytes orig n i hs ho hlt]
  case blsfCopyQuads.loop.exhausted =>
    rintro rf ws A ⟨hx10, hx11, hx12, hle, hs, ho, hfr, hws, _⟩
    simp [Cond.holds, hx12]
  case blsfCopyQuads.loop.body.copy.mem =>
    rintro rf ws A hlen ⟨i, hi, ⟨hx10, hx11, hx12, hle, hs, ho, hfr, hws, _⟩, hcond⟩
    have hlt : i < n := by
      by_contra hnot
      have hin : i = n := by omega
      subst hin
      exact hcond (by simp [hx12])
    have hlenN : ws.length = 8 * n := by
      change ws.length = 8 * n at hlen
      exact hlen
    exact copy_blockVCs src dst srcBytes rf ws n i hlt hx10 hx11 hlenN hs hfr
  case blsfCopyQuads.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx11, hx12, hle', hs, ho, hfr, hws, hA⟩, hncond⟩
    have hi : i = n := by
      simp only [Cond.holds, hx12, RegFile.get_x0, not_not] at hncond
      have hnlt : n < 2 ^ 64 := by
        obtain ⟨hsr, _, _⟩ := hfr
        omega
      have hto := congrArg BitVec.toNat hncond
      rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at hto
      omega
    subst i
    rw [hws, copyWinN_end srcBytes orig n hs ho]
    exact ⟨rfl, hA⟩

/-! ## Flat linked-entry contract -/

def blsfCopyQuadsCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.blsf_copy_quads : Word) blsfCopyQuads_prog

def blsfCopyQuadsScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_copy_quads (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
        (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf blsfCopyQuadsScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [blsfCopyQuadsScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem copy_quads_args_notin_scratch :
    ∀ r ∈ blsfCopyQuadsScratch,
      r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide

theorem blsfCopyQuadsFlat_spec (ret src dst : Word) (n : Nat)
    (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 8 * n⟩)
    (hs : srcBytes.length = 8 * n) (ho : orig.length = 8 * n)
    (hfr : frameOkN src dst n)
    (hsz : 4 * ((blsfCopyQuadsFn src dst n srcBytes orig).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((blsfCopyQuadsFn src dst n srcBytes orig).body.steps + 1)
      (GuestAddrs.blsf_copy_quads : Word) ret blsfCopyQuadsCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) **
        (.x12 ↦ᵣ BitVec.ofNat 64 n) ** regOwns blsfCopyQuadsScratch **
        bytesRegion dst orig ** bytesRegion src srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion dst srcBytes ** bytesRegion src srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns blsfCopyQuadsScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) **
        (.x12 ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion dst orig **
        bytesRegion src srcBytes)
      (fun vf => ?_))
  have hpre : (blsfCopyQuadsFn src dst n srcBytes orig).pre
      (fun r => if r = .x10 then src else
        if r = .x11 then dst else if r = .x12 then BitVec.ofNat 64 n else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, ?_, rfl, hs, ho, hfr, rfl⟩
    · show RegFile.get _ .x10 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = BitVec.ofNat 64 n
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (blsfCopyQuadsFn src dst n srcBytes orig)
    (GuestAddrs.blsf_copy_quads : Word)
    (blsfCopyQuadsFn_spec src dst n srcBytes orig hwf hrww
      (GuestAddrs.blsf_copy_quads : Word))
    hsz ret halign
    (fun r => if r = .x10 then src else
      if r = .x11 then dst else if r = .x12 then BitVec.ofNat 64 n else vf r)
    orig empAssertion pcFree_emp (by simpa [blsfCopyQuadsFn] using ho) hpre
    (fun _ _ _ hpost => hpost.2)
    (Q := regOwns exposedRegs ** bytesRegion dst srcBytes)
    (fun rf' ws' _ hpost' hp hh => by
      obtain ⟨hws', -⟩ := hpost'
      rw [hws', show (blsfCopyQuadsFn src dst n srcBytes orig).rw.base = dst from rfl]
        at hh
      simp only [sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (blsfCopyQuadsFn src dst n srcBytes orig).programRet
      (GuestAddrs.blsf_copy_quads : Word) = blsfCopyQuads_prog from rfl] at had
  have hadC := had
  rw [show (blsfCopyQuadsFn src dst n srcBytes orig).rw.base = dst from rfl,
    show (blsfCopyQuadsFn src dst n srcBytes orig).region =
      (Region.mk src srcBytes) from rfl] at hadC
  simp only [sepConj_emp_right'] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_copy_quads,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then dst else
        if (Reg.x10 : Reg) = .x12 then BitVec.ofNat 64 n else vf .x10) = src
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then dst else
        if (Reg.x11 : Reg) = .x12 then BitVec.ofNat 64 n else vf .x11) = dst
      from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then src else
        if (Reg.x12 : Reg) = .x11 then dst else
        if (Reg.x12 : Reg) = .x12 then BitVec.ofNat 64 n else vf .x12) =
        BitVec.ofNat 64 n from by
      rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else
        if r = .x11 then dst else if r = .x12 then BitVec.ofNat 64 n else vf r)
      vf blsfCopyQuadsScratch
      (fun r hr => by
        show (if r = .x10 then src else
          if r = .x11 then dst else if r = .x12 then BitVec.ofNat 64 n else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) =>
              (copy_quads_args_notin_scratch r hr).1 hc),
            if_neg (fun (hc : r = .x11) =>
              (copy_quads_args_notin_scratch r hr).2.1 hc),
            if_neg (fun (hc : r = .x12) =>
              (copy_quads_args_notin_scratch r hr).2.2 hc)])] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end Bls12FieldCopyQuadsSAsm

end EvmAsm.Codegen
