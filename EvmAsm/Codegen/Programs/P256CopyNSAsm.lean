/-
  EvmAsm.Codegen.Programs.P256CopyNSAsm

  Verified SAsm port of `p256_copy_n`: copy `a2` bytes from `a0` to `a1`.
  This is the P256 helper variant of the top-tested byte-copy loop.
-/

import EvmAsm.Codegen.Programs.P256Verify
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace P256CopyNSAsm

/-- The `k`-th output byte: source byte at index `k` (forward copy). -/
def copyByte (bs : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  bs.getD k 0

/-- Loop window: first `i` output bytes are the copied prefix, the rest is the
    untouched tail of the original dst buffer. -/
def copyWin (bs orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (List.range i).map (copyByte bs) ++ orig.drop i

#guard copyWin [10,20,30] [0,0,0] 0 = [0,0,0]
#guard (List.range 3).map (copyByte [10,20,30]) = [10,20,30]

theorem copyWin_zero (bs orig : List (BitVec 8)) : copyWin bs orig 0 = orig := by
  simp [copyWin]

theorem length_copyWin (bs orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = len) (hi : i ≤ len) : (copyWin bs orig i).length = len := by
  simp only [copyWin, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

theorem copyWin_step (bs orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = len) (hi : i < len) :
    setBytes (copyWin bs orig i) i [copyByte bs i] = copyWin bs orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : ((List.range i).map (copyByte bs)).length = i := by simp
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [copyWin, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero]

theorem copyWin_len_eq (bs orig : List (BitVec 8)) (len : Nat)
    (h : orig.length = len) (hlen : len ≤ bs.length) :
    copyWin bs orig len = bs.take len := by
  have hnil : orig.drop len = [] := by simp [h]
  simp only [copyWin, hnil, List.append_nil]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]; omega
  · intro j hj1 hj2
    simp only [List.length_map, List.length_range] at hj1
    simp only [List.getElem_map, List.getElem_range, copyByte, List.getElem_take,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < bs.length by omega), Option.getD_some]

def p256CopyNStepBlock : List Instr :=
  [.LBU .x5 .x10 0,
   .SB .x11 .x5 0,
   .ADDI .x10 .x10 1,
   .ADDI .x11 .x11 1,
   .ADDI .x12 .x12 (-1 : BitVec 12)]

def p256CopyNInv (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x10 = src + BitVec.ofNat 64 i ∧
    rf.get .x11 = dst + BitVec.ofNat 64 i ∧
    rf.get .x12 = BitVec.ofNat 64 (len - i) ∧
    i ≤ len ∧ len ≤ bs.length ∧ orig.length = len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) ∧
    ws = copyWin bs orig i ∧ A = empAssertion

def p256CopyNBody (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Stmt :=
  .«while» "loop" (.bne .x12 .x0) len (p256CopyNInv src dst len bs orig)
    (.block "copy" p256CopyNStepBlock)

def p256CopyNFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Fn where
  name := "p256CopyN"
  region := ⟨src, bs⟩
  rw := ⟨dst, len⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ rf.get .x12 = BitVec.ofNat 64 len ∧
    ws = orig ∧ orig.length = len ∧ len ≤ bs.length ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) ∧
    A = empAssertion
  post := fun _ ws A => ws = bs.take len ∧ A = empAssertion
  body := p256CopyNBody src dst len bs orig

/-- Byte-identity: the structured loop body plus the shared return epilogue is the emitted `p256_copy_n`. -/
theorem p256CopyN_byte_tie :
    (p256CopyNBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] =
      p256CopyN_prog := rfl

#guard ((p256CopyNBody 0 0 0 [] []).flatten 0 : List Instr).length = 7
#guard (p256CopyNBody 0 0 0 [] []).flatten 0 = (p256CopyNBody 0 0 0 [] []).flatten 0x80000000

def p256CopyN_verified : Program :=
  (p256CopyNBody 0 0 0 [] []).flatten 0

#guard (p256CopyN_verified : List Instr).length = 7
#guard (p256CopyNBody 0 0 0 [] []).flatten 0 = (p256CopyNBody 0 0 0 [] []).flatten 0x80000000

/-- An `LBU` that misses the writable window reads the read-only region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- Register file after one loop body (given the loaded byte `b`). -/
def copyStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x5 (b.zeroExtend 64)
  let r2 := r1.set .x10 (r1.get .x10 + signExtend12 (1 : BitVec 12))
  let r3 := r2.set .x11 (r2.get .x11 + signExtend12 (1 : BitVec 12))
  r3.set .x12 (r3.get .x12 + signExtend12 (-1 : BitVec 12))

theorem copyStepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x10 = rf.get .x10 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x12),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
    RegFile.get_set_self _ _ _ (by decide : Reg.x10 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]

theorem copyStepRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x11 = rf.get .x11 + signExtend12 (1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x12),
    RegFile.get_set_self _ _ _ (by decide : Reg.x11 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]

theorem copyStepRf_get_x12 (rf : RegFile) (b : BitVec 8) :
    (copyStepRf rf b).get .x12 = rf.get .x12 + signExtend12 (-1 : BitVec 12) := by
  unfold copyStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x12 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]

/-- One loop body loads `src[i]`, stores it at `dst[i]`, and advances both
    cursors plus the counter. -/
theorem copy_step_engine (src dst : Word) (len i : Nat) (bs : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = src + BitVec.ofNat 64 i)
    (hx11 : rf.get .x11 = dst + BitVec.ofNat 64 i)
    (hi : i < len)
    (hsrc : src.toNat + len < 2 ^ 64) (hdst : dst.toNat + len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (hws : ws.length = len) :
    execBlock ⟨src, bs⟩ dst rf ws p256CopyNStepBlock
      = (copyStepRf rf (copyByte bs i), setBytes ws i [copyByte bs i]) := by
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  -- the load address `src + i` misses the writable window `[dst, dst+len)`
  have hloadaddr : rf.get .x10 + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 i := by
    rw [hx10, hse_0]; simp
  have hnr : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadaddr]
    unfold inRw
    rw [hws]
    have hsubd : (src + BitVec.ofNat 64 i - dst).toNat
        = (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; congr 1; omega
    rw [hsubd]
    rcases hdisj with hd | hd <;> omega
  -- the loaded byte equals `src[i]`
  have hval : (Region.byteAt ⟨src, bs⟩ (rf.get .x10 + signExtend12 (0 : BitVec 12)))
      = copyByte bs i := by
    rw [hloadaddr]
    show bs.getD ((src + BitVec.ofNat 64 i - src).toNat) 0 = copyByte bs i
    rw [show (src + BitVec.ofNat 64 i - src).toNat = i by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; omega]
    rfl
  -- the store address is index `i` of the writable window
  have hstore : (rf.get .x11 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx11, hse_0]
    bv_omega
  rw [show p256CopyNStepBlock =
      [.LBU .x5 .x10 0, .SB .x11 .x5 0, .ADDI .x10 .x10 (1 : BitVec 12),
       .ADDI .x11 .x11 (1 : BitVec 12), .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
  dsimp only
  rw [hval]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]; exact hstore)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton, truncate_zeroExtend_byte]
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
  rw [setBytes_singleton]

theorem p256CopyNFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩) (base : Word) :
    (p256CopyNFn src dst len bs orig).Spec base := by
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case p256CopyN.loop.inv_init =>
    rintro rf ws A ⟨hx10, hx11, hx12, rfl, hol, hlb, hsb, hdb, hdj, hA⟩
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_, hA⟩
    · rw [hx10]; simp
    · rw [hx11]; simp
    · rw [hx12]; simp
    · rw [copyWin_zero]
  case p256CopyN.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin, hA⟩, -⟩, rfl, rfl⟩
    have hwslen : ws₀.length = len := by rw [hwin]; exact length_copyWin bs orig i hol (by omega)
    simp only [show (p256CopyNFn src dst len bs orig).rw.base = dst from rfl,
      show (p256CopyNFn src dst len bs orig).region = ⟨src, bs⟩ from rfl]
    rw [copy_step_engine src dst len i bs rf₀ ws₀ hx10 hx11 hi hsb hdb hdj hwslen]
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_, hA⟩
    · rw [copyStepRf_get_x10, hx10, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x11, hx11, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x12, hx12, hse_m1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, copyWin_step bs orig i hol hi]
  case p256CopyN.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx12, hile, -, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx12]
    rw [show (BitVec.ofNat 64 (len - len)) = (0 : Word) by rw [show len - len = 0 by omega]; rfl]
    rfl
  case p256CopyN.loop.body.copy.mem =>
    rintro rf ws A hwslen ⟨i, hi, ⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin, -⟩, -⟩
    have hlen0 : ws.length = len := hwslen
    have hbase : (p256CopyNFn src dst len bs orig).rw.base = dst := rfl
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    have hloadaddr : rf.get .x10 + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 i := by
      rw [hx10, hse_0]; simp
    have hnr : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hloadaddr]
      unfold inRw
      rw [hlen0]
      have hsubd : (src + BitVec.ofNat 64 i - dst).toNat
          = (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; congr 1; omega
      rw [hsubd]; rcases hdj with hd | hd <;> omega
    have hload_ok : (src + BitVec.ofNat 64 i - src).toNat = i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; omega
    have hstore : (rf.get .x11 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx11, hse_0]; bv_omega
    rw [show p256CopyNStepBlock =
        [.LBU .x5 .x10 0, .SB .x11 .x5 0, .ADDI .x10 .x10 (1 : BitVec 12),
         .ADDI .x11 .x11 (1 : BitVec 12), .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl,
      show (p256CopyNFn src dst len bs orig).region = ⟨src, bs⟩ from rfl, hbase]
    -- LBU obligation (routes to read-only region) ∧ rest
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hnr]
      unfold Region.loadOk
      rw [hloadaddr, hload_ok]
      refine ⟨Nat.one_dvd _, ?_⟩
      show i + 1 ≤ bs.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
      -- SB obligation (writable, aligned) ∧ trailing ADDIs (no obligations)
      refine ⟨?_, trivial, trivial, trivial, trivial⟩
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hlen0, hstore]
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hstore]
        exact Nat.one_dvd _
  case p256CopyN.post =>
    rintro rf ws A ⟨⟨i, hile, hx10, hx11, hx12, hle, hlb, hol, hsb, hdb, hdj, hwin, hA⟩, hncond⟩
    have hi_len : i = len := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx12] at hncond
      have hz : rf.get .x0 = 0 := rfl
      rw [hz] at hncond
      have : (BitVec.ofNat 64 (len - i)).toNat = (0 : Word).toNat := by rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at this
      omega
    subst hi_len
    change ws = bs.take i ∧ A = empAssertion
    refine ⟨?_, hA⟩
    rw [hwin, copyWin_len_eq bs orig i hol hlb]

/-! ## Flat linked-entry contract

The structured copy proof above is the callee contract.  This adapter is the
caller-facing contract at the linked guest address; it exposes the complete
register file and keeps the source region framed read-only.
-/

def p256CopyNCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.p256_copy_n : Word) p256CopyN_prog

def p256CopyNScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_p256CopyN (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
        (.x12 ↦ᵣ vf .x12) ** regAtomsOf vf p256CopyNScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [p256CopyNScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem p256CopyN_scratch_disjoint :
    ∀ r ∈ p256CopyNScratch, r ≠ (.x10 : Reg) ∧
      r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide

theorem p256CopyNFlat_spec (ret src dst : Word) (len : Nat)
    (bs orig : List (BitVec 8))
    (holen : orig.length = len) (hbs : len ≤ bs.length)
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩)
    (hsb : src.toNat + len < 2 ^ 64)
    (hdb : dst.toNat + len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (hsz : 4 * ((p256CopyNFn src dst len bs orig).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((p256CopyNFn src dst len bs orig).body.steps + 1)
      (GuestAddrs.p256_copy_n : Word) ret p256CopyNCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
        ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) ** regOwns p256CopyNScratch
        ** bytesRegion dst orig ** bytesRegion src bs)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs
        ** bytesRegion dst (bs.take len) ** bytesRegion src bs) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns p256CopyNScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) **
        (.x11 ↦ᵣ dst) ** (.x12 ↦ᵣ (BitVec.ofNat 64 len)) **
        bytesRegion dst orig ** bytesRegion src bs)
      (fun vf => ?_))
  have hpre : (p256CopyNFn src dst len bs orig).pre
      (fun r => if r = .x10 then src else
        if r = .x11 then dst else
        if r = .x12 then BitVec.ofNat 64 len else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, ?_, rfl, holen, hbs, hsb, hdb, hdisj, rfl⟩
    · show RegFile.get _ .x10 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = BitVec.ofNat 64 len
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlat (p256CopyNFn src dst len bs orig)
    (GuestAddrs.p256_copy_n : Word)
    (p256CopyNFn_spec src dst len bs orig hwf hrww
      (GuestAddrs.p256_copy_n : Word))
    hsz ret halign
    (fun r => if r = .x10 then src else
      if r = .x11 then dst else
      if r = .x12 then BitVec.ofNat 64 len else vf r)
    orig (by simpa [p256CopyNFn] using holen) hpre
    (fun _ _ _ hpost => hpost.2)
    (Q := regOwns exposedRegs ** bytesRegion dst (bs.take len))
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain ⟨hws', -⟩ := hpost'
      subst hws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (p256CopyNFn src dst len bs orig).programRet
      (GuestAddrs.p256_copy_n : Word) = p256CopyN_prog from rfl] at had
  have hadC := liftCode (cr' := p256CopyNCr) had (by code_mem)
  rw [show (p256CopyNFn src dst len bs orig).region = (⟨src, bs⟩ : Region) from rfl,
    show (p256CopyNFn src dst len bs orig).rw.base = dst from rfl,
    regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_p256CopyN,
    show (if (Reg.x10 : Reg) = .x10 then src else
        if (Reg.x10 : Reg) = .x11 then dst else
        if (Reg.x10 : Reg) = .x12 then BitVec.ofNat 64 len else vf .x10) = src
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src else
        if (Reg.x11 : Reg) = .x11 then dst else
        if (Reg.x11 : Reg) = .x12 then BitVec.ofNat 64 len else vf .x11) = dst
      from by rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]; exact if_pos rfl,
    show (if (Reg.x12 : Reg) = .x10 then src else
        if (Reg.x12 : Reg) = .x11 then dst else
        if (Reg.x12 : Reg) = .x12 then BitVec.ofNat 64 len else vf .x12)
        = BitVec.ofNat 64 len
      from by rw [if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x10)),
        if_neg (by decide : ¬ ((Reg.x12 : Reg) = .x11))]; exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then src else
        if r = .x11 then dst else
        if r = .x12 then BitVec.ofNat 64 len else vf r)
      vf p256CopyNScratch
      (fun r hr => by
        show (if r = .x10 then src else
          if r = .x11 then dst else
          if r = .x12 then BitVec.ofNat 64 len else vf r) = vf r
        rw [if_neg (p256CopyN_scratch_disjoint r hr).1,
          if_neg (p256CopyN_scratch_disjoint r hr).2.1,
          if_neg (p256CopyN_scratch_disjoint r hr).2.2]
      )] at hadC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

end P256CopyNSAsm

end EvmAsm.Codegen
