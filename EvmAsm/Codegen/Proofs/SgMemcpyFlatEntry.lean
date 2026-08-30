/-
  EvmAsm.Codegen.Proofs.SgMemcpyFlatEntry

  The flat whole-routine contract for `sg_memcpy` at its linked guest
  address (#13090).  `sgMemcpyFn`'s ambient is FREE in both pre and
  post, which `Fn.retSpecFlatAmbient` cannot consume (its `hpostAmb`
  side-condition needs the post to pin the ambient), so this file
  carries an ambient-PINNED twin — same instructions, same emitted
  program, invariant conjoined with `A = empAssertion` — with its own
  `vcgen` discharge (the #12244 "leaf change" done as a twin so the
  shared `sgMemcpyFn` and its consumers stay untouched), and then the
  flat lift at `GuestAddrs.sg_memcpy`.
-/

import EvmAsm.Codegen.Programs.SgMemcpySAsm
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.SgMemcpyFlatEntry

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.SgMemcpySAsm

/-- The pinned loop invariant: the shared `sgMemcpyInv` with the ambient
    pinned to `empAssertion`. -/
def sgmcInv (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A => sgMemcpyInv src dst len bs orig i rf ws A
    ∧ A = empAssertion

def sgmcBody (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Stmt :=
  .«while» "loop" (.bne .x12 .x0) len (sgmcInv src dst len bs orig)
    (.block "copy" sgMemcpyStepBlock)

/-- Ambient-pinned twin of `sgMemcpyFn` (the shared `Fn` and its
    consumers are untouched). -/
def sgmcFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Fn where
  name := "sgMemcpyPinned"
  region := ⟨src, bs⟩
  rw := ⟨dst, len⟩
  pre := fun rf ws A =>
    (rf.get .x10 = dst ∧ rf.get .x11 = src ∧
      rf.get .x12 = BitVec.ofNat 64 len ∧
      ws = orig ∧ orig.length = len ∧ len ≤ bs.length ∧
      src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
      (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)) ∧
    A = empAssertion
  post := fun _ ws A => ws = bs.take len ∧ A = empAssertion
  body := sgmcBody src dst len bs orig

/-- The pinned twin flattens to the SAME emitted routine (`flatten`
    ignores invariants). -/
theorem sgmc_byte_tie :
    (sgmcFn 0 0 0 [] []).body.flatten 0
      ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)] = sgMemcpy_prog := rfl

theorem sgmcFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩)
    (base : Word) :
    (sgmcFn src dst len bs orig).Spec base := by
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case sgMemcpyPinned.loop.inv_init =>
    rintro rf ws A ⟨⟨hx10, hx11, hx12, rfl, hol, hlb, hsb, hdb, hdj⟩, rfl⟩
    refine ⟨⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩, rfl⟩
    · rw [hx10]; simp
    · rw [hx11]; simp
    · rw [hx12]; simp
    · rw [copyWin_zero]
  case sgMemcpyPinned.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin⟩, rfl⟩, -⟩,
      rfl, rfl⟩
    have hwslen : ws₀.length = len := by
      rw [hwin]; exact length_copyWin bs orig i hol (by omega)
    simp only [show (sgmcFn src dst len bs orig).rw.base = dst from rfl,
      show (sgmcFn src dst len bs orig).region = ⟨src, bs⟩ from rfl]
    rw [copy_step_engine src dst len i bs rf₀ ws₀ hx10 hx11 hi hsb hdb hdj
      hwslen]
    refine ⟨⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩, rfl⟩
    · rw [copyStepRf_get_x10, hx10, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x11, hx11, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [copyStepRf_get_x12, hx12, hse_m1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by
        rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, copyWin_step bs orig i hol hi]
  case sgMemcpyPinned.loop.exhausted =>
    rintro rf ws A ⟨⟨-, -, hx12, hile, -, -, -, -, -, -⟩, -⟩
    simp only [Cond.holds, not_not]
    rw [hx12]
    rw [show (BitVec.ofNat 64 (len - len)) = (0 : Word) by
      rw [show len - len = 0 by omega]; rfl]
    rfl
  case sgMemcpyPinned.loop.body.copy.mem =>
    rintro rf ws A hwslen ⟨i, hi,
      ⟨⟨hx10, hx11, hx12, hile, hlb, hol, hsb, hdb, hdj, hwin⟩, -⟩, -⟩
    have hlen0 : ws.length = len := hwslen
    have hbase : (sgmcFn src dst len bs orig).rw.base = dst := rfl
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]; omega
    have hloadaddr : rf.get .x11 + signExtend12 (0 : BitVec 12)
        = src + BitVec.ofNat 64 i := by
      rw [hx11, hse_0]; simp
    have hnr : ¬ inRw dst ws (rf.get .x11 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hloadaddr]
      unfold inRw
      rw [hlen0]
      have hsubd : (src + BitVec.ofNat 64 i - dst).toNat
          = (src.toNat + i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; congr 1; omega
      rw [hsubd]; rcases hdj with hd | hd <;> omega
    have hload_ok : (src + BitVec.ofNat 64 i - src).toNat = i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi2]; omega
    have hstore : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat
        = i := by
      rw [hx10, hse_0]; bv_omega
    rw [show sgMemcpyStepBlock =
        [.LBU .x5 .x11 0, .SB .x10 .x5 0, .ADDI .x10 .x10 (1 : BitVec 12),
         .ADDI .x11 .x11 (1 : BitVec 12),
         .ADDI .x12 .x12 (-1 : BitVec 12)] from rfl,
      show (sgmcFn src dst len bs orig).region = ⟨src, bs⟩ from rfl, hbase]
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hnr]
      unfold Region.loadOk
      rw [hloadaddr, hload_ok]
      refine ⟨Nat.one_dvd _, ?_⟩
      show i + 1 ≤ bs.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
      refine ⟨?_, trivial, trivial, trivial, trivial⟩
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hlen0,
          hstore]
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hstore]
        exact Nat.one_dvd _
  case sgMemcpyPinned.post =>
    rintro rf ws A ⟨⟨i, hile,
      ⟨⟨hx10, hx11, hx12, hle, hlb, hol, hsb, hdb, hdj, hwin⟩, rfl⟩⟩, hncond⟩
    have hi_len : i = len := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx12] at hncond
      have hz : rf.get .x0 = 0 := rfl
      rw [hz] at hncond
      have : (BitVec.ofNat 64 (len - i)).toNat = (0 : Word).toNat := by
        rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at this
      omega
    subst hi_len
    refine ⟨?_, rfl⟩
    show ws = bs.take i
    rw [hwin, copyWin_len_eq bs orig i hol hlb]

/-! ## The flat linked-entry contract -/

abbrev SgmcB : Word := (GuestAddrs.sg_memcpy : Word)
def sgmcCr : CodeReq := CodeReq.ofProg SgmcB sgMemcpy_prog

/-- The exposed registers except `a0`/`a1`/`a2`. -/
def sgmcScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_sgmc (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** (.x12 ↦ᵣ vf .x12) **
        regAtomsOf vf sgmcScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [sgmcScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private def sgmcRf (dst src nW : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x10 then dst else if r = .x11 then src
    else if r = .x12 then nW else vf r

/-- ⭐ **`sg_memcpy` at its linked guest address**: `a0` = dst, `a1` =
    src, `a2 = len` — the `len`-byte destination window becomes the
    source prefix, the source region intact. -/
theorem sgMemcpyFlat_spec (ret src dst : Word) (len : Nat)
    (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩)
    (horig : orig.length = len) (hlb : len ≤ bs.length)
    (hsb : src.toNat + len < 2 ^ 64) (hdb : dst.toNat + len < 2 ^ 64)
    (hdj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (hsz : 4 * ((sgmcFn src dst len bs orig).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((sgmcFn src dst len bs orig).body.steps + 1)
      SgmcB ret sgmcCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
        (.x12 ↦ᵣ BitVec.ofNat 64 len) ** regOwns sgmcScratch **
        bytesRegion src bs ** bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion src bs ** bytesRegion dst (bs.take len)) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns sgmcScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
        (.x12 ↦ᵣ BitVec.ofNat 64 len) **
        bytesRegion src bs ** bytesRegion dst orig)
      (fun vf => ?_))
  have hpre : (sgmcFn src dst len bs orig).pre
      (sgmcRf dst src (BitVec.ofNat 64 len) vf) orig empAssertion := by
    refine ⟨⟨?_, ?_, ?_, rfl, horig, hlb, hsb, hdb, hdj⟩, rfl⟩
    · show RegFile.get _ .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [sgmcRf, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = BitVec.ofNat 64 len
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [sgmcRf, if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (sgmcFn src dst len bs orig) SgmcB
    (sgmcFn_spec src dst len bs orig hwf hrww SgmcB) hsz ret halign
    (sgmcRf dst src (BitVec.ofNat 64 len) vf) orig empAssertion pcFree_emp
    (show orig.length = (sgmcFn src dst len bs orig).rw.len from horig) hpre
    (Q := regOwns exposedRegs ** bytesRegion dst (bs.take len))
    (fun _ _ _ hpost => hpost.2)
    (fun rf' ws' _hlen' hpost hp hh => by
      obtain ⟨rfl, -⟩ := hpost
      rw [sepConj_emp_right',
        show (sgmcFn src dst len bs orig).rw.base = dst from rfl,
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left
        (regAtomsOf_to_regOwns (fun r => rf' r) exposedRegs) hp hh)
  rw [show (sgmcFn src dst len bs orig).programRet SgmcB
      = sgMemcpy_prog from rfl] at had
  rw [show (sgmcFn src dst len bs orig).rw.base = dst from rfl,
    show (sgmcFn src dst len bs orig).region = Region.mk src bs from rfl]
    at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_sgmc,
    show sgmcRf dst src (BitVec.ofNat 64 len) vf .x10 = dst from if_pos rfl,
    show sgmcRf dst src (BitVec.ofNat 64 len) vf .x11 = src from by
      rw [sgmcRf, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl,
    show sgmcRf dst src (BitVec.ofNat 64 len) vf .x12 = BitVec.ofNat 64 len
      from by
      rw [sgmcRf, if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl,
    regAtomsOf_congr (fun r => sgmcRf dst src (BitVec.ofNat 64 len) vf r)
      vf sgmcScratch
      (fun r hr => by
        show (if r = .x10 then dst else if r = .x11 then src
          else if r = .x12 then BitVec.ofNat 64 len else vf r) = vf r
        rw [if_neg (fun hc => (by decide : (Reg.x10 : Reg) ∉ sgmcScratch)
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => (by decide : (Reg.x11 : Reg) ∉ sgmcScratch)
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => (by decide : (Reg.x12 : Reg) ∉ sgmcScratch)
              (by rw [← hc]; exact hr))])] at had
  rw [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

#print axioms sgMemcpyFlat_spec

end EvmAsm.Codegen.SgMemcpyFlatEntry
