/-
  EvmAsm.Rv64.SAsm.RegionSound

  Soundness of byte loads from the SAsm read-only region: a supported load
  (`LBU`/`LB`) at regFileIs granularity reads exactly the region byte the
  pure engine (`Region.byteAt`) computes, leaving the `bytesRegion`
  assertion untouched.

  The bridge from the dword-packed memory model is
  `holdsFor_bytesRegion_getByte`, built on `bytesRegion_dword_at` and the
  `extractByte`/`packBytes` algebra (EvmAsm.Rv64.MemRegion / ByteOps).
-/

import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.SAsm.Sym
import EvmAsm.Rv64.SAsm.RegFileSep

namespace EvmAsm.Rv64
namespace SAsm

private theorem sepConj_left_comm (A B C : Assertion) :
    (A ** (B ** C)) = (B ** (A ** C)) := by
  rw [← sepConj_assoc', sepConj_comm' A B, sepConj_assoc']

/-- Extract byte `i` of a framed `bytesRegion` from the machine state. -/
theorem holdsFor_bytesRegion_getByte {b : Word} {bs : List (BitVec 8)}
    {R : Assertion} {s : MachineState}
    (hPR : ((bytesRegion b bs) ** R).holdsFor s)
    {i : Nat} (halign : b.toNat % 8 = 0) (hi : i < bs.length)
    (hover : b.toNat + i < 2 ^ 64) :
    s.getByte (b + BitVec.ofNat 64 i) = bs[i]'hi := by
  obtain ⟨front, rest, hfp, hrp, heq⟩ :=
    bytesRegion_dword_at b bs (i / 8) (by omega)
  rw [heq] at hPR
  have hcell : (((b + BitVec.ofNat 64 (8 * (i / 8))) ↦ₘ
      packBytes ((bs.drop (8 * (i / 8))).take 8))).holdsFor s :=
    holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hmem := (holdsFor_memIs.mp hcell).1
  show extractByte (s.getMem (alignToDword (b + BitVec.ofNat 64 i)))
    (byteOffset (b + BitVec.ofNat 64 i)) = bs[i]'hi
  rw [alignToDword_add_ofNat_of_aligned halign hover,
    byteOffset_add_ofNat_of_aligned halign hover, hmem]
  have hchunk : i % 8 < ((bs.drop (8 * (i / 8))).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [extractByte_packBytes _ (i % 8) (by omega) hchunk]
  rw [List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- Byte-load spec at register-file granularity: one step, the destination
    receives the extended region byte at the effective address, the region
    itself is untouched. -/
theorem regFile_load_spec_within (i : Instr) (l : LoadOp) (reg : Region)
    (rf : RegFile) (base : Word)
    (hsem : loadSem i = some l)
    (hreg : reg.wf)
    (hrd : (Reg.isExposed l.rd || l.rd == .x0) = true)
    (hrs1 : (Reg.isExposed l.rs1 || l.rs1 == .x0) = true)
    (hin : ((rf.get l.rs1 + signExtend12 l.ofs) - reg.base).toNat
      < reg.bytes.length) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.singleton base i)
      ((regFileIs rf) ** bytesRegion reg.base reg.bytes)
      ((regFileIs (rf.set l.rd
          (l.ext (reg.byteAt (rf.get l.rs1 + signExtend12 l.ofs))))) **
        bytesRegion reg.base reg.bytes) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some i := CodeReq.singleton_satisfiedBy.mp hcr
  rw [sepConj_assoc'] at hPR
  -- hPR : (regFileIs rf ** (bytesRegion ** R)).holdsFor s
  have hrs1v : s.getReg l.rs1 = rf.get l.rs1 :=
    holdsFor_regFileIs_agree hPR hrs1
  have haddr_eq : rf.get l.rs1 + signExtend12 l.ofs
      = reg.base + BitVec.ofNat 64
          ((rf.get l.rs1 + signExtend12 l.ofs) - reg.base).toNat := by
    bv_omega
  have hover : reg.base.toNat
      + ((rf.get l.rs1 + signExtend12 l.ofs) - reg.base).toNat < 2 ^ 64 := by
    have := hreg.2.1
    omega
  have hvalidmem : isValidMemAddr (rf.get l.rs1 + signExtend12 l.ofs) = true := by
    rw [haddr_eq]
    exact hreg.2.2 _ hin
  have hvalid : isValidByteAccess (s.getReg l.rs1 + signExtend12 l.ofs) = true := by
    rw [isValidByteAccess_eq, hrs1v]
    exact hvalidmem
  -- the loaded byte
  have hPR2 : ((bytesRegion reg.base reg.bytes) ** (regFileIs rf ** R)).holdsFor s := by
    rw [sepConj_left_comm] at hPR
    exact hPR
  have hgb : s.getByte (rf.get l.rs1 + signExtend12 l.ofs) = reg.bytes[
      ((rf.get l.rs1 + signExtend12 l.ofs) - reg.base).toNat]'hin := by
    conv_lhs => rw [haddr_eq]
    exact holdsFor_bytesRegion_getByte hPR2 hreg.1 hin hover
  have hbyteAt : reg.byteAt (rf.get l.rs1 + signExtend12 l.ofs)
      = reg.bytes[((rf.get l.rs1 + signExtend12 l.ofs) - reg.base).toNat]'hin := by
    unfold Region.byteAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin]
    rfl
  -- one machine step
  have hstep' : step s = some (execInstrBr s i) := by
    cases i <;> simp only [loadSem, reduceCtorEq] at hsem <;>
      (injection hsem with hsem; subst hsem;
       first
         | exact step_lbu hfetch hvalid
         | exact step_lb hfetch hvalid)
  have hexec : execInstrBr s i
      = (s.setReg l.rd (l.ext (s.getByte (rf.get l.rs1 + signExtend12 l.ofs)))).setPC
          (s.pc + 4) := by
    cases i <;> simp only [loadSem, reduceCtorEq] at hsem <;>
      (injection hsem with hsem; subst hsem;
       simp only [execInstrBr]; rw [hrs1v])
  refine ⟨1, Nat.le_refl 1,
    (s.setReg l.rd (l.ext (s.getByte (rf.get l.rs1 + signExtend12 l.ofs)))).setPC
      (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec]; rfl
  · rw [hgb, ← hbyteAt] at *
    rcases Bool.or_eq_true_iff.mp hrd with hexp | hx0
    · have h1 := holdsFor_sepConj_regFileIs_setReg
        (v := l.ext (reg.byteAt (rf.get l.rs1 + signExtend12 l.ofs))) hexp hPR
      rw [← sepConj_assoc'] at h1
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regFileIs _)
          (bytesRegion_pcFree _ _)) hR) h1
    · have hx0' : l.rd = .x0 := by simpa using hx0
      rw [hx0', RegFile.set_x0]
      rw [show s.setReg .x0
        (l.ext (reg.byteAt (rf.get l.rs1 + signExtend12 l.ofs))) = s from rfl]
      rw [← sepConj_assoc'] at hPR
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regFileIs _)
          (bytesRegion_pcFree _ _)) hR) hPR

-- ============================================================================
-- The region-carrying reachable-set embedding
-- ============================================================================

/-- Leaf-shaped embedding of a reachable set: the exposed register file plus
    the function's read-only region. -/
def asrtM (reg : Region) (reach : Reach) : Assertion :=
  asrtOf reach ** bytesRegion reg.base reg.bytes

theorem pcFree_asrtM (reg : Region) (reach : Reach) : (asrtM reg reach).pcFree :=
  pcFree_sepConj (pcFree_asrtOf _) (bytesRegion_pcFree _ _)

theorem asrtM_mono {reg : Region} {r₁ r₂ : Reach} (h : ∀ rf, r₁ rf → r₂ rf) :
    ∀ hp, asrtM reg r₁ hp → asrtM reg r₂ hp :=
  fun hp => sepConj_mono_left (fun hq hh => by
    obtain ⟨rf, hrf, hr⟩ := hh
    exact ⟨rf, hrf, h rf hr⟩) hp

theorem asrtM_unsat {reg : Region} {r : Reach} (h : ∀ rf, r rf → False) :
    ∀ hp, asrtM reg r hp → False := by
  rintro hp ⟨h1, h2, -, -, ⟨rf, -, hr⟩, -⟩
  exact h rf hr

/-- Split an `asrtM` precondition into a per-register-file family with the
    region alongside. -/
theorem cpsTripleWithin_exists_pre_M {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {reg : Region} {reach : Reach} {Q : Assertion}
    (h : ∀ rf, reach rf → cpsTripleWithin n entry exit_ cr
      ((regFileIs rf) ** bytesRegion reg.base reg.bytes) Q) :
    cpsTripleWithin n entry exit_ cr (asrtM reg reach) Q := by
  intro R hR s hcr hPR hpc
  rw [show asrtM reg reach
    = (asrtOf reach ** bytesRegion reg.base reg.bytes) from rfl,
    sepConj_assoc'] at hPR
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨rf, hrf1, hreach⟩, hR2⟩ := hPR
  have hPR' : ((regFileIs rf) ** (bytesRegion reg.base reg.bytes ** R)).holdsFor s :=
    ⟨hp, hcompat, h1, h2, hd, hu, hrf1, hR2⟩
  rw [← sepConj_assoc'] at hPR'
  exact h rf hreach R hR s hcr hPR' hpc

end SAsm
end EvmAsm.Rv64
