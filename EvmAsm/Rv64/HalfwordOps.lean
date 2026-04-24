/-
  EvmAsm.Rv64.HalfwordOps

  Halfword-level infrastructure: extractHalfword/replaceHalfword algebra and
  generic CPS specs for LH (load halfword signed), LHU (load halfword unsigned),
  and SH (store halfword).
-/
-- `CPSSpec` transitively imports `Basic`, `SepLogic`, and `Execution`.
import EvmAsm.Rv64.CPSSpec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace EvmAsm.Rv64

/-! ## extractHalfword / replaceHalfword algebra -/

local macro "halfword_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 16); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

private theorem erhs_0 (w : Word) (h : BitVec 16) :
    extractHalfword (replaceHalfword w 0 h) 0 = h := by
  simp only [extractHalfword, replaceHalfword]; halfword_algebra
private theorem erhs_1 (w : Word) (h : BitVec 16) :
    extractHalfword (replaceHalfword w 1 h) 1 = h := by
  simp only [extractHalfword, replaceHalfword]; halfword_algebra
private theorem erhs_2 (w : Word) (h : BitVec 16) :
    extractHalfword (replaceHalfword w 2 h) 2 = h := by
  simp only [extractHalfword, replaceHalfword]; halfword_algebra
private theorem erhs_3 (w : Word) (h : BitVec 16) :
    extractHalfword (replaceHalfword w 3 h) 3 = h := by
  simp only [extractHalfword, replaceHalfword]; halfword_algebra

theorem extractHalfword_replaceHalfword_same (w : Word) (pos : Fin 4) (h : BitVec 16) :
    extractHalfword (replaceHalfword w pos.val h) pos.val = h := by
  fin_cases pos <;> first
    | exact erhs_0 w h | exact erhs_1 w h | exact erhs_2 w h | exact erhs_3 w h

/-! ## getHalfword / setHalfword in terms of extractHalfword / replaceHalfword -/

theorem getHalfword_eq {s : MachineState} {addr : Word} :
    s.getHalfword addr = extractHalfword (s.getMem (alignToDword addr)) ((byteOffset addr) / 2) := rfl

theorem setHalfword_eq {s : MachineState} {addr : Word} {h : BitVec 16} :
    s.setHalfword addr h = s.setMem (alignToDword addr)
      (replaceHalfword (s.getMem (alignToDword addr)) ((byteOffset addr) / 2) h) := rfl

/-! ## halfwordOffset bound -/

private theorem byteOffset_lt_8' (addr : Word) : byteOffset addr < 8 := by
  unfold byteOffset; rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem halfwordOffset_lt_4 {addr : Word} : (byteOffset addr) / 2 < 4 := by
  have := byteOffset_lt_8' addr; omega

/-! ## LHU generic spec

LHU reads a halfword from memory at a 2-byte aligned address and zero-extends it. -/

theorem generic_lhu_spec (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidHalfwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LHU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LHU rd rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LHU rd rs1 offset)) :=
    step_lhu hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LHU rd rs1 offset) =
      (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getHalfword_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).zeroExtend 64)).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg
      (v' := (extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).zeroExtend 64)
      hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h4

/-! ## LH generic spec

LH reads a halfword from memory at a 2-byte aligned address and sign-extends it. -/

theorem generic_lh_spec (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidHalfwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LH rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LH rd rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LH rd rs1 offset)) :=
    step_lh hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LH rd rs1 offset) =
      (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getHalfword_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).signExtend 64)).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg
      (v' := (extractHalfword wordVal ((byteOffset (v_addr + signExtend12 offset)) / 2)).signExtend 64)
      hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h4

/-! ## SH generic spec

SH writes a halfword to memory at a 2-byte aligned address. -/

theorem generic_sh_spec (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidHalfwordAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.SH rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 offset)) / 2) (v_data.truncate 16))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SH rs1 rs2 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordOld :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.SH rs1 rs2 offset)) :=
    step_sh hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.SH rs1 rs2 offset) =
      (s.setMem dwordAddr (replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 offset)) / 2) (v_data.truncate 16))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setHalfword_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setMem dwordAddr (replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 offset)) / 2) (v_data.truncate 16))).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIs_setMem
      (v' := replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 offset)) / 2) (v_data.truncate 16)) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h5

end EvmAsm.Rv64
