/-
  EvmAsm.Rv64.ByteOps

  Byte-level infrastructure: extractByte/replaceByte algebra and
  generic CPS specs for LBU (load byte unsigned) and SB (store byte).
-/
import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.CPSSpec
import Mathlib.Tactic

namespace EvmAsm.Rv64

/-! ## byteOffset bound -/

theorem byteOffset_lt_8 (addr : Word) : byteOffset addr < 8 := by
  unfold byteOffset; rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-! ## extractByte / replaceByte algebra

Proved by `ext i` then `simp` + `interval_cases i` for the remaining
concrete-literal goals. -/

local macro "byte_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 8); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

private theorem erbs_0 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 0 b) 0 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_1 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 1 b) 1 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_2 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 2 b) 2 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_3 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 3 b) 3 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_4 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 4 b) 4 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_5 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 5 b) 5 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_6 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 6 b) 6 = b := by
  simp only [extractByte, replaceByte]; byte_algebra
private theorem erbs_7 (w : Word) (b : BitVec 8) :
    extractByte (replaceByte w 7 b) 7 = b := by
  simp only [extractByte, replaceByte]; byte_algebra

theorem extractByte_replaceByte_same (w : Word) (pos : Fin 8) (b : BitVec 8) :
    extractByte (replaceByte w pos.val b) pos.val = b := by
  fin_cases pos <;> first
    | exact erbs_0 w b | exact erbs_1 w b | exact erbs_2 w b | exact erbs_3 w b
    | exact erbs_4 w b | exact erbs_5 w b | exact erbs_6 w b | exact erbs_7 w b

/-! ## getByte / setByte in terms of extractByte / replaceByte -/

theorem getByte_eq (s : MachineState) (addr : Word) :
    s.getByte addr = extractByte (s.getMem (alignToDword addr)) (byteOffset addr) := rfl

theorem setByte_eq (s : MachineState) (addr : Word) (b : BitVec 8) :
    s.setByte addr b = s.setMem (alignToDword addr)
      (replaceByte (s.getMem (alignToDword addr)) (byteOffset addr) b) := rfl

/-! ## LBU generic spec

LBU reads a byte from memory at an arbitrary byte address. The precondition
owns the containing doubleword; the postcondition preserves it unchanged. -/

theorem generic_lbu_spec (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LBU rd rs1 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.LBU rd rs1 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LBU rd rs1 offset)) :=
    step_lbu s hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LBU rd rs1 offset) =
      (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64)).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg
      (v' := (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64)
      hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h4

/-! ## LB generic spec

LB reads a byte from memory at an arbitrary byte address and sign-extends it.
The precondition owns the containing doubleword; the postcondition preserves it unchanged. -/

theorem generic_lb_spec (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LB rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LB rd rs1 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.LB rd rs1 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LB rd rs1 offset)) :=
    step_lb s hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LB rd rs1 offset) =
      (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64)).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg
      (v' := (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64)
      hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h4

/-! ## SB generic spec

SB writes a byte to memory at an arbitrary byte address. -/

theorem generic_sb_spec (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SB rs1 rs2 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.SB rs1 rs2 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordOld :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.SB rs1 rs2 offset)) :=
    step_sb s hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.SB rs1 rs2 offset) =
      (s.setMem dwordAddr (replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setByte_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setMem dwordAddr (replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8))).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIs_setMem
      (v' := replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8)) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h5

end EvmAsm.Rv64
