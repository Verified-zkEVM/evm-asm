/-
  EvmAsm.Rv64.WordOps

  Word32-level infrastructure: extractWord32/replaceWord32 algebra and
  generic CPS specs for LW (load word signed), LWU (load word unsigned),
  and SW (store word).
-/
import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.CPSSpec
import Mathlib.Tactic

namespace EvmAsm.Rv64

/-! ## extractWord32 / replaceWord32 algebra -/

local macro "word32_algebra" : tactic =>
  `(tactic| (ext i (hi : i < 32); simp [BitVec.truncate, BitVec.zeroExtend];
             try { interval_cases i <;> simp_all }))

private theorem erws_0 (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 0 v) 0 = v := by
  simp only [extractWord32, replaceWord32, show (0 : Nat) * 32 = 0 from rfl]; word32_algebra
private theorem erws_1 (w : Word) (v : BitVec 32) :
    extractWord32 (replaceWord32 w 1 v) 1 = v := by
  simp only [extractWord32, replaceWord32, show (1 : Nat) * 32 = 32 from rfl]; word32_algebra

theorem extractWord32_replaceWord32_same (w : Word) (pos : Fin 2) (v : BitVec 32) :
    extractWord32 (replaceWord32 w pos.val v) pos.val = v := by
  fin_cases pos <;> first
    | exact erws_0 w v | exact erws_1 w v

/-! ## getWord32 / setWord32 in terms of extractWord32 / replaceWord32 -/

theorem getWord32_eq (s : MachineState) (addr : Word) :
    s.getWord32 addr = extractWord32 (s.getMem (alignToDword addr)) ((byteOffset addr) / 4) := rfl

theorem setWord32_eq (s : MachineState) (addr : Word) (v : BitVec 32) :
    s.setWord32 addr v = s.setMem (alignToDword addr)
      (replaceWord32 (s.getMem (alignToDword addr)) ((byteOffset addr) / 4) v) := rfl

/-! ## LWU generic spec

LWU reads a 32-bit word from memory at a 4-byte aligned address and zero-extends it. -/

theorem generic_lwu_spec (rd rs1 : Reg) (v_addr v_old : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LWU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LWU rd rs1 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.LWU rd rs1 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LWU rd rs1 offset)) :=
    step_lwu s rd rs1 offset hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LWU rd rs1 offset) =
      (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getWord32_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).zeroExtend 64)).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg
      (v' := (extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).zeroExtend 64)
      hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h4

/-! ## LW generic spec

LW reads a 32-bit word from memory at a 4-byte aligned address and sign-extends it. -/

theorem generic_lw_spec (rd rs1 : Reg) (v_addr v_old : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.LW rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LW rd rs1 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.LW rd rs1 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LW rd rs1 offset)) :=
    step_lw s rd rs1 offset hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LW rd rs1 offset) =
      (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getWord32_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).signExtend 64)).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg
      (v' := (extractWord32 wordVal ((byteOffset (v_addr + signExtend12 offset)) / 4)).signExtend 64)
      hrd_ne_x0 h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h4

/-! ## SW generic spec

SW writes the lower 32 bits of a register to memory at a 4-byte aligned address. -/

theorem generic_sw_spec (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (word_old : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ word_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceWord32 word_old ((byteOffset (v_addr + signExtend12 offset)) / 4) (v_data.truncate 32))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SW rs1 rs2 offset) :=
    (CodeReq.singleton_satisfiedBy s.pc (.SW rs1 rs2 offset) s).mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = word_old :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.SW rs1 rs2 offset)) :=
    step_sw s rs1 rs2 offset hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.SW rs1 rs2 offset) =
      (s.setMem dwordAddr (replaceWord32 word_old ((byteOffset (v_addr + signExtend12 offset)) / 4) (v_data.truncate 32))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setWord32_eq]; rw [halign, hmem]
  refine ⟨1,
    (s.setMem dwordAddr (replaceWord32 word_old ((byteOffset (v_addr + signExtend12 offset)) / 4) (v_data.truncate 32))).setPC (s.pc + 4),
    ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIs_setMem
      (v' := replaceWord32 word_old ((byteOffset (v_addr + signExtend12 offset)) / 4) (v_data.truncate 32)) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) _ _ h5

end EvmAsm.Rv64
