/-
  EvmAsm.Rv64.ByteOps

  Byte-level infrastructure: extractByte/replaceByte algebra and
  generic CPS specs for LBU (load byte unsigned) and SB (store byte).
-/
-- `CPSSpec` transitively imports `Basic`, `SepLogic`, and `Execution`.
import EvmAsm.Rv64.CPSSpec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace EvmAsm.Rv64

/-! ## byteOffset bound -/

theorem byteOffset_lt_8 {addr : Word} : byteOffset addr < 8 := by
  unfold byteOffset; rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- Aligning a byte address down to its containing doubleword gives byte
    offset zero.  (`(addr &&& ~~~7) &&& 7 = addr &&& (~~~7 &&& 7) = addr &&& 0 = 0`.) -/
theorem alignToDword_byteOffset_zero (addr : Word) :
    byteOffset (alignToDword addr) = 0 := by
  unfold byteOffset alignToDword
  rw [BitVec.and_assoc, show (~~~7#64 &&& 7#64) = 0#64 from by decide, BitVec.and_zero]
  rfl

/-- Aligning an already dword-aligned address is idempotent
    (`(addr &&& ~~~7) &&& ~~~7 = addr &&& (~~~7 &&& ~~~7) = addr &&& ~~~7`). -/
theorem alignToDword_idempotent (addr : Word) :
    alignToDword (alignToDword addr) = alignToDword addr := by
  unfold alignToDword
  rw [BitVec.and_assoc, BitVec.and_self]

/-- The aligned base plus the byte offset reconstructs the original address, in `Nat` form.
    Disjoint-bit decomposition (proved WITHOUT `bv_decide`): the aligned base holds the high
    bits (`addr.toNat / 8 * 8`), the byte offset the low 3 bits (`addr.toNat % 8`). -/
theorem alignToDword_add_byteOffset_toNat (addr : Word) :
    (alignToDword addr).toNat + byteOffset addr = addr.toNat := by
  unfold alignToDword byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
             show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have hlo : addr.toNat &&& 7 = addr.toNat % 8 := by
    have h := Nat.and_two_pow_sub_one_eq_mod addr.toNat 3
    simpa using h
  have hhi_mod : (addr.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
        show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have hhi_div : (addr.toNat &&& (2 ^ 64 - 1 - 7)) / 8 = addr.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
        show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by have := addr.isLt; omega)
  have hhi : addr.toNat &&& (2 ^ 64 - 1 - 7) = addr.toNat / 8 * 8 := by
    have heucl := Nat.div_add_mod (addr.toNat &&& (2 ^ 64 - 1 - 7)) 8
    omega
  rw [hlo, hhi]; omega

/-- The aligned base plus the byte offset reconstructs the original address (BitVec form),
    derived from the `Nat` decomposition above — no `bv_decide`. -/
theorem alignToDword_add_byteOffset (addr : Word) :
    alignToDword addr + BitVec.ofNat 64 (byteOffset addr) = addr := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show byteOffset addr < 2 ^ 64 from by have := byteOffset_lt_8 (addr := addr); omega),
      alignToDword_add_byteOffset_toNat addr, Nat.mod_eq_of_lt addr.isLt]

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

theorem getByte_eq {s : MachineState} {addr : Word} :
    s.getByte addr = extractByte (s.getMem (alignToDword addr)) (byteOffset addr) := rfl

theorem setByte_eq {s : MachineState} {addr : Word} {b : BitVec 8} :
    s.setByte addr b = s.setMem (alignToDword addr)
      (replaceByte (s.getMem (alignToDword addr)) (byteOffset addr) b) := rfl

/-! ## LBU generic spec

LBU reads a byte from memory at an arbitrary byte address. The precondition
owns the containing doubleword; the postcondition preserves it unchanged. -/

theorem generic_lbu_spec_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LBU rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LBU rd rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LBU rd rs1 offset)) :=
    step_lbu hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LBU rd rs1 offset) =
      (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1,
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
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h4

/-! ## LB generic spec

LB reads a byte from memory at an arbitrary byte address and sign-extends it.
The precondition owns the containing doubleword; the postcondition preserves it unchanged. -/

theorem generic_lb_spec_within (rd rs1 : Reg) (v_addr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordVal : Word)
    (hrd_ne_x0 : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.LB rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** (dwordAddr ↦ₘ wordVal))
      ((rs1 ↦ᵣ v_addr) **
       (rd ↦ᵣ (extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64) **
       (dwordAddr ↦ₘ wordVal)) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LB rd rs1 offset) :=
    CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hstep' : step s = some (execInstrBr s (.LB rd rs1 offset)) :=
    step_lb hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.LB rd rs1 offset) =
      (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 offset))).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1,
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
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h4

/-! ## SB generic spec

SB writes a byte to memory at an arbitrary byte address. -/

theorem generic_sb_spec_within (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (base : Word)
    (dwordAddr : Word) (wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 offset) = dwordAddr)
    (hvalid : isValidByteAccess (v_addr + signExtend12 offset) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SB rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (dwordAddr ↦ₘ wordOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
       (dwordAddr ↦ₘ replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8))) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SB rs1 rs2 offset) :=
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
  have hstep' : step s = some (execInstrBr s (.SB rs1 rs2 offset)) :=
    step_sb hfetch (hrs1 ▸ hvalid)
  have hexec' : execInstrBr s (.SB rs1 rs2 offset) =
      (s.setMem dwordAddr (replaceByte wordOld (byteOffset (v_addr + signExtend12 offset)) (v_data.truncate 8))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1,
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
    exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) h5

/-! ## Compatibility wrappers -/
end EvmAsm.Rv64
