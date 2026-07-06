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
    offset zero. -/
theorem alignToDword_byteOffset_zero (addr : Word) :
    byteOffset (alignToDword addr) = 0 := by
  unfold byteOffset alignToDword
  have h : (addr &&& ~~~(7 : Word)) &&& (7 : Word) = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i _hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases ha : (7 : Word).getLsbD i <;> simp
  have h' : ((addr &&& ~~~(7 : Word)) &&& (7 : Word)).toNat = 0 := by rw [h]; rfl
  exact h'

/-- Aligning an already dword-aligned address is idempotent. -/
theorem alignToDword_idempotent (addr : Word) :
    alignToDword (alignToDword addr) = alignToDword addr := by
  unfold alignToDword
  rw [BitVec.and_assoc, BitVec.and_self]

/-- The aligned base plus the byte offset reconstructs the original address. -/
theorem alignToDword_add_byteOffset (addr : Word) :
    alignToDword addr + BitVec.ofNat 64 (byteOffset addr) = addr := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- Goal: (addr &&& ~~~7#64) + (addr &&& 7#64) = addr
  -- Prove using or-factorization: the parts are disjoint
  have hdisj : (addr &&& ~~~7#64) &&& (addr &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;> simp [h7]
  have hor : (addr &&& ~~~7#64) ||| (addr &&& 7#64) = addr := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    rcases Bool.eq_false_or_eq_true (addr[i]) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;>
    simp [ha, h7]
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, hor]

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

/-! ## Byte packing — reconstruct 64-bit words from byte lists

These are pure byte-level operations (relocated here from `Evm64.CodeRegion`,
their natural home): `packBytes` packs a byte list little-endian into a dword,
and `extractByte_packBytes` reads byte `k` back out. Used by the EVM code-region
model and the RV64 byte-region model. -/

/-- Pack 8 bytes (little-endian) into a 64-bit word.
    Byte 0 at bits [0,8), byte 1 at bits [8,16), ..., byte 7 at bits [56,64). -/
def packDword (f : Fin 8 → BitVec 8) : Word :=
  (f 0).zeroExtend 64 |||
  ((f 1).zeroExtend 64 <<< 8) |||
  ((f 2).zeroExtend 64 <<< 16) |||
  ((f 3).zeroExtend 64 <<< 24) |||
  ((f 4).zeroExtend 64 <<< 32) |||
  ((f 5).zeroExtend 64 <<< 40) |||
  ((f 6).zeroExtend 64 <<< 48) |||
  ((f 7).zeroExtend 64 <<< 56)

/-- Index into a byte list with zero-padding for out-of-range. -/
def getByteAt (bytes : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  if h : k < bytes.length then bytes[k] else 0

/-- Pack a list of bytes into a 64-bit word (little-endian).
    Uses the first 8 bytes; pads with zeros if fewer than 8 are provided. -/
def packBytes (bytes : List (BitVec 8)) : Word :=
  packDword (fun i => getByteAt bytes i.val)

private theorem epd_core (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (k : Fin 8) :
    let w := b0.zeroExtend 64 |||
       (b1.zeroExtend 64 <<< 8) |||
       (b2.zeroExtend 64 <<< 16) |||
       (b3.zeroExtend 64 <<< 24) |||
       (b4.zeroExtend 64 <<< 32) |||
       (b5.zeroExtend 64 <<< 40) |||
       (b6.zeroExtend 64 <<< 48) |||
       (b7.zeroExtend 64 <<< 56)
    (w >>> (k.val * 8)).truncate 8 =
    (match k with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
                  | 4 => b4 | 5 => b5 | 6 => b6 | 7 => b7) := by
  fin_cases k <;> simp only [] <;>
  apply BitVec.eq_of_getLsbD_eq <;>
  intro i hi <;>
  interval_cases i <;>
  simp

theorem extractByte_packDword {f : Fin 8 → BitVec 8} {i : Fin 8} :
    extractByte (packDword f) i.val = f i := by
  show (packDword f >>> (i.val * 8)).truncate 8 = f i
  unfold packDword
  have := epd_core (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) i
  simp only [] at this
  convert this using 1
  fin_cases i <;> rfl

theorem extractByte_packBytes (bytes : List (BitVec 8)) (k : Nat)
    (hk : k < 8) (hlen : k < bytes.length) :
    extractByte (packBytes bytes) k = bytes[k] := by
  conv_lhs => rw [show k = (⟨k, hk⟩ : Fin 8).val from rfl]
  rw [packBytes, extractByte_packDword]
  simp [getByteAt, hlen]

/-! ## Compatibility wrappers -/
end EvmAsm.Rv64
