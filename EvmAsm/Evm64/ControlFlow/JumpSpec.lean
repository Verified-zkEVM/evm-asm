/-
  EvmAsm.Evm64.ControlFlow.JumpSpec

  Stack-level cpsTripleWithin specification for the EVM `JUMP` opcode
  (0x56; see `evm_jump` in `EvmAsm/Evm64/ControlFlow/Program.lean`).

  JUMP pops a 256-bit destination `dest` and validates it. The destination is
  *valid* iff its upper three limbs are zero and its low limb is strictly below
  the running-bytecode length `codeSize`. On the valid path the body sets
  `x10 := codeBaseReg + dest.low64` and loads the target code byte
  `code[dest.low64]` into `validityReg` for the handler tail's JUMPDEST check.
  On any invalid path (nonzero upper limb, or `dest.low64 ≥ codeSize`) the body
  writes the non-`0x5b` sentinel `0` into `validityReg` and leaves `x10`
  untouched; the handler tail routes such a value to `.exit_invalid`.

  The body reads but never writes the stack; it advances the EVM stack pointer
  `x12` by 32 (a genuine pop). The code region is modeled as
  `bytesRegion codeBase codeBytes`; on the valid path the target dword is split
  out of the region (`bytesRegion_dword_at`) and the byte read via the generic
  `LBU` spec, then re-assembled.

  Layout:
  - Three per-path core lemmas at the raw memory-cell level
    (`evm_jump_invalid_upper_spec_within` — BNE on the OR of the upper limbs,
    `evm_jump_invalid_bounds_spec_within` — BGEU on `dest.low ≥ codeSize`,
    `evm_jump_valid_spec_within` — the ADD/LBU/JAL valid path, reading a plain
    dword cell). Per-path step bounds: 9 / 11 / 13.
  - The public witness `evm_jump_stack_spec_within`: a single merged triple
    whose path-dependent part (`validityReg`, `x10`) sits inside an
    if-then-else keyed on the validity predicate; the clobbered temp `tmpReg`
    is shed to `regOwn`, and `bytesRegion` is framed (split on the valid path).
-/

import EvmAsm.Evm64.ControlFlow.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace ControlFlow

open EvmAsm.Rv64

/-- The `evm_jump` program placed in RV64 code memory at `base`. -/
abbrev evm_jump_code (codeBaseReg envBaseReg destReg tmpReg validityReg : Reg)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_jump codeBaseReg envBaseReg destReg tmpReg validityReg)

/-- The OR-reduction of three 64-bit limbs is zero iff each limb is zero. -/
private theorem or3_eq_zero_iff (a b c : Word) :
    ((a ||| b) ||| c) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    obtain ⟨hab, hc⟩ := BitVec.or_eq_zero_iff.mp h
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hab
    exact ⟨ha, hb, hc⟩
  · rintro ⟨ha, hb, hc⟩
    exact BitVec.or_eq_zero_iff.mpr ⟨BitVec.or_eq_zero_iff.mpr ⟨ha, hb⟩, hc⟩

-- ============================================================================
-- Per-path core lemmas (raw memory cells)
--
-- `tmpReg` and `x10` lead the footprint so the merge can shed them to
-- `regOwn`. The invalid cores never touch the code region, so it is framed at
-- the merge; the valid core reads a single dword cell (the merge splits it out
-- of `bytesRegion`). All cores carry the four stack-top limb cells and the
-- `codeSize` cell.
-- ============================================================================

/-- Invalid path via the BNE guard: the OR of the upper three destination limbs
    is nonzero, so `BNE` jumps to the sentinel which writes `0` to `validityReg`.
    `x10` is untouched; `tmpReg` ends at limb 3. 9 steps. -/
theorem evm_jump_invalid_upper_spec_within
    (codeBaseReg envBaseReg destReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (htmp : tmpReg ≠ .x0) (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld tmpOld valOld : Word)
    (i0 i1 i2 i3 codeSize : Word)
    (hor : ((i1 ||| i2) ||| i3) ≠ 0) :
    let code := evm_jump_code codeBaseReg envBaseReg destReg tmpReg validityReg base
    cpsTripleWithin 9 base (base + 56) code
      ((tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) ** (destReg ↦ᵣ destOld) **
       (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize))
      ((tmpReg ↦ᵣ i3) ** (.x10 ↦ᵣ x10old) ** (destReg ↦ᵣ i0) **
       (validityReg ↦ᵣ (0 : Word)) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize)) := by
  have hld0 := ld_spec_gen_within destReg .x12 nsp destOld i0 0 base hdest
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  have hld1 := ld_spec_gen_within validityReg .x12 nsp valOld i1 8 (base + 4) hval
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hor1 := or_spec_gen_rd_eq_rs1_within validityReg tmpReg i1 i2 (base + 12) hval
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hor2 := or_spec_gen_rd_eq_rs1_within validityReg tmpReg (i1 ||| i2) i3 (base + 20) hval
  have haddi := addi_spec_gen_same_within .x12 nsp (32 : BitVec 12) (base + 24) (by nofun)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show (nsp + (32 : Word)) = nsp + 32 from by bv_omega] at haddi
  have hbne_raw := bne_spec_gen_within validityReg .x0 (BitVec.ofNat 13 24)
    ((i1 ||| i2) ||| i3) (0 : Word) (base + 28)
  rw [show signExtend13 (BitVec.ofNat 13 24) = BitVec.ofNat 64 24 from by decide,
      show (base + 28 : Word) + BitVec.ofNat 64 24 = base + 52 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hor ((sepConj_pure_right _).mp h_rest).2)
  have hsent := addi_x0_spec_gen_within validityReg ((i1 ||| i2) ||| i3)
    (BitVec.ofNat 12 0) (base + 52) hval
  rw [show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) from by decide] at hsent
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 haddi hbne hsent

/-- Invalid path via the BGEU guard: the upper limbs OR to zero (canonical
    destination) but `dest.low ≥ codeSize`, so `BGEU` jumps to the sentinel.
    `x10` untouched; `tmpReg` ends at `codeSize`. 11 steps. -/
theorem evm_jump_invalid_bounds_spec_within
    (codeBaseReg envBaseReg destReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (htmp : tmpReg ≠ .x0) (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld tmpOld valOld : Word)
    (i0 i1 i2 i3 codeSize : Word)
    (hor : ((i1 ||| i2) ||| i3) = 0)
    (hbounds : ¬ BitVec.ult i0 codeSize) :
    let code := evm_jump_code codeBaseReg envBaseReg destReg tmpReg validityReg base
    cpsTripleWithin 11 base (base + 56) code
      ((tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) ** (destReg ↦ᵣ destOld) **
       (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize))
      ((tmpReg ↦ᵣ codeSize) ** (.x10 ↦ᵣ x10old) ** (destReg ↦ᵣ i0) **
       (validityReg ↦ᵣ (0 : Word)) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize)) := by
  have hld0 := ld_spec_gen_within destReg .x12 nsp destOld i0 0 base hdest
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  have hld1 := ld_spec_gen_within validityReg .x12 nsp valOld i1 8 (base + 4) hval
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hor1 := or_spec_gen_rd_eq_rs1_within validityReg tmpReg i1 i2 (base + 12) hval
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hor2 := or_spec_gen_rd_eq_rs1_within validityReg tmpReg (i1 ||| i2) i3 (base + 20) hval
  have haddi := addi_spec_gen_same_within .x12 nsp (32 : BitVec 12) (base + 24) (by nofun)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show (nsp + (32 : Word)) = nsp + 32 from by bv_omega] at haddi
  have hbne_raw := bne_spec_gen_within validityReg .x0 (BitVec.ofNat 13 24)
    ((i1 ||| i2) ||| i3) (0 : Word) (base + 28)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_ntakenStripPure2 hbne_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hor)
  have hldcs := ld_spec_gen_within tmpReg envBaseReg envAddr i3 codeSize
    (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff) (base + 32) htmp
  rw [show signExtend12 (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff)
        = BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff from
        signExtend12_ofNat_small (by decide)] at hldcs
  have hbgeu_raw := bgeu_spec_gen_within destReg tmpReg (BitVec.ofNat 13 16) i0 codeSize (base + 36)
  rw [show signExtend13 (BitVec.ofNat 13 16) = BitVec.ofNat 64 16 from by decide,
      show (base + 36 : Word) + BitVec.ofNat 64 16 = base + 52 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_takenStripPure2 hbgeu_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hbounds ((sepConj_pure_right _).mp h_rest).2)
  have hsent := addi_x0_spec_gen_within validityReg ((i1 ||| i2) ||| i3)
    (BitVec.ofNat 12 0) (base + 52) hval
  rw [show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) from by decide] at hsent
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 haddi hbne hldcs hbgeu hsent

/-- Valid path: upper limbs OR to zero and `dest.low <u codeSize`. Sets
    `x10 := codeBase + i0` and loads the code byte from the dword cell
    `dwordAddr ↦ₘ wordVal` (`dwordAddr = alignToDword (codeBase + i0)`), then
    JAL skips the sentinel. `tmpReg` ends at `codeSize`. 13 steps. -/
theorem evm_jump_valid_spec_within
    (codeBaseReg envBaseReg destReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (htmp : tmpReg ≠ .x0) (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld tmpOld valOld : Word)
    (i0 i1 i2 i3 codeSize dwordAddr wordVal : Word)
    (hor : ((i1 ||| i2) ||| i3) = 0)
    (hlt : BitVec.ult i0 codeSize)
    (halign_lbu : alignToDword (codeBase + i0) = dwordAddr)
    (hvalid_lbu : isValidByteAccess (codeBase + i0) = true) :
    let code := evm_jump_code codeBaseReg envBaseReg destReg tmpReg validityReg base
    cpsTripleWithin 13 base (base + 56) code
      ((tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) ** (destReg ↦ᵣ destOld) **
       (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       (dwordAddr ↦ₘ wordVal))
      ((tmpReg ↦ᵣ codeSize) ** (.x10 ↦ᵣ (codeBase + i0)) ** (destReg ↦ᵣ i0) **
       (validityReg ↦ᵣ ((extractByte wordVal (byteOffset (codeBase + i0))).zeroExtend 64)) **
       (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       (dwordAddr ↦ₘ wordVal)) := by
  have hld0 := ld_spec_gen_within destReg .x12 nsp destOld i0 0 base hdest
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  have hld1 := ld_spec_gen_within validityReg .x12 nsp valOld i1 8 (base + 4) hval
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hor1 := or_spec_gen_rd_eq_rs1_within validityReg tmpReg i1 i2 (base + 12) hval
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hor2 := or_spec_gen_rd_eq_rs1_within validityReg tmpReg (i1 ||| i2) i3 (base + 20) hval
  have haddi := addi_spec_gen_same_within .x12 nsp (32 : BitVec 12) (base + 24) (by nofun)
  rw [show signExtend12 (32 : BitVec 12) = (32 : Word) from by decide,
      show (nsp + (32 : Word)) = nsp + 32 from by bv_omega] at haddi
  have hbne_raw := bne_spec_gen_within validityReg .x0 (BitVec.ofNat 13 24)
    ((i1 ||| i2) ||| i3) (0 : Word) (base + 28)
  rw [show (base + 28 : Word) + 4 = base + 32 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_ntakenStripPure2 hbne_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hor)
  have hldcs := ld_spec_gen_within tmpReg envBaseReg envAddr i3 codeSize
    (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff) (base + 32) htmp
  rw [show signExtend12 (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff)
        = BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff from
        signExtend12_ofNat_small (by decide)] at hldcs
  have hbgeu_raw := bgeu_spec_gen_within destReg tmpReg (BitVec.ofNat 13 16) i0 codeSize (base + 36)
  rw [show (base + 36 : Word) + 4 = base + 40 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_ntakenStripPure2 hbgeu_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlt)
  have hadd := add_spec_gen_within .x10 codeBaseReg destReg codeBase i0 x10old
    (base + 40) (by nofun)
  -- +44 LBU validityReg x10 0 : read the code byte from the dword cell.
  have hz : ((codeBase + i0) + signExtend12 (0 : BitVec 12)) = codeBase + i0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have halign' : alignToDword ((codeBase + i0) + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [hz]; exact halign_lbu
  have hvalid' : isValidByteAccess ((codeBase + i0) + signExtend12 (0 : BitVec 12)) = true := by
    rw [hz]; exact hvalid_lbu
  have hlbu := generic_lbu_spec_within validityReg .x10 (codeBase + i0)
    ((i1 ||| i2) ||| i3) (0 : BitVec 12) (base + 44) dwordAddr wordVal hval halign' hvalid'
  rw [hz] at hlbu
  -- +48 JAL x0 +8 → base + 56
  have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 8) (base + 48)
  rw [show signExtend21 (BitVec.ofNat 21 8) = BitVec.ofNat 64 8 from by decide,
      show (base + 48 : Word) + BitVec.ofNat 64 8 = base + 56 from by bv_omega] at hjal
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 haddi hbne hldcs hbgeu hadd hlbu hjal

-- ============================================================================
-- Public stack-level witness
-- ============================================================================

/-- Weaken two leading concrete register atoms to `regOwn`. -/
private theorem sepConj_own2 {r1 r2 : Reg} {v1 v2 : Word} {Q : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h → (regOwn r1 ** regOwn r2 ** Q) h :=
  fun h hp =>
    sepConj_mono_left (regIs_to_regOwn r1 v1) h
      (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn r2 v2)) h hp)

/-- **JUMP stack spec** (the `.proven` witness): pops the destination `dest`,
    advancing the EVM stack pointer by 32 (the stack memory is read, not
    written). On the valid path (`dest`'s upper three limbs zero and
    `dest.low <u codeSize`) `x10 := codeBase + dest.low` and `validityReg`
    receives the target code byte `code[dest.low]`; on any invalid path
    `validityReg := 0` and `x10` is left owned but unconstrained. The
    path-dependent registers sit inside the if-then-else; the clobbered
    `tmpReg` is shed to `regOwn`. Hypotheses: register shape (`≠ x0`), the
    dispatcher fact `codeSize.toNat ≤ codeBytes.length`, and the code-region
    shape facts (dword-aligned base, no address overflow, valid byte access)
    used by the single code-byte read on the valid path. -/
theorem evm_jump_stack_spec_within
    (codeBaseReg envBaseReg destReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (htmp : tmpReg ≠ .x0) (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld tmpOld valOld : Word)
    (dest : EvmWord) (codeSize : Word) (codeBytes : List (BitVec 8))
    (rest : List EvmWord)
    (hcount : codeSize.toNat ≤ codeBytes.length)
    (halign : codeBase.toNat % 8 = 0)
    (hcodeOver : codeBase.toNat + codeBytes.length ≤ 2 ^ 64)
    (hcodeValid : ∀ j : Nat, j < codeBytes.length →
      isValidByteAccess (codeBase + BitVec.ofNat 64 j) = true) :
    let code := evm_jump_code codeBaseReg envBaseReg destReg tmpReg validityReg base
    cpsTripleWithin 13 base (base + 56) code
      ((codeBaseReg ↦ᵣ codeBase) ** (envBaseReg ↦ᵣ envAddr) **
       (destReg ↦ᵣ destOld) ** (tmpReg ↦ᵣ tmpOld) ** (validityReg ↦ᵣ valOld) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10old) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (dest :: rest) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       bytesRegion codeBase codeBytes)
      ((codeBaseReg ↦ᵣ codeBase) ** (envBaseReg ↦ᵣ envAddr) **
       (destReg ↦ᵣ dest.getLimbN 0) ** regOwn tmpReg **
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 32)) **
       evmStackIs nsp (dest :: rest) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       bytesRegion codeBase codeBytes **
       (if dest.getLimbN 1 = 0 ∧ dest.getLimbN 2 = 0 ∧ dest.getLimbN 3 = 0 ∧
            BitVec.ult (dest.getLimbN 0) codeSize
        then (validityReg ↦ᵣ ((codeBytes.getD (dest.getLimbN 0).toNat 0).zeroExtend 64)) **
             (.x10 ↦ᵣ (codeBase + dest.getLimbN 0))
        else (validityReg ↦ᵣ (0 : Word)) ** regOwn .x10)) := by
  intro code
  have hword : evmWordIs nsp dest
      = ((nsp ↦ₘ dest.getLimbN 0) ** ((nsp + 8) ↦ₘ dest.getLimbN 1) **
         ((nsp + 16) ↦ₘ dest.getLimbN 2) ** ((nsp + 24) ↦ₘ dest.getLimbN 3)) := rfl
  by_cases hc : dest.getLimbN 1 = 0 ∧ dest.getLimbN 2 = 0 ∧ dest.getLimbN 3 = 0 ∧
      BitVec.ult (dest.getLimbN 0) codeSize
  · -- Valid path.
    rw [if_pos hc]
    obtain ⟨hz1, hz2, hz3, hlt⟩ := hc
    have hor : ((dest.getLimbN 1 ||| dest.getLimbN 2) ||| dest.getLimbN 3) = 0 :=
      (or3_eq_zero_iff _ _ _).mpr ⟨hz1, hz2, hz3⟩
    have hltn : (dest.getLimbN 0).toNat < codeSize.toNat := by
      have h := hlt; rw [BitVec.ult_iff_lt, BitVec.lt_def] at h; exact h
    have hi : (dest.getLimbN 0).toNat < codeBytes.length := by omega
    have hover : codeBase.toNat + (dest.getLimbN 0).toNat < 2 ^ 64 := by omega
    have hdw : 8 * ((dest.getLimbN 0).toNat / 8) < codeBytes.length := by omega
    obtain ⟨front, restR, hf, hr, hsplit⟩ :=
      bytesRegion_dword_at codeBase codeBytes ((dest.getLimbN 0).toNat / 8) hdw
    set dwAddr := codeBase + BitVec.ofNat 64 (8 * ((dest.getLimbN 0).toNat / 8)) with hdwAddr
    set wVal := packBytes ((codeBytes.drop (8 * ((dest.getLimbN 0).toNat / 8))).take 8) with hwVal
    have hcodeAddr : codeBase + dest.getLimbN 0
        = codeBase + BitVec.ofNat 64 (dest.getLimbN 0).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have halign_lbu : alignToDword (codeBase + dest.getLimbN 0) = dwAddr := by
      rw [hcodeAddr, hdwAddr]; exact alignToDword_add_ofNat_of_aligned halign hover
    have hvalid_lbu : isValidByteAccess (codeBase + dest.getLimbN 0) = true := by
      rw [hcodeAddr]; exact hcodeValid _ hi
    have hbo : byteOffset (codeBase + dest.getLimbN 0) = (dest.getLimbN 0).toNat % 8 := by
      rw [hcodeAddr]; exact byteOffset_add_ofNat_of_aligned halign hover
    have hbyte : extractByte wVal (byteOffset (codeBase + dest.getLimbN 0))
        = codeBytes[(dest.getLimbN 0).toNat]'hi := by
      rw [hbo, hwVal,
          extractByte_packBytes _ _ (by omega)
            (by rw [List.length_take, List.length_drop]; omega),
          List.getElem_take, List.getElem_drop]
      congr 1; omega
    have hgetD : (codeBytes.getD (dest.getLimbN 0).toNat (0 : BitVec 8)).zeroExtend 64
        = (extractByte wVal (byteOffset (codeBase + dest.getLimbN 0))).zeroExtend 64 := by
      rw [hbyte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
      (cpsTripleWithin_frameR (evmStackIs (nsp + 32) rest ** front ** restR)
        (pcFree_sepConj pcFree_evmStackIs (pcFree_sepConj hf hr))
        (evm_jump_valid_spec_within codeBaseReg envBaseReg destReg tmpReg validityReg
          hdest htmp hval nsp base envAddr codeBase x10old destOld tmpOld valOld
          (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
          codeSize dwAddr wVal hor hlt halign_lbu hvalid_lbu))
    · rw [evmStackIs_cons, hword, hsplit] at hp
      xperm_hyp hp
    · rw [evmStackIs_cons, hword, hsplit, hgetD]
      have hq' := sepConj_mono_left
        (sepConj_mono_left (regIs_to_regOwn tmpReg codeSize)) h hq
      xperm_hyp hq'
  · -- Invalid paths.
    rw [if_neg hc]
    by_cases hor : ((dest.getLimbN 1 ||| dest.getLimbN 2) ||| dest.getLimbN 3) = 0
    · -- Upper limbs canonical but out of bounds → BGEU sentinel.
      obtain ⟨hz1, hz2, hz3⟩ := (or3_eq_zero_iff _ _ _).mp hor
      have hbounds : ¬ BitVec.ult (dest.getLimbN 0) codeSize :=
        fun hl => hc ⟨hz1, hz2, hz3, hl⟩
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
        (cpsTripleWithin_frameR (evmStackIs (nsp + 32) rest ** bytesRegion codeBase codeBytes)
          (pcFree_sepConj pcFree_evmStackIs (bytesRegion_pcFree _ _))
          (cpsTripleWithin_mono_nSteps (by omega)
            (evm_jump_invalid_bounds_spec_within codeBaseReg envBaseReg destReg tmpReg validityReg
              hdest htmp hval nsp base envAddr codeBase x10old destOld tmpOld valOld
              (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
              codeSize hor hbounds)))
      · rw [evmStackIs_cons, hword] at hp
        xperm_hyp hp
      · rw [evmStackIs_cons, hword]
        have hq' := sepConj_mono_left (sepConj_own2 (r1 := tmpReg) (r2 := .x10)) h hq
        xperm_hyp hq'
    · -- Nonzero upper limb → BNE sentinel.
      refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
        (cpsTripleWithin_frameR (evmStackIs (nsp + 32) rest ** bytesRegion codeBase codeBytes)
          (pcFree_sepConj pcFree_evmStackIs (bytesRegion_pcFree _ _))
          (cpsTripleWithin_mono_nSteps (by omega)
            (evm_jump_invalid_upper_spec_within codeBaseReg envBaseReg destReg tmpReg validityReg
              hdest htmp hval nsp base envAddr codeBase x10old destOld tmpOld valOld
              (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
              codeSize hor)))
      · rw [evmStackIs_cons, hword] at hp
        xperm_hyp hp
      · rw [evmStackIs_cons, hword]
        have hq' := sepConj_mono_left (sepConj_own2 (r1 := tmpReg) (r2 := .x10)) h hq
        xperm_hyp hq'

end ControlFlow
end EvmAsm.Evm64
