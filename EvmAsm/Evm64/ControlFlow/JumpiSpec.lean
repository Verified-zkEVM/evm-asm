/-
  EvmAsm.Evm64.ControlFlow.JumpiSpec

  Stack-level cpsTripleWithin specification for the EVM `JUMPI` opcode
  (0x57; see `evm_jumpi` in `EvmAsm/Evm64/ControlFlow/Program.lean`).

  JUMPI pops `dest` (stack top) and `cond` (second) and advances the EVM stack
  pointer `x12` by 64 (two genuine pops; the stack memory is read, not written).
  There are three outcomes:

  - **Fall-through** (`cond == 0`, i.e. all four cond limbs zero): the `BEQ`
    guard is taken; `x10 := x10 + 1` (skip past the JUMPI opcode) and
    `validityReg := 0x5b` (the harmless sentinel the handler tail treats as a
    no-op). The destination is ignored.
  - **Valid taken jump** (`cond != 0`, `dest`'s upper three limbs zero, and
    `dest.low <u codeSize`): `x10 := codeBase + dest.low` and the target code
    byte `code[dest.low]` is loaded into `validityReg` for the handler tail's
    JUMPDEST check.
  - **Invalid taken jump** (`cond != 0` but a nonzero upper `dest` limb or
    `dest.low ≥ codeSize`): `validityReg := 0` (a non-`0x5b` sentinel the
    handler tail routes to `.exit_invalid`) and `x10` is left owned but
    unconstrained.

  This is the direct branchy sibling of `JumpSpec.lean`: it reuses the same
  raw-cell per-path core / `cpsBranchWithin` merge recipe, keeping the compound
  `bytesRegion codeBase codeBytes` out of every `runBlock` footprint. The
  invalid / fall-through cores frame it whole; the valid taken core reads the
  target dword out of a plain cell (`bytesRegion_dword_at`) and the merge
  re-assembles the region.

  Layout:
  - Four per-path core lemmas at the raw memory-cell level
    (`evm_jumpi_fallthrough_spec_within` — BEQ taken, 18 steps;
    `evm_jumpi_valid_spec_within` — the ADD/LBU/JAL valid path, 21 steps;
    `evm_jumpi_invalid_upper_spec_within` — BNE on the OR of the upper dest
    limbs, 17 steps; `evm_jumpi_invalid_bounds_spec_within` — BGEU on
    `dest.low ≥ codeSize`, 19 steps).
  - The public witness `evm_jumpi_stack_spec_within`: a single merged triple
    (21 steps) whose path-dependent part (`validityReg`, `x10`) sits inside a
    nested if-then-else; the clobbered temps `condReg` / `tmpReg` are shed to
    `regOwn`, and `bytesRegion` is framed (split on the valid path).
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

/-- The `evm_jumpi` program placed in RV64 code memory at `base`. -/
abbrev evm_jumpi_code (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg)
    (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_jumpi codeBaseReg envBaseReg destReg condReg tmpReg validityReg)

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

/-- The OR-reduction of four 64-bit limbs is zero iff each limb is zero. -/
private theorem or4_eq_zero_iff (a b c d : Word) :
    (((a ||| b) ||| c) ||| d) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    obtain ⟨habc, hd⟩ := BitVec.or_eq_zero_iff.mp h
    obtain ⟨ha, hb, hc⟩ := (or3_eq_zero_iff _ _ _).mp habc
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact BitVec.or_eq_zero_iff.mpr ⟨(or3_eq_zero_iff _ _ _).mpr ⟨ha, hb, hc⟩, hd⟩

-- ============================================================================
-- Per-path core lemmas (raw memory cells)
--
-- `condReg`, `tmpReg` and `x10` lead the footprint so the merge can shed them
-- to `regOwn`. The invalid / fall-through cores never touch the code region,
-- so it is framed at the merge; the valid core reads a single dword cell (the
-- merge splits it out of `bytesRegion`). All cores carry the four `dest` limb
-- cells (nsp..nsp+24), the four `cond` limb cells (nsp+32..nsp+56), and the
-- `codeSize` cell.
--
-- The shared 14-instruction prefix (loads + OR-reductions + `x12 += 64`) is
-- inlined in each core; the register state after it is
--   destReg = i0, validityReg = (i1|i2)|i3, condReg = ((c0|c1)|c2)|c3,
--   tmpReg = c3, x12 = nsp+64.
-- ============================================================================

/-- Fall-through path (`cond == 0`): the `BEQ condReg x0` guard is taken, so
    the program jumps to `ADDI x10 x10 1` / `ADDI validityReg x0 0x5b` /
    `JAL +8`. `x10 := x10old + 1`, `validityReg := 0x5b`, `tmpReg` ends at `c3`.
    18 steps. -/
theorem evm_jumpi_fallthrough_spec_within
    (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (hcondR : condReg ≠ .x0) (htmp : tmpReg ≠ .x0)
    (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld condOld tmpOld valOld : Word)
    (i0 i1 i2 i3 c0 c1 c2 c3 codeSize : Word)
    (hcond : (((c0 ||| c1) ||| c2) ||| c3) = 0) :
    let code := evm_jumpi_code codeBaseReg envBaseReg destReg condReg tmpReg validityReg base
    cpsTripleWithin 18 base (base + 100) code
      ((condReg ↦ᵣ condOld) ** (tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) **
       (destReg ↦ᵣ destOld) ** (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize))
      ((condReg ↦ᵣ (((c0 ||| c1) ||| c2) ||| c3)) ** (tmpReg ↦ᵣ c3) ** (.x10 ↦ᵣ (x10old + 1)) **
       (destReg ↦ᵣ i0) ** (validityReg ↦ᵣ (0x5b : Word)) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 64)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
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
  have hc0' := ld_spec_gen_within condReg .x12 nsp condOld c0 32 (base + 24) hcondR
  rw [show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32 from by decide,
      show (nsp + BitVec.ofNat 64 32 : Word) = nsp + 32 from by bv_omega] at hc0'
  have hc1' := ld_spec_gen_within tmpReg .x12 nsp i3 c1 40 (base + 28) htmp
  rw [show signExtend12 (40 : BitVec 12) = BitVec.ofNat 64 40 from by decide,
      show (nsp + BitVec.ofNat 64 40 : Word) = (nsp + 32) + 8 from by bv_omega] at hc1'
  have horc1 := or_spec_gen_rd_eq_rs1_within condReg tmpReg c0 c1 (base + 32) hcondR
  have hc2' := ld_spec_gen_within tmpReg .x12 nsp c1 c2 48 (base + 36) htmp
  rw [show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 48 from by decide,
      show (nsp + BitVec.ofNat 64 48 : Word) = (nsp + 32) + 16 from by bv_omega] at hc2'
  have horc2 := or_spec_gen_rd_eq_rs1_within condReg tmpReg (c0 ||| c1) c2 (base + 40) hcondR
  have hc3' := ld_spec_gen_within tmpReg .x12 nsp c2 c3 56 (base + 44) htmp
  rw [show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 from by decide,
      show (nsp + BitVec.ofNat 64 56 : Word) = (nsp + 32) + 24 from by bv_omega] at hc3'
  have horc3 := or_spec_gen_rd_eq_rs1_within condReg tmpReg ((c0 ||| c1) ||| c2) c3 (base + 48) hcondR
  have haddi := addi_spec_gen_same_within .x12 nsp (64 : BitVec 12) (base + 52) (by nofun)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (nsp + (64 : Word)) = nsp + 64 from by bv_omega] at haddi
  have hbeq_raw := beq_spec_gen_within condReg .x0 (BitVec.ofNat 13 28)
    (((c0 ||| c1) ||| c2) ||| c3) (0 : Word) (base + 56)
  rw [show signExtend13 (BitVec.ofNat 13 28) = BitVec.ofNat 64 28 from by decide,
      show (base + 56 : Word) + BitVec.ofNat 64 28 = base + 84 from by bv_omega] at hbeq_raw
  have hbeq := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _).mp h_rest).2 hcond)
  have haddx10 := addi_spec_gen_same_within .x10 x10old (1 : BitVec 12) (base + 84) (by nofun)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at haddx10
  have hsent5b := addi_x0_spec_gen_within validityReg ((i1 ||| i2) ||| i3)
    (BitVec.ofNat 12 0x5b) (base + 88) hval
  rw [show signExtend12 (BitVec.ofNat 12 0x5b) = (0x5b : Word) from by decide] at hsent5b
  have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 8) (base + 92)
  rw [show signExtend21 (BitVec.ofNat 21 8) = BitVec.ofNat 64 8 from by decide,
      show (base + 92 : Word) + BitVec.ofNat 64 8 = base + 100 from by bv_omega] at hjal
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 hc0' hc1' horc1 hc2' horc2 hc3' horc3 haddi
    hbeq haddx10 hsent5b hjal

/-- Valid taken path (`cond != 0`, upper limbs OR to zero, `dest.low <u
    codeSize`): sets `x10 := codeBase + i0` and loads the code byte from the
    dword cell `dwordAddr ↦ₘ wordVal`, then JAL skips the fall-through /
    sentinel. `tmpReg` ends at `codeSize`. 21 steps. -/
theorem evm_jumpi_valid_spec_within
    (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (hcondR : condReg ≠ .x0) (htmp : tmpReg ≠ .x0)
    (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld condOld tmpOld valOld : Word)
    (i0 i1 i2 i3 c0 c1 c2 c3 codeSize dwordAddr wordVal : Word)
    (hcond_ne : (((c0 ||| c1) ||| c2) ||| c3) ≠ 0)
    (hor : ((i1 ||| i2) ||| i3) = 0)
    (hlt : BitVec.ult i0 codeSize)
    (halign_lbu : alignToDword (codeBase + i0) = dwordAddr)
    (hvalid_lbu : isValidByteAccess (codeBase + i0) = true) :
    let code := evm_jumpi_code codeBaseReg envBaseReg destReg condReg tmpReg validityReg base
    cpsTripleWithin 21 base (base + 100) code
      ((condReg ↦ᵣ condOld) ** (tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) **
       (destReg ↦ᵣ destOld) ** (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       (dwordAddr ↦ₘ wordVal))
      ((condReg ↦ᵣ (((c0 ||| c1) ||| c2) ||| c3)) ** (tmpReg ↦ᵣ codeSize) **
       (.x10 ↦ᵣ (codeBase + i0)) **
       (destReg ↦ᵣ i0) **
       (validityReg ↦ᵣ ((extractByte wordVal (byteOffset (codeBase + i0))).zeroExtend 64)) **
       (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 64)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
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
  have hc0' := ld_spec_gen_within condReg .x12 nsp condOld c0 32 (base + 24) hcondR
  rw [show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32 from by decide,
      show (nsp + BitVec.ofNat 64 32 : Word) = nsp + 32 from by bv_omega] at hc0'
  have hc1' := ld_spec_gen_within tmpReg .x12 nsp i3 c1 40 (base + 28) htmp
  rw [show signExtend12 (40 : BitVec 12) = BitVec.ofNat 64 40 from by decide,
      show (nsp + BitVec.ofNat 64 40 : Word) = (nsp + 32) + 8 from by bv_omega] at hc1'
  have horc1 := or_spec_gen_rd_eq_rs1_within condReg tmpReg c0 c1 (base + 32) hcondR
  have hc2' := ld_spec_gen_within tmpReg .x12 nsp c1 c2 48 (base + 36) htmp
  rw [show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 48 from by decide,
      show (nsp + BitVec.ofNat 64 48 : Word) = (nsp + 32) + 16 from by bv_omega] at hc2'
  have horc2 := or_spec_gen_rd_eq_rs1_within condReg tmpReg (c0 ||| c1) c2 (base + 40) hcondR
  have hc3' := ld_spec_gen_within tmpReg .x12 nsp c2 c3 56 (base + 44) htmp
  rw [show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 from by decide,
      show (nsp + BitVec.ofNat 64 56 : Word) = (nsp + 32) + 24 from by bv_omega] at hc3'
  have horc3 := or_spec_gen_rd_eq_rs1_within condReg tmpReg ((c0 ||| c1) ||| c2) c3 (base + 48) hcondR
  have haddi := addi_spec_gen_same_within .x12 nsp (64 : BitVec 12) (base + 52) (by nofun)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (nsp + (64 : Word)) = nsp + 64 from by bv_omega] at haddi
  have hbeq_raw := beq_spec_gen_within condReg .x0 (BitVec.ofNat 13 28)
    (((c0 ||| c1) ||| c2) ||| c3) (0 : Word) (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hbeq_raw
  have hbeq := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact hcond_ne ((sepConj_pure_right _).mp h_rest).2)
  have hbne_raw := bne_spec_gen_within validityReg .x0 (BitVec.ofNat 13 36)
    ((i1 ||| i2) ||| i3) (0 : Word) (base + 60)
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_ntakenStripPure2 hbne_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hor)
  have hldcs := ld_spec_gen_within tmpReg envBaseReg envAddr c3 codeSize
    (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff) (base + 64) htmp
  rw [show signExtend12 (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff)
        = BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff from
        signExtend12_ofNat_small (by decide)] at hldcs
  have hbgeu_raw := bgeu_spec_gen_within destReg tmpReg (BitVec.ofNat 13 28) i0 codeSize (base + 68)
  rw [show (base + 68 : Word) + 4 = base + 72 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_ntakenStripPure2 hbgeu_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlt)
  have hadd := add_spec_gen_within .x10 codeBaseReg destReg codeBase i0 x10old
    (base + 72) (by nofun)
  have hz : ((codeBase + i0) + signExtend12 (0 : BitVec 12)) = codeBase + i0 := by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
  have halign' : alignToDword ((codeBase + i0) + signExtend12 (0 : BitVec 12)) = dwordAddr := by
    rw [hz]; exact halign_lbu
  have hvalid' : isValidByteAccess ((codeBase + i0) + signExtend12 (0 : BitVec 12)) = true := by
    rw [hz]; exact hvalid_lbu
  have hlbu := generic_lbu_spec_within validityReg .x10 (codeBase + i0)
    ((i1 ||| i2) ||| i3) (0 : BitVec 12) (base + 76) dwordAddr wordVal hval halign' hvalid'
  rw [hz] at hlbu
  have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 20) (base + 80)
  rw [show signExtend21 (BitVec.ofNat 21 20) = BitVec.ofNat 64 20 from by decide,
      show (base + 80 : Word) + BitVec.ofNat 64 20 = base + 100 from by bv_omega] at hjal
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 hc0' hc1' horc1 hc2' horc2 hc3' horc3 haddi
    hbeq hbne hldcs hbgeu hadd hlbu hjal

/-- Invalid taken path via the BNE guard (`cond != 0`, some upper `dest` limb
    nonzero): the `BNE validityReg x0` jumps to `ADDI validityReg x0 0`.
    `x10` untouched; `tmpReg` ends at `c3`. 17 steps. -/
theorem evm_jumpi_invalid_upper_spec_within
    (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (hcondR : condReg ≠ .x0) (htmp : tmpReg ≠ .x0)
    (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld condOld tmpOld valOld : Word)
    (i0 i1 i2 i3 c0 c1 c2 c3 codeSize : Word)
    (hcond_ne : (((c0 ||| c1) ||| c2) ||| c3) ≠ 0)
    (hor : ((i1 ||| i2) ||| i3) ≠ 0) :
    let code := evm_jumpi_code codeBaseReg envBaseReg destReg condReg tmpReg validityReg base
    cpsTripleWithin 17 base (base + 100) code
      ((condReg ↦ᵣ condOld) ** (tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) **
       (destReg ↦ᵣ destOld) ** (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize))
      ((condReg ↦ᵣ (((c0 ||| c1) ||| c2) ||| c3)) ** (tmpReg ↦ᵣ c3) ** (.x10 ↦ᵣ x10old) **
       (destReg ↦ᵣ i0) ** (validityReg ↦ᵣ (0 : Word)) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 64)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
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
  have hc0' := ld_spec_gen_within condReg .x12 nsp condOld c0 32 (base + 24) hcondR
  rw [show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32 from by decide,
      show (nsp + BitVec.ofNat 64 32 : Word) = nsp + 32 from by bv_omega] at hc0'
  have hc1' := ld_spec_gen_within tmpReg .x12 nsp i3 c1 40 (base + 28) htmp
  rw [show signExtend12 (40 : BitVec 12) = BitVec.ofNat 64 40 from by decide,
      show (nsp + BitVec.ofNat 64 40 : Word) = (nsp + 32) + 8 from by bv_omega] at hc1'
  have horc1 := or_spec_gen_rd_eq_rs1_within condReg tmpReg c0 c1 (base + 32) hcondR
  have hc2' := ld_spec_gen_within tmpReg .x12 nsp c1 c2 48 (base + 36) htmp
  rw [show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 48 from by decide,
      show (nsp + BitVec.ofNat 64 48 : Word) = (nsp + 32) + 16 from by bv_omega] at hc2'
  have horc2 := or_spec_gen_rd_eq_rs1_within condReg tmpReg (c0 ||| c1) c2 (base + 40) hcondR
  have hc3' := ld_spec_gen_within tmpReg .x12 nsp c2 c3 56 (base + 44) htmp
  rw [show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 from by decide,
      show (nsp + BitVec.ofNat 64 56 : Word) = (nsp + 32) + 24 from by bv_omega] at hc3'
  have horc3 := or_spec_gen_rd_eq_rs1_within condReg tmpReg ((c0 ||| c1) ||| c2) c3 (base + 48) hcondR
  have haddi := addi_spec_gen_same_within .x12 nsp (64 : BitVec 12) (base + 52) (by nofun)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (nsp + (64 : Word)) = nsp + 64 from by bv_omega] at haddi
  have hbeq_raw := beq_spec_gen_within condReg .x0 (BitVec.ofNat 13 28)
    (((c0 ||| c1) ||| c2) ||| c3) (0 : Word) (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hbeq_raw
  have hbeq := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact hcond_ne ((sepConj_pure_right _).mp h_rest).2)
  have hbne_raw := bne_spec_gen_within validityReg .x0 (BitVec.ofNat 13 36)
    ((i1 ||| i2) ||| i3) (0 : Word) (base + 60)
  rw [show signExtend13 (BitVec.ofNat 13 36) = BitVec.ofNat 64 36 from by decide,
      show (base + 60 : Word) + BitVec.ofNat 64 36 = base + 96 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hor ((sepConj_pure_right _).mp h_rest).2)
  have hsent := addi_x0_spec_gen_within validityReg ((i1 ||| i2) ||| i3)
    (BitVec.ofNat 12 0) (base + 96) hval
  rw [show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) from by decide] at hsent
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 hc0' hc1' horc1 hc2' horc2 hc3' horc3 haddi
    hbeq hbne hsent

/-- Invalid taken path via the BGEU guard (`cond != 0`, upper limbs OR to zero
    but `dest.low ≥ codeSize`): after the codeSize load, `BGEU` jumps to
    `ADDI validityReg x0 0`. `x10` untouched; `tmpReg` ends at `codeSize`.
    19 steps. -/
theorem evm_jumpi_invalid_bounds_spec_within
    (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (hcondR : condReg ≠ .x0) (htmp : tmpReg ≠ .x0)
    (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld condOld tmpOld valOld : Word)
    (i0 i1 i2 i3 c0 c1 c2 c3 codeSize : Word)
    (hcond_ne : (((c0 ||| c1) ||| c2) ||| c3) ≠ 0)
    (hor : ((i1 ||| i2) ||| i3) = 0)
    (hbounds : ¬ BitVec.ult i0 codeSize) :
    let code := evm_jumpi_code codeBaseReg envBaseReg destReg condReg tmpReg validityReg base
    cpsTripleWithin 19 base (base + 100) code
      ((condReg ↦ᵣ condOld) ** (tmpReg ↦ᵣ tmpOld) ** (.x10 ↦ᵣ x10old) **
       (destReg ↦ᵣ destOld) ** (validityReg ↦ᵣ valOld) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize))
      ((condReg ↦ᵣ (((c0 ||| c1) ||| c2) ||| c3)) ** (tmpReg ↦ᵣ codeSize) ** (.x10 ↦ᵣ x10old) **
       (destReg ↦ᵣ i0) ** (validityReg ↦ᵣ (0 : Word)) ** (codeBaseReg ↦ᵣ codeBase) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 64)) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) ** ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((nsp + 32) ↦ₘ c0) ** (((nsp + 32) + 8) ↦ₘ c1) ** (((nsp + 32) + 16) ↦ₘ c2) **
       (((nsp + 32) + 24) ↦ₘ c3) **
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
  have hc0' := ld_spec_gen_within condReg .x12 nsp condOld c0 32 (base + 24) hcondR
  rw [show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32 from by decide,
      show (nsp + BitVec.ofNat 64 32 : Word) = nsp + 32 from by bv_omega] at hc0'
  have hc1' := ld_spec_gen_within tmpReg .x12 nsp i3 c1 40 (base + 28) htmp
  rw [show signExtend12 (40 : BitVec 12) = BitVec.ofNat 64 40 from by decide,
      show (nsp + BitVec.ofNat 64 40 : Word) = (nsp + 32) + 8 from by bv_omega] at hc1'
  have horc1 := or_spec_gen_rd_eq_rs1_within condReg tmpReg c0 c1 (base + 32) hcondR
  have hc2' := ld_spec_gen_within tmpReg .x12 nsp c1 c2 48 (base + 36) htmp
  rw [show signExtend12 (48 : BitVec 12) = BitVec.ofNat 64 48 from by decide,
      show (nsp + BitVec.ofNat 64 48 : Word) = (nsp + 32) + 16 from by bv_omega] at hc2'
  have horc2 := or_spec_gen_rd_eq_rs1_within condReg tmpReg (c0 ||| c1) c2 (base + 40) hcondR
  have hc3' := ld_spec_gen_within tmpReg .x12 nsp c2 c3 56 (base + 44) htmp
  rw [show signExtend12 (56 : BitVec 12) = BitVec.ofNat 64 56 from by decide,
      show (nsp + BitVec.ofNat 64 56 : Word) = (nsp + 32) + 24 from by bv_omega] at hc3'
  have horc3 := or_spec_gen_rd_eq_rs1_within condReg tmpReg ((c0 ||| c1) ||| c2) c3 (base + 48) hcondR
  have haddi := addi_spec_gen_same_within .x12 nsp (64 : BitVec 12) (base + 52) (by nofun)
  rw [show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide,
      show (nsp + (64 : Word)) = nsp + 64 from by bv_omega] at haddi
  have hbeq_raw := beq_spec_gen_within condReg .x0 (BitVec.ofNat 13 28)
    (((c0 ||| c1) ||| c2) ||| c3) (0 : Word) (base + 56)
  rw [show (base + 56 : Word) + 4 = base + 60 from by bv_omega] at hbeq_raw
  have hbeq := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact hcond_ne ((sepConj_pure_right _).mp h_rest).2)
  have hbne_raw := bne_spec_gen_within validityReg .x0 (BitVec.ofNat 13 36)
    ((i1 ||| i2) ||| i3) (0 : Word) (base + 60)
  rw [show (base + 60 : Word) + 4 = base + 64 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_ntakenStripPure2 hbne_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hor)
  have hldcs := ld_spec_gen_within tmpReg envBaseReg envAddr c3 codeSize
    (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff) (base + 64) htmp
  rw [show signExtend12 (BitVec.ofNat 12 EvmAsm.Evm64.Code.codeSizeOff)
        = BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff from
        signExtend12_ofNat_small (by decide)] at hldcs
  have hbgeu_raw := bgeu_spec_gen_within destReg tmpReg (BitVec.ofNat 13 28) i0 codeSize (base + 68)
  rw [show signExtend13 (BitVec.ofNat 13 28) = BitVec.ofNat 64 28 from by decide,
      show (base + 68 : Word) + BitVec.ofNat 64 28 = base + 96 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_takenStripPure2 hbgeu_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hbounds ((sepConj_pure_right _).mp h_rest).2)
  have hsent := addi_x0_spec_gen_within validityReg ((i1 ||| i2) ||| i3)
    (BitVec.ofNat 12 0) (base + 96) hval
  rw [show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) from by decide] at hsent
  runBlock hld0 hld1 hld2 hor1 hld3 hor2 hc0' hc1' horc1 hc2' horc2 hc3' horc3 haddi
    hbeq hbne hldcs hbgeu hsent

-- ============================================================================
-- Public stack-level witness
-- ============================================================================

/-- Weaken two leading concrete register atoms to `regOwn`. -/
private theorem sepConj_own2 {r1 r2 : Reg} {v1 v2 : Word} {Q : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** Q) h → (regOwn r1 ** regOwn r2 ** Q) h :=
  fun h hp =>
    sepConj_mono_left (regIs_to_regOwn r1 v1) h
      (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn r2 v2)) h hp)

/-- Weaken three leading concrete register atoms to `regOwn`. -/
private theorem sepConj_own3 {r1 r2 r3 : Reg} {v1 v2 v3 : Word} {Q : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** Q) h →
      (regOwn r1 ** regOwn r2 ** regOwn r3 ** Q) h :=
  fun h hp =>
    sepConj_mono_left (regIs_to_regOwn r1 v1) h
      (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn r2 v2)) h
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn r3 v3))) h hp))

/-- **JUMPI stack spec** (the `.proven` witness): pops `dest` (top) and `cond`
    (second), advancing the EVM stack pointer by 64 (the stack memory is read,
    not written). Three outcomes, selected by a nested if-then-else over the
    path-dependent registers `validityReg` / `x10`:

    - `cond == 0` (all four cond limbs zero): fall-through — `x10 := x10 + 1`
      and `validityReg := 0x5b`.
    - `cond != 0` and `dest` valid (upper three limbs zero and `dest.low <u
      codeSize`): `x10 := codeBase + dest.low`, `validityReg := code[dest.low]`.
    - otherwise (invalid taken jump): `validityReg := 0`, `x10` owned but
      unconstrained.

    The clobbered temps `condReg` / `tmpReg` are shed to `regOwn`; `destReg`
    ends at `dest.low`. Hypotheses mirror JUMP: register shape (`≠ x0`), the
    dispatcher fact `codeSize.toNat ≤ codeBytes.length`, and the code-region
    shape facts (dword-aligned base, no address overflow, valid byte access)
    used by the single code-byte read on the valid path. -/
theorem evm_jumpi_stack_spec_within
    (codeBaseReg envBaseReg destReg condReg tmpReg validityReg : Reg)
    (hdest : destReg ≠ .x0) (hcondR : condReg ≠ .x0) (htmp : tmpReg ≠ .x0)
    (hval : validityReg ≠ .x0)
    (nsp base envAddr codeBase x10old destOld condOld tmpOld valOld : Word)
    (dest cond : EvmWord) (codeSize : Word) (codeBytes : List (BitVec 8))
    (rest : List EvmWord)
    (hcount : codeSize.toNat ≤ codeBytes.length)
    (halign : codeBase.toNat % 8 = 0)
    (hcodeOver : codeBase.toNat + codeBytes.length ≤ 2 ^ 64)
    (hcodeValid : ∀ j : Nat, j < codeBytes.length →
      isValidByteAccess (codeBase + BitVec.ofNat 64 j) = true) :
    let code := evm_jumpi_code codeBaseReg envBaseReg destReg condReg tmpReg validityReg base
    cpsTripleWithin 21 base (base + 100) code
      ((codeBaseReg ↦ᵣ codeBase) ** (envBaseReg ↦ᵣ envAddr) **
       (destReg ↦ᵣ destOld) ** (condReg ↦ᵣ condOld) ** (tmpReg ↦ᵣ tmpOld) **
       (validityReg ↦ᵣ valOld) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ x10old) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (dest :: cond :: rest) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       bytesRegion codeBase codeBytes)
      ((codeBaseReg ↦ᵣ codeBase) ** (envBaseReg ↦ᵣ envAddr) **
       (destReg ↦ᵣ dest.getLimbN 0) ** regOwn condReg ** regOwn tmpReg **
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ (nsp + 64)) **
       evmStackIs nsp (dest :: cond :: rest) **
       ((envAddr + BitVec.ofNat 64 EvmAsm.Evm64.Code.codeSizeOff) ↦ₘ codeSize) **
       bytesRegion codeBase codeBytes **
       (if cond.getLimbN 0 = 0 ∧ cond.getLimbN 1 = 0 ∧ cond.getLimbN 2 = 0 ∧
            cond.getLimbN 3 = 0
        then (validityReg ↦ᵣ (0x5b : Word)) ** (.x10 ↦ᵣ (x10old + 1))
        else if dest.getLimbN 1 = 0 ∧ dest.getLimbN 2 = 0 ∧ dest.getLimbN 3 = 0 ∧
               BitVec.ult (dest.getLimbN 0) codeSize
          then (validityReg ↦ᵣ ((codeBytes.getD (dest.getLimbN 0).toNat 0).zeroExtend 64)) **
               (.x10 ↦ᵣ (codeBase + dest.getLimbN 0))
          else (validityReg ↦ᵣ (0 : Word)) ** regOwn .x10)) := by
  intro code
  have hwordD : evmWordIs nsp dest
      = ((nsp ↦ₘ dest.getLimbN 0) ** ((nsp + 8) ↦ₘ dest.getLimbN 1) **
         ((nsp + 16) ↦ₘ dest.getLimbN 2) ** ((nsp + 24) ↦ₘ dest.getLimbN 3)) := rfl
  have hwordC : evmWordIs (nsp + 32) cond
      = (((nsp + 32) ↦ₘ cond.getLimbN 0) ** (((nsp + 32) + 8) ↦ₘ cond.getLimbN 1) **
         (((nsp + 32) + 16) ↦ₘ cond.getLimbN 2) ** (((nsp + 32) + 24) ↦ₘ cond.getLimbN 3)) := rfl
  by_cases hcz : cond.getLimbN 0 = 0 ∧ cond.getLimbN 1 = 0 ∧ cond.getLimbN 2 = 0 ∧
      cond.getLimbN 3 = 0
  · -- Fall-through path (`cond == 0`).
    rw [if_pos hcz]
    obtain ⟨hcz0, hcz1, hcz2, hcz3⟩ := hcz
    have hcond : (((cond.getLimbN 0 ||| cond.getLimbN 1) ||| cond.getLimbN 2) ||| cond.getLimbN 3)
        = 0 := (or4_eq_zero_iff _ _ _ _).mpr ⟨hcz0, hcz1, hcz2, hcz3⟩
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
      (cpsTripleWithin_frameR (evmStackIs ((nsp + 32) + 32) rest ** bytesRegion codeBase codeBytes)
        (pcFree_sepConj pcFree_evmStackIs (bytesRegion_pcFree _ _))
        (cpsTripleWithin_mono_nSteps (by omega)
          (evm_jumpi_fallthrough_spec_within codeBaseReg envBaseReg destReg condReg tmpReg validityReg
            hdest hcondR htmp hval nsp base envAddr codeBase x10old destOld condOld tmpOld valOld
            (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
            (cond.getLimbN 0) (cond.getLimbN 1) (cond.getLimbN 2) (cond.getLimbN 3)
            codeSize hcond)))
    · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC] at hp
      xperm_hyp hp
    · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC]
      have hq' := sepConj_mono_left (sepConj_own2 (r1 := condReg) (r2 := tmpReg)) h hq
      xperm_hyp hq'
  · -- Taken paths (`cond != 0`).
    rw [if_neg hcz]
    have hcond_ne : (((cond.getLimbN 0 ||| cond.getLimbN 1) ||| cond.getLimbN 2)
        ||| cond.getLimbN 3) ≠ 0 := fun h => hcz ((or4_eq_zero_iff _ _ _ _).mp h)
    by_cases hvalid : dest.getLimbN 1 = 0 ∧ dest.getLimbN 2 = 0 ∧ dest.getLimbN 3 = 0 ∧
        BitVec.ult (dest.getLimbN 0) codeSize
    · -- Valid taken jump.
      rw [if_pos hvalid]
      obtain ⟨hz1, hz2, hz3, hlt⟩ := hvalid
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
        (cpsTripleWithin_frameR (evmStackIs ((nsp + 32) + 32) rest ** front ** restR)
          (pcFree_sepConj pcFree_evmStackIs (pcFree_sepConj hf hr))
          (evm_jumpi_valid_spec_within codeBaseReg envBaseReg destReg condReg tmpReg validityReg
            hdest hcondR htmp hval nsp base envAddr codeBase x10old destOld condOld tmpOld valOld
            (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
            (cond.getLimbN 0) (cond.getLimbN 1) (cond.getLimbN 2) (cond.getLimbN 3)
            codeSize dwAddr wVal hcond_ne hor hlt halign_lbu hvalid_lbu))
      · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC, hsplit] at hp
        xperm_hyp hp
      · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC, hsplit, hgetD]
        have hq' := sepConj_mono_left (sepConj_own2 (r1 := condReg) (r2 := tmpReg)) h hq
        xperm_hyp hq'
    · -- Invalid taken jump.
      rw [if_neg hvalid]
      by_cases hor : ((dest.getLimbN 1 ||| dest.getLimbN 2) ||| dest.getLimbN 3) = 0
      · -- Upper limbs canonical but out of bounds → BGEU sentinel.
        obtain ⟨hz1, hz2, hz3⟩ := (or3_eq_zero_iff _ _ _).mp hor
        have hbounds : ¬ BitVec.ult (dest.getLimbN 0) codeSize :=
          fun hl => hvalid ⟨hz1, hz2, hz3, hl⟩
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
          (cpsTripleWithin_frameR (evmStackIs ((nsp + 32) + 32) rest ** bytesRegion codeBase codeBytes)
            (pcFree_sepConj pcFree_evmStackIs (bytesRegion_pcFree _ _))
            (cpsTripleWithin_mono_nSteps (by omega)
              (evm_jumpi_invalid_bounds_spec_within codeBaseReg envBaseReg destReg condReg tmpReg validityReg
                hdest hcondR htmp hval nsp base envAddr codeBase x10old destOld condOld tmpOld valOld
                (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
                (cond.getLimbN 0) (cond.getLimbN 1) (cond.getLimbN 2) (cond.getLimbN 3)
                codeSize hcond_ne hor hbounds)))
        · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC] at hp
          xperm_hyp hp
        · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC]
          have hq' := sepConj_mono_left
            (sepConj_own3 (r1 := condReg) (r2 := tmpReg) (r3 := .x10)) h hq
          xperm_hyp hq'
      · -- Nonzero upper limb → BNE sentinel.
        refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
          (cpsTripleWithin_frameR (evmStackIs ((nsp + 32) + 32) rest ** bytesRegion codeBase codeBytes)
            (pcFree_sepConj pcFree_evmStackIs (bytesRegion_pcFree _ _))
            (cpsTripleWithin_mono_nSteps (by omega)
              (evm_jumpi_invalid_upper_spec_within codeBaseReg envBaseReg destReg condReg tmpReg validityReg
                hdest hcondR htmp hval nsp base envAddr codeBase x10old destOld condOld tmpOld valOld
                (dest.getLimbN 0) (dest.getLimbN 1) (dest.getLimbN 2) (dest.getLimbN 3)
                (cond.getLimbN 0) (cond.getLimbN 1) (cond.getLimbN 2) (cond.getLimbN 3)
                codeSize hcond_ne hor)))
        · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC] at hp
          xperm_hyp hp
        · rw [evmStackIs_cons, evmStackIs_cons, hwordD, hwordC]
          have hq' := sepConj_mono_left
            (sepConj_own3 (r1 := condReg) (r2 := tmpReg) (r3 := .x10)) h hq
          xperm_hyp hq'

end ControlFlow
end EvmAsm.Evm64
