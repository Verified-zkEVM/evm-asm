/-
  EvmAsm.Evm64.BlobHash.Spec

  Stack-level cpsTripleWithin specification for the EVM `BLOBHASH` opcode
  (0x49, EIP-4844; see `EvmAsm/Evm64/BlobHash/Program.lean`).

  BLOBHASH pops an index word `w` and pushes `hashes[w]` when the index is in
  range (`w.getLimbN 1/2/3 = 0` and `w.getLimbN 0 <u count`), or zero
  otherwise. The pop-then-push happens in place at the stack top: `x12` is
  unchanged. The program has five exit paths — three early BNE guards on the
  high limbs, a BGEU bounds guard against the dispatcher-seeded count cell at
  `envAddr + blobHashCountOff`, and the valid table-read path (SLLI-by-5 +
  ADD indexing into the `evm_blob_hashes` table, four LD/SD limb copies, JAL
  over the zero arm).

  Layout of this file:
  - Five per-path core lemmas at the raw memory-cell level, one per exit path
    (`evm_blobhash_zero_high1/2/3_spec_within`, `evm_blobhash_zero_oob_spec_within`,
    `evm_blobhash_valid_spec_within`), each a straight-line `runBlock`
    composition where the untaken branch arm is discharged by
    `cpsBranchWithin_takenStripPure2` / `cpsBranchWithin_ntakenStripPure2`.
  - The public witness `evm_blobhash_stack_spec_within`: a single **merged
    if-then-else** triple (not a valid/zero pair). Precondition holds the
    index word on the stack (`evmStackIs nsp (w :: rest)`), the count cell,
    and the hash table (`evmStackIs tblAddr hashes`); postcondition replaces
    the stack top with
    `if w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
        w.getLimbN 0 <u count then hashes.getD (w.getLimbN 0).toNat 0 else 0`.
    Scratch registers (`tableBaseReg`, `idxReg`, `tmpReg`, `valReg`) are
    clobbered to `regOwn`; everything else is framed. The only hypotheses are
    register non-`x0` shape conditions and the dispatcher table-shape fact
    `count.toNat ≤ hashes.length` (no upper bound on the table length is
    needed: the entry-offset arithmetic `32 * k = i0 <<< 5` holds modulo
    `2^64` unconditionally).
-/

import EvmAsm.Evm64.BlobHash.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace BlobHash

open EvmAsm.Rv64

-- ============================================================================
-- Per-path core lemmas (raw memory cells)
--
-- All five cores share a uniform footprint: the seven registers
-- (`tableBaseReg`, `idxReg`, `tmpReg`, `valReg`, `envBaseReg`, `x0`, `x12`),
-- the four stack-top limb cells at `nsp .. nsp+24`, and the count cell at
-- `envAddr + blobHashCountOff`. The valid path additionally owns the four
-- table-entry cells at `tblAddr + (i0 <<< 5) + {0,8,16,24}`.
-- ============================================================================

/-- Zero path via the first BNE (index limb 1 nonzero → out of range).
    Executes LD, BNE(taken → `base+80`), then the four-SD zero arm. -/
theorem evm_blobhash_zero_high1_spec_within
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0)
    (nsp base envAddr tblAddr idxOld tmpOld valOld : Word)
    (i0 i1 i2 i3 count : Word)
    (h1nz : i1 ≠ 0) :
    let code := evm_blobhash_code envBaseReg tableBaseReg idxReg tmpReg valReg base
    cpsTripleWithin 6 base (base + 96) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ i1) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count)) := by
  -- +0 LD tmpReg x12 8 (index limb 1)
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  -- +4 BNE tmpReg x0 +76 (taken: i1 ≠ 0) → base + 80
  have hbne_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i1 (0 : Word) (base + 4)
  rw [show signExtend13 (BitVec.ofNat 13 76) = BitVec.ofNat 64 76 from by decide,
      show (base + 4 : Word) + BitVec.ofNat 64 76 = base + 80 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact h1nz ((sepConj_pure_right _).mp h_rest).2)
  -- +80 .. +92 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 84)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 88)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 92)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne hsd0 hsd1 hsd2 hsd3

/-- Zero path via the second BNE (limb 1 zero, limb 2 nonzero). -/
theorem evm_blobhash_zero_high2_spec_within
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0)
    (nsp base envAddr tblAddr idxOld tmpOld valOld : Word)
    (i0 i1 i2 i3 count : Word)
    (hz1 : i1 = 0) (h2nz : i2 ≠ 0) :
    let code := evm_blobhash_code envBaseReg tableBaseReg idxReg tmpReg valReg base
    cpsTripleWithin 8 base (base + 96) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ i2) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count)) := by
  -- +0 LD tmpReg x12 8; +4 BNE (not taken: i1 = 0)
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  -- +8 LD tmpReg x12 16; +12 BNE (taken: i2 ≠ 0) → base + 80
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 68) i2 (0 : Word) (base + 12)
  rw [show signExtend13 (BitVec.ofNat 13 68) = BitVec.ofNat 64 68 from by decide,
      show (base + 12 : Word) + BitVec.ofNat 64 68 = base + 80 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact h2nz ((sepConj_pure_right _).mp h_rest).2)
  -- +80 .. +92 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 84)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 88)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 92)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hsd0 hsd1 hsd2 hsd3

/-- Zero path via the third BNE (limbs 1-2 zero, limb 3 nonzero). -/
theorem evm_blobhash_zero_high3_spec_within
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0)
    (nsp base envAddr tblAddr idxOld tmpOld valOld : Word)
    (i0 i1 i2 i3 count : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (h3nz : i3 ≠ 0) :
    let code := evm_blobhash_code envBaseReg tableBaseReg idxReg tmpReg valReg base
    cpsTripleWithin 10 base (base + 96) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ i3) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count)) := by
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 68) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  -- +16 LD tmpReg x12 24; +20 BNE (taken: i3 ≠ 0) → base + 80
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 60) i3 (0 : Word) (base + 20)
  rw [show signExtend13 (BitVec.ofNat 13 60) = BitVec.ofNat 64 60 from by decide,
      show (base + 20 : Word) + BitVec.ofNat 64 60 = base + 80 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_takenStripPure2 hbne3_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact h3nz ((sepConj_pure_right _).mp h_rest).2)
  -- +80 .. +92 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 84)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 88)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 92)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hsd0 hsd1 hsd2 hsd3

/-- Zero path via the BGEU bounds guard (high limbs zero, `i0 ≥ count`). -/
theorem evm_blobhash_zero_oob_spec_within
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0) (hidx : idxReg ≠ .x0)
    (nsp base envAddr tblAddr idxOld tmpOld valOld : Word)
    (i0 i1 i2 i3 count : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (hz3 : i3 = 0)
    (hge : ¬ BitVec.ult i0 count) :
    let code := evm_blobhash_code envBaseReg tableBaseReg idxReg tmpReg valReg base
    cpsTripleWithin 13 base (base + 96) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ i0) **
       (tmpReg ↦ᵣ count) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count)) := by
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 68) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 60) i3 (0 : Word) (base + 20)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz3)
  -- +24 LD idxReg x12 0 (low index limb)
  have hld0 := ld_spec_gen_within idxReg .x12 nsp idxOld i0 0 (base + 24) hidx
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  -- +28 LD tmpReg envBaseReg 544 (count)
  have hldc := ld_spec_gen_within tmpReg envBaseReg envAddr i3 count
    (BitVec.ofNat 12 blobHashCountOff) (base + 28) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blobHashCountOff)
        = BitVec.ofNat 64 blobHashCountOff from
        signExtend12_ofNat_small (by decide)] at hldc
  -- +32 BGEU idxReg tmpReg +48 (taken: ¬ i0 <u count) → base + 80
  have hbgeu_raw := bgeu_spec_gen_within idxReg tmpReg (BitVec.ofNat 13 48) i0 count (base + 32)
  rw [show signExtend13 (BitVec.ofNat 13 48) = BitVec.ofNat 64 48 from by decide,
      show (base + 32 : Word) + BitVec.ofNat 64 48 = base + 80 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_takenStripPure2 hbgeu_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hge ((sepConj_pure_right _).mp h_rest).2)
  -- +80 .. +92 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 80)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 84)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 88)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 92)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hld0 hldc hbgeu hsd0 hsd1 hsd2 hsd3

/-- Valid table-read path: all high limbs zero and `i0 <u count`. The four
    table-entry cells at `tblAddr + (i0 <<< 5) + {0,8,16,24}` are copied to
    the stack top; `tableBaseReg` is clobbered to the entry address and
    `idxReg` to the byte offset `i0 <<< 5`. -/
theorem evm_blobhash_valid_spec_within
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg)
    (htbl : tableBaseReg ≠ .x0) (hidx : idxReg ≠ .x0)
    (htmp : tmpReg ≠ .x0) (hval : valReg ≠ .x0)
    (nsp base envAddr tblAddr idxOld tmpOld valOld : Word)
    (i0 i1 i2 i3 count v0 v1 v2 v3 : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (hz3 : i3 = 0)
    (hlt : BitVec.ult i0 count) :
    let code := evm_blobhash_code envBaseReg tableBaseReg idxReg tmpReg valReg base
    cpsTripleWithin 20 base (base + 96) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count) **
       ((tblAddr + (i0 <<< 5)) ↦ₘ v0) ** ((tblAddr + (i0 <<< 5) + 8) ↦ₘ v1) **
       ((tblAddr + (i0 <<< 5) + 16) ↦ₘ v2) ** ((tblAddr + (i0 <<< 5) + 24) ↦ₘ v3))
      ((tableBaseReg ↦ᵣ (tblAddr + (i0 <<< 5))) ** (idxReg ↦ᵣ (i0 <<< 5)) **
       (tmpReg ↦ᵣ count) ** (valReg ↦ᵣ v3) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ v0) ** ((nsp + 8) ↦ₘ v1) **
       ((nsp + 16) ↦ₘ v2) ** ((nsp + 24) ↦ₘ v3) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count) **
       ((tblAddr + (i0 <<< 5)) ↦ₘ v0) ** ((tblAddr + (i0 <<< 5) + 8) ↦ₘ v1) **
       ((tblAddr + (i0 <<< 5) + 16) ↦ₘ v2) ** ((tblAddr + (i0 <<< 5) + 24) ↦ₘ v3)) := by
  -- +0 LD limb 1; +4 BNE not taken
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  -- +8 LD limb 2; +12 BNE not taken
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 68) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  -- +16 LD limb 3; +20 BNE not taken
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 60) i3 (0 : Word) (base + 20)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz3)
  -- +24 LD low index; +28 LD count; +32 BGEU not taken
  have hld0 := ld_spec_gen_within idxReg .x12 nsp idxOld i0 0 (base + 24) hidx
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  have hldc := ld_spec_gen_within tmpReg envBaseReg envAddr i3 count
    (BitVec.ofNat 12 blobHashCountOff) (base + 28) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blobHashCountOff)
        = BitVec.ofNat 64 blobHashCountOff from
        signExtend12_ofNat_small (by decide)] at hldc
  have hbgeu_raw := bgeu_spec_gen_within idxReg tmpReg (BitVec.ofNat 13 48) i0 count (base + 32)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_ntakenStripPure2 hbgeu_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlt)
  -- +36 SLLI idxReg idxReg 5 (32-byte entry stride)
  have hslli := slli_spec_gen_same_within idxReg i0 5 (base + 36) hidx
  rw [show ((5 : BitVec 6)).toNat = 5 from rfl] at hslli
  -- +40 ADD tableBaseReg tableBaseReg idxReg (entry address)
  have hadd := add_spec_gen_rd_eq_rs1_within tableBaseReg idxReg tblAddr (i0 <<< 5)
    (base + 40) htbl
  -- +44 .. +72 copy the four entry limbs to the stack top
  have hldv0 := ld_spec_gen_within valReg tableBaseReg (tblAddr + (i0 <<< 5)) valOld v0
    0 (base + 44) hval
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ((tblAddr + (i0 <<< 5)) + 0 : Word) = tblAddr + (i0 <<< 5) from by bv_omega] at hldv0
  have hsd0 := sd_spec_gen_within .x12 valReg nsp v0 i0 0 (base + 48)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hldv1 := ld_spec_gen_within valReg tableBaseReg (tblAddr + (i0 <<< 5)) v0 v1
    8 (base + 52) hval
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show ((tblAddr + (i0 <<< 5)) + BitVec.ofNat 64 8 : Word) = tblAddr + (i0 <<< 5) + 8
        from by bv_omega] at hldv1
  have hsd1 := sd_spec_gen_within .x12 valReg nsp v1 i1 8 (base + 56)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hldv2 := ld_spec_gen_within valReg tableBaseReg (tblAddr + (i0 <<< 5)) v1 v2
    16 (base + 60) hval
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show ((tblAddr + (i0 <<< 5)) + BitVec.ofNat 64 16 : Word) = tblAddr + (i0 <<< 5) + 16
        from by bv_omega] at hldv2
  have hsd2 := sd_spec_gen_within .x12 valReg nsp v2 i2 16 (base + 64)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hldv3 := ld_spec_gen_within valReg tableBaseReg (tblAddr + (i0 <<< 5)) v2 v3
    24 (base + 68) hval
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show ((tblAddr + (i0 <<< 5)) + BitVec.ofNat 64 24 : Word) = tblAddr + (i0 <<< 5) + 24
        from by bv_omega] at hldv3
  have hsd3 := sd_spec_gen_within .x12 valReg nsp v3 i3 24 (base + 72)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  -- +76 JAL x0 +20 over the zero arm → base + 96
  have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 20) (base + 76)
  rw [show signExtend21 (BitVec.ofNat 21 20) = BitVec.ofNat 64 20 from by decide,
      show (base + 76 : Word) + BitVec.ofNat 64 20 = base + 96 from by bv_omega] at hjal
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hld0 hldc hbgeu hslli hadd
    hldv0 hsd0 hldv1 hsd1 hldv2 hsd2 hldv3 hsd3 hjal

-- ============================================================================
-- Public stack-level witness
-- ============================================================================

/-- Weaken the four leading concrete scratch-register atoms to `regOwn`. -/
private theorem sepConj_own4 {r1 r2 r3 r4 : Reg} {v1 v2 v3 v4 : Word} {Q : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) ** Q) h →
      (regOwn r1 ** regOwn r2 ** regOwn r3 ** regOwn r4 ** Q) h :=
  fun h hp =>
    sepConj_mono_left (regIs_to_regOwn r1 v1) h
      (sepConj_mono_right
        (sepConj_mono (regIs_to_regOwn r2 v2)
          (sepConj_mono (regIs_to_regOwn r3 v3)
            (sepConj_mono_left (regIs_to_regOwn r4 v4)))) h hp)

/-- **BLOBHASH stack spec** (the `.proven` witness): pops the index word `w`
    and pushes, in place at the stack top (`x12` unchanged),
    `hashes[w]` when `w` is in range and `0` otherwise — as a single merged
    if-then-else postcondition. Unconditional over all inputs: the only
    hypotheses are register shape conditions (scratch registers distinct from
    `x0`) and the dispatcher-guaranteed table shape
    `count.toNat ≤ hashes.length`. The scratch registers
    (`tableBaseReg`, `idxReg`, `tmpReg`, `valReg`) end clobbered (`regOwn`);
    the count cell and the hash table are framed. -/
theorem evm_blobhash_stack_spec_within
    (envBaseReg tableBaseReg idxReg tmpReg valReg : Reg)
    (htbl : tableBaseReg ≠ .x0) (hidx : idxReg ≠ .x0)
    (htmp : tmpReg ≠ .x0) (hval : valReg ≠ .x0)
    (nsp base envAddr tblAddr idxOld tmpOld valOld : Word)
    (w : EvmWord) (count : Word) (hashes : List EvmWord) (rest : List EvmWord)
    (hcount : count.toNat ≤ hashes.length) :
    let code := evm_blobhash_code envBaseReg tableBaseReg idxReg tmpReg valReg base
    cpsTripleWithin 20 base (base + 96) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (idxReg ↦ᵣ idxOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (w :: rest) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count) **
       evmStackIs tblAddr hashes)
      (regOwn tableBaseReg ** regOwn idxReg ** regOwn tmpReg ** regOwn valReg **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp
         ((if w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
              BitVec.ult (w.getLimbN 0) count
           then hashes.getD (w.getLimbN 0).toNat 0 else 0) :: rest) **
       ((envAddr + BitVec.ofNat 64 blobHashCountOff) ↦ₘ count) **
       evmStackIs tblAddr hashes) := by
  intro code
  by_cases hc : w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
      BitVec.ult (w.getLimbN 0) count
  · -- Valid path: table read.
    rw [if_pos hc]
    obtain ⟨hz1, hz2, hz3, hlt⟩ := hc
    have hklt : (w.getLimbN 0).toNat < hashes.length := by
      have h0 : (w.getLimbN 0).toNat < count.toNat := by
        rwa [BitVec.ult_iff_lt] at hlt
      omega
    -- The stack top becomes the table entry.
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt, Option.getD_some]
    -- Byte offset of entry k: `32 * k = i0 <<< 5` (no overflow: k < 16).
    have hshift : BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) = w.getLimbN 0 <<< 5 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    -- Split the table at entry k.
    have hsplit := evmStackIs_split_at tblAddr hashes (w.getLimbN 0).toNat hklt
    refine cpsTripleWithin_weaken
      (fun h hp => ?_) (fun h hq => ?_)
      (cpsTripleWithin_frameR
        (evmStackIs (nsp + 32) rest **
         evmStackIs tblAddr (hashes.take (w.getLimbN 0).toNat) **
         evmStackIs (tblAddr + BitVec.ofNat 64 (((w.getLimbN 0).toNat + 1) * 32))
           (hashes.drop ((w.getLimbN 0).toNat + 1)))
        (pcFree_sepConj pcFree_evmStackIs
          (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs))
        (evm_blobhash_valid_spec_within envBaseReg tableBaseReg idxReg tmpReg valReg
          htbl hidx htmp hval nsp base envAddr tblAddr idxOld tmpOld valOld
          (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) count
          ((hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 0)
          ((hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 1)
          ((hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 2)
          ((hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 3)
          hz1 hz2 hz3 hlt))
    · -- Pre: unfold the stack word and split the table.
      rw [evmStackIs_cons,
          show evmWordIs nsp w
              = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                 ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl,
          hsplit,
          show evmWordIs (tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32))
                (hashes[(w.getLimbN 0).toNat]'hklt)
              = (((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32)) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 0) **
                 ((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) + 8) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 1) **
                 ((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) + 16) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 2) **
                 ((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) + 24) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 3)) from rfl,
          hshift] at hp
      xperm_hyp hp
    · -- Post: fold the stack word and reassemble the table, then weaken the
      -- scratch registers to regOwn (via sepConj_own4 on the framed core post).
      rw [evmStackIs_cons,
          show evmWordIs nsp (hashes[(w.getLimbN 0).toNat]'hklt)
              = ((nsp ↦ₘ (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 0) **
                 ((nsp + 8) ↦ₘ (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 1) **
                 ((nsp + 16) ↦ₘ (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 2) **
                 ((nsp + 24) ↦ₘ (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 3)) from rfl,
          hsplit,
          show evmWordIs (tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32))
                (hashes[(w.getLimbN 0).toNat]'hklt)
              = (((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32)) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 0) **
                 ((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) + 8) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 1) **
                 ((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) + 16) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 2) **
                 ((tblAddr + BitVec.ofNat 64 ((w.getLimbN 0).toNat * 32) + 24) ↦ₘ
                    (hashes[(w.getLimbN 0).toNat]'hklt).getLimbN 3)) from rfl,
          hshift]
      have hq' := sepConj_mono_left
        (sepConj_own4 (r1 := tableBaseReg) (r2 := idxReg) (r3 := tmpReg) (r4 := valReg))
        h hq
      xperm_hyp hq'
  · -- Zero paths: dispatch on which guard fires.
    rw [if_neg hc]
    by_cases hz1 : w.getLimbN 1 = 0
    · by_cases hz2 : w.getLimbN 2 = 0
      · by_cases hz3 : w.getLimbN 3 = 0
        · -- Bounds guard: high limbs zero but index ≥ count.
          have hge : ¬ BitVec.ult (w.getLimbN 0) count :=
            fun hlt => hc ⟨hz1, hz2, hz3, hlt⟩
          refine cpsTripleWithin_weaken
            (fun h hp => ?_) (fun h hq => ?_)
            (cpsTripleWithin_frameR
              (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
              (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
              (cpsTripleWithin_mono_nSteps (by omega)
                (evm_blobhash_zero_oob_spec_within envBaseReg tableBaseReg idxReg
                  tmpReg valReg htmp hidx nsp base envAddr tblAddr idxOld tmpOld valOld
                  (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) count
                  hz1 hz2 hz3 hge)))
          · rw [evmStackIs_cons,
                show evmWordIs nsp w
                    = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                       ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
            xperm_hyp hp
          · rw [evmStackIs_cons, evmWordIs_zero]
            have hq' := sepConj_mono_left
              (sepConj_own4 (r1 := tableBaseReg) (r2 := idxReg) (r3 := tmpReg) (r4 := valReg))
              h hq
            xperm_hyp hq'
        · -- Third high-limb guard.
          refine cpsTripleWithin_weaken
            (fun h hp => ?_) (fun h hq => ?_)
            (cpsTripleWithin_frameR
              (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
              (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
              (cpsTripleWithin_mono_nSteps (by omega)
                (evm_blobhash_zero_high3_spec_within envBaseReg tableBaseReg idxReg
                  tmpReg valReg htmp nsp base envAddr tblAddr idxOld tmpOld valOld
                  (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) count
                  hz1 hz2 hz3)))
          · rw [evmStackIs_cons,
                show evmWordIs nsp w
                    = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                       ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
            xperm_hyp hp
          · rw [evmStackIs_cons, evmWordIs_zero]
            have hq' := sepConj_mono_left
              (sepConj_own4 (r1 := tableBaseReg) (r2 := idxReg) (r3 := tmpReg) (r4 := valReg))
              h hq
            xperm_hyp hq'
      · -- Second high-limb guard.
        refine cpsTripleWithin_weaken
          (fun h hp => ?_) (fun h hq => ?_)
          (cpsTripleWithin_frameR
            (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
            (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
            (cpsTripleWithin_mono_nSteps (by omega)
              (evm_blobhash_zero_high2_spec_within envBaseReg tableBaseReg idxReg
                tmpReg valReg htmp nsp base envAddr tblAddr idxOld tmpOld valOld
                (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) count
                hz1 hz2)))
        · rw [evmStackIs_cons,
              show evmWordIs nsp w
                  = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                     ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
          xperm_hyp hp
        · rw [evmStackIs_cons, evmWordIs_zero]
          have hq' := sepConj_mono_left
            (sepConj_own4 (r1 := tableBaseReg) (r2 := idxReg) (r3 := tmpReg) (r4 := valReg))
            h hq
          xperm_hyp hq'
    · -- First high-limb guard.
      refine cpsTripleWithin_weaken
        (fun h hp => ?_) (fun h hq => ?_)
        (cpsTripleWithin_frameR
          (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
          (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
          (cpsTripleWithin_mono_nSteps (by omega)
            (evm_blobhash_zero_high1_spec_within envBaseReg tableBaseReg idxReg
              tmpReg valReg htmp nsp base envAddr tblAddr idxOld tmpOld valOld
              (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) count
              hz1)))
      · rw [evmStackIs_cons,
            show evmWordIs nsp w
                = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                   ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
        xperm_hyp hp
      · rw [evmStackIs_cons, evmWordIs_zero]
        have hq' := sepConj_mono_left
          (sepConj_own4 (r1 := tableBaseReg) (r2 := idxReg) (r3 := tmpReg) (r4 := valReg))
          h hq
        xperm_hyp hq'

-- #print axioms evm_blobhash_stack_spec_within
--   (and all five per-path cores): [propext, Classical.choice, Quot.sound]

end BlobHash
end EvmAsm.Evm64
