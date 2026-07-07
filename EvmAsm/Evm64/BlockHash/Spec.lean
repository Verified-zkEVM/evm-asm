/-
  EvmAsm.Evm64.BlockHash.Spec

  Stack-level cpsTripleWithin specification for the EVM `BLOCKHASH` opcode
  (0x40; see `EvmAsm/Evm64/BlockHash/Program.lean`).

  BLOCKHASH pops a target block number `w` and pushes the hash of that block
  when it lies within the recent-history window, or zero otherwise. With
  `cur` the current block number (env+552), `count` the number of loaded
  recent hashes (env+560, `count.toNat ≤ hashes.length`), and `hashes` the
  `evm_block_hashes` table in increasing block-number order, the pushed word
  is `hashes[count - (cur - w)]` when the high limbs of `w` are zero,
  `w <u cur`, and `¬ count <u cur - w` (i.e. `age := cur - w ≤ count`), and
  `0` otherwise. The pop-then-push happens in place at the stack top: `x12`
  is unchanged. The program has six exit paths — three early BNE guards on
  the high limbs, a BGEU guard (`target ≥ cur`), a BLTU guard
  (`count < age`), and the valid table-read path (two SUBs computing
  `age = cur - target` and `index = count - age`, SLLI-by-5 + ADD indexing,
  four LD/SD limb copies, JAL over the zero arm).

  Layout of this file:
  - Six per-path core lemmas at the raw memory-cell level, one per exit path
    (`evm_blockhash_zero_high1/2/3_spec_within`,
    `evm_blockhash_zero_future_spec_within` (BGEU, target ≥ cur),
    `evm_blockhash_zero_ancient_spec_within` (BLTU, count < age),
    `evm_blockhash_valid_spec_within`), each a straight-line `runBlock`
    composition where the untaken branch arm is discharged by
    `cpsBranchWithin_takenStripPure2` / `cpsBranchWithin_ntakenStripPure2`.
    Per-path step bounds: 6 / 8 / 10 / 13 / 16 / 24.
  - The public witness `evm_blockhash_stack_spec_within`: a single **merged
    if-then-else** triple. Precondition holds the target word on the stack
    (`evmStackIs nsp (w :: rest)`), the two env cells (`cur` at
    `envAddr + blockNumberOff`, `count` at `envAddr + blockHashCountOff`),
    and the hash table (`evmStackIs tblAddr hashes`); postcondition replaces
    the stack top with
    `if w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
        BitVec.ult (w.getLimbN 0) cur ∧
        ¬ BitVec.ult count (cur - w.getLimbN 0)
     then hashes.getD (count - (cur - w.getLimbN 0)).toNat 0 else 0`.
    Scratch registers (`tableBaseReg`, `tgtReg`, `tmpReg`, `valReg`) are
    clobbered to `regOwn`; everything else is framed. The only hypotheses
    are register non-`x0` shape conditions and the dispatcher table-shape
    fact `count.toNat ≤ hashes.length`. In-range index for `getD`: the
    guards give `1 ≤ (cur - w.getLimbN 0).toNat ≤ count.toNat`, hence
    `(count - (cur - w.getLimbN 0)).toNat < count.toNat ≤ hashes.length`.
-/

import EvmAsm.Evm64.BlockHash.Program
import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace BlockHash

open EvmAsm.Rv64

-- ============================================================================
-- Per-path core lemmas (raw memory cells)
--
-- All six cores share a uniform footprint: the seven registers
-- (`tableBaseReg`, `tgtReg`, `tmpReg`, `valReg`, `envBaseReg`, `x0`, `x12`),
-- the four stack-top limb cells at `nsp .. nsp+24`, the current-block cell
-- at `envAddr + blockNumberOff`, and the count cell at
-- `envAddr + blockHashCountOff`. The valid path additionally owns the four
-- table-entry cells at `tblAddr + ((count - (cur - i0)) <<< 5) + {0,8,16,24}`.
-- ============================================================================

/-- Zero path via the first BNE (target limb 1 nonzero → out of range).
    Executes LD, BNE(taken → `base+96`), then the four-SD zero arm. -/
theorem evm_blockhash_zero_high1_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (i0 i1 i2 i3 cur count : Word)
    (h1nz : i1 ≠ 0) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 6 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ i1) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count)) := by
  -- +0 LD tmpReg x12 8 (target limb 1)
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  -- +4 BNE tmpReg x0 +92 (taken: i1 ≠ 0) → base + 96
  have hbne_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 92) i1 (0 : Word) (base + 4)
  rw [show signExtend13 (BitVec.ofNat 13 92) = BitVec.ofNat 64 92 from by decide,
      show (base + 4 : Word) + BitVec.ofNat 64 92 = base + 96 from by bv_omega] at hbne_raw
  have hbne := cpsBranchWithin_takenStripPure2 hbne_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact h1nz ((sepConj_pure_right _).mp h_rest).2)
  -- +96 .. +108 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 96)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 100)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 104)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 108)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne hsd0 hsd1 hsd2 hsd3

/-- Zero path via the second BNE (limb 1 zero, limb 2 nonzero). -/
theorem evm_blockhash_zero_high2_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (i0 i1 i2 i3 cur count : Word)
    (hz1 : i1 = 0) (h2nz : i2 ≠ 0) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 8 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ i2) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count)) := by
  -- +0 LD tmpReg x12 8; +4 BNE (not taken: i1 = 0)
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 92) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  -- +8 LD tmpReg x12 16; +12 BNE (taken: i2 ≠ 0) → base + 96
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 84) i2 (0 : Word) (base + 12)
  rw [show signExtend13 (BitVec.ofNat 13 84) = BitVec.ofNat 64 84 from by decide,
      show (base + 12 : Word) + BitVec.ofNat 64 84 = base + 96 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact h2nz ((sepConj_pure_right _).mp h_rest).2)
  -- +96 .. +108 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 96)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 100)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 104)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 108)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hsd0 hsd1 hsd2 hsd3

/-- Zero path via the third BNE (limbs 1-2 zero, limb 3 nonzero). -/
theorem evm_blockhash_zero_high3_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (i0 i1 i2 i3 cur count : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (h3nz : i3 ≠ 0) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 10 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ i3) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count)) := by
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 92) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 84) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  -- +16 LD tmpReg x12 24; +20 BNE (taken: i3 ≠ 0) → base + 96
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i3 (0 : Word) (base + 20)
  rw [show signExtend13 (BitVec.ofNat 13 76) = BitVec.ofNat 64 76 from by decide,
      show (base + 20 : Word) + BitVec.ofNat 64 76 = base + 96 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_takenStripPure2 hbne3_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact h3nz ((sepConj_pure_right _).mp h_rest).2)
  -- +96 .. +108 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 96)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 100)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 104)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 108)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hsd0 hsd1 hsd2 hsd3

/-- Zero path via the BGEU guard (high limbs zero, `target ≥ cur`: the
    requested block is the current block or in the future). -/
theorem evm_blockhash_zero_future_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0) (htgt : tgtReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (i0 i1 i2 i3 cur count : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (hz3 : i3 = 0)
    (hge : ¬ BitVec.ult i0 cur) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 13 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ i0) **
       (tmpReg ↦ᵣ cur) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count)) := by
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 92) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 84) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i3 (0 : Word) (base + 20)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz3)
  -- +24 LD tgtReg x12 0 (target block number)
  have hld0 := ld_spec_gen_within tgtReg .x12 nsp tgtOld i0 0 (base + 24) htgt
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  -- +28 LD tmpReg envBaseReg 552 (cur)
  have hldc := ld_spec_gen_within tmpReg envBaseReg envAddr i3 cur
    (BitVec.ofNat 12 blockNumberOff) (base + 28) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blockNumberOff)
        = BitVec.ofNat 64 blockNumberOff from
        signExtend12_ofNat_small (by decide)] at hldc
  -- +32 BGEU tgtReg tmpReg +64 (taken: ¬ i0 <u cur) → base + 96
  have hbgeu_raw := bgeu_spec_gen_within tgtReg tmpReg (BitVec.ofNat 13 64) i0 cur (base + 32)
  rw [show signExtend13 (BitVec.ofNat 13 64) = BitVec.ofNat 64 64 from by decide,
      show (base + 32 : Word) + BitVec.ofNat 64 64 = base + 96 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_takenStripPure2 hbgeu_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact hge ((sepConj_pure_right _).mp h_rest).2)
  -- +96 .. +108 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 96)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 100)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 104)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 108)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hld0 hldc hbgeu hsd0 hsd1 hsd2 hsd3

/-- Zero path via the BLTU guard (high limbs zero, `target <u cur` but
    `count <u age` with `age = cur - target`: the requested block is older
    than the loaded history window). -/
theorem evm_blockhash_zero_ancient_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htmp : tmpReg ≠ .x0) (htgt : tgtReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (i0 i1 i2 i3 cur count : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (hz3 : i3 = 0)
    (hlt : BitVec.ult i0 cur)
    (hoob : BitVec.ult count (cur - i0)) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 16 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count))
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ (cur - i0)) **
       (tmpReg ↦ᵣ count) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ (0 : Word)) ** ((nsp + 8) ↦ₘ (0 : Word)) **
       ((nsp + 16) ↦ₘ (0 : Word)) ** ((nsp + 24) ↦ₘ (0 : Word)) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count)) := by
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 92) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 84) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i3 (0 : Word) (base + 20)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz3)
  -- +24 LD tgtReg x12 0; +28 LD tmpReg envBaseReg 552; +32 BGEU not taken
  have hld0 := ld_spec_gen_within tgtReg .x12 nsp tgtOld i0 0 (base + 24) htgt
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  have hldc := ld_spec_gen_within tmpReg envBaseReg envAddr i3 cur
    (BitVec.ofNat 12 blockNumberOff) (base + 28) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blockNumberOff)
        = BitVec.ofNat 64 blockNumberOff from
        signExtend12_ofNat_small (by decide)] at hldc
  have hbgeu_raw := bgeu_spec_gen_within tgtReg tmpReg (BitVec.ofNat 13 64) i0 cur (base + 32)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_ntakenStripPure2 hbgeu_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlt)
  -- +36 SUB tgtReg tmpReg tgtReg (rd = rs2): tgtReg := age = cur - i0
  have hsuba := sub_spec_gen_rd_eq_rs2_within tgtReg tmpReg cur i0 (base + 36) htgt
  -- +40 LD tmpReg envBaseReg 560 (count)
  have hldcnt := ld_spec_gen_within tmpReg envBaseReg envAddr cur count
    (BitVec.ofNat 12 blockHashCountOff) (base + 40) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blockHashCountOff)
        = BitVec.ofNat 64 blockHashCountOff from
        signExtend12_ofNat_small (by decide)] at hldcnt
  -- +44 BLTU tmpReg tgtReg +52 (taken: count <u age) → base + 96
  have hbltu_raw := bltu_spec_gen_within tmpReg tgtReg (BitVec.ofNat 13 52) count (cur - i0)
    (base + 44)
  rw [show signExtend13 (BitVec.ofNat 13 52) = BitVec.ofNat 64 52 from by decide,
      show (base + 44 : Word) + BitVec.ofNat 64 52 = base + 96 from by bv_omega] at hbltu_raw
  have hbltu := cpsBranchWithin_takenStripPure2 hbltu_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact ((sepConj_pure_right _).mp h_rest).2 hoob)
  -- +96 .. +108 zero arm
  have hsd0 := sd_x0_spec_gen_within .x12 nsp i0 0 (base + 96)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hsd1 := sd_x0_spec_gen_within .x12 nsp i1 8 (base + 100)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hsd2 := sd_x0_spec_gen_within .x12 nsp i2 16 (base + 104)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hsd3 := sd_x0_spec_gen_within .x12 nsp i3 24 (base + 108)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hld0 hldc hbgeu hsuba hldcnt hbltu
    hsd0 hsd1 hsd2 hsd3

/-- Valid table-read path: all high limbs zero, `i0 <u cur`, and
    `¬ count <u cur - i0` (the age is within the loaded window). The four
    table-entry cells at `tblAddr + ((count - (cur - i0)) <<< 5) + {0,8,16,24}`
    are copied to the stack top; `tableBaseReg` is clobbered to the entry
    address, `tgtReg` to the age `cur - i0`, and `tmpReg` to the byte offset
    `(count - (cur - i0)) <<< 5`. -/
theorem evm_blockhash_valid_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htbl : tableBaseReg ≠ .x0) (htgt : tgtReg ≠ .x0)
    (htmp : tmpReg ≠ .x0) (hval : valReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (i0 i1 i2 i3 cur count v0 v1 v2 v3 : Word)
    (hz1 : i1 = 0) (hz2 : i2 = 0) (hz3 : i3 = 0)
    (hlt : BitVec.ult i0 cur)
    (hge : ¬ BitVec.ult count (cur - i0)) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 24 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ i0) ** ((nsp + 8) ↦ₘ i1) **
       ((nsp + 16) ↦ₘ i2) ** ((nsp + 24) ↦ₘ i3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
       ((tblAddr + ((count - (cur - i0)) <<< 5)) ↦ₘ v0) **
       ((tblAddr + ((count - (cur - i0)) <<< 5) + 8) ↦ₘ v1) **
       ((tblAddr + ((count - (cur - i0)) <<< 5) + 16) ↦ₘ v2) **
       ((tblAddr + ((count - (cur - i0)) <<< 5) + 24) ↦ₘ v3))
      ((tableBaseReg ↦ᵣ (tblAddr + ((count - (cur - i0)) <<< 5))) **
       (tgtReg ↦ᵣ (cur - i0)) **
       (tmpReg ↦ᵣ ((count - (cur - i0)) <<< 5)) ** (valReg ↦ᵣ v3) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ v0) ** ((nsp + 8) ↦ₘ v1) **
       ((nsp + 16) ↦ₘ v2) ** ((nsp + 24) ↦ₘ v3) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
       ((tblAddr + ((count - (cur - i0)) <<< 5)) ↦ₘ v0) **
       ((tblAddr + ((count - (cur - i0)) <<< 5) + 8) ↦ₘ v1) **
       ((tblAddr + ((count - (cur - i0)) <<< 5) + 16) ↦ₘ v2) **
       ((tblAddr + ((count - (cur - i0)) <<< 5) + 24) ↦ₘ v3)) := by
  -- +0 LD limb 1; +4 BNE not taken
  have hld1 := ld_spec_gen_within tmpReg .x12 nsp tmpOld i1 8 base htmp
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hld1
  have hbne1_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 92) i1 (0 : Word) (base + 4)
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at hbne1_raw
  have hbne1 := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz1)
  -- +8 LD limb 2; +12 BNE not taken
  have hld2 := ld_spec_gen_within tmpReg .x12 nsp i1 i2 16 (base + 8) htmp
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hld2
  have hbne2_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 84) i2 (0 : Word) (base + 12)
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at hbne2_raw
  have hbne2 := cpsBranchWithin_ntakenStripPure2 hbne2_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz2)
  -- +16 LD limb 3; +20 BNE not taken
  have hld3 := ld_spec_gen_within tmpReg .x12 nsp i2 i3 24 (base + 16) htmp
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hld3
  have hbne3_raw := bne_spec_gen_within tmpReg .x0 (BitVec.ofNat 13 76) i3 (0 : Word) (base + 20)
  rw [show (base + 20 : Word) + 4 = base + 24 from by bv_omega] at hbne3_raw
  have hbne3 := cpsBranchWithin_ntakenStripPure2 hbne3_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hz3)
  -- +24 LD target; +28 LD cur; +32 BGEU not taken
  have hld0 := ld_spec_gen_within tgtReg .x12 nsp tgtOld i0 0 (base + 24) htgt
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hld0
  have hldc := ld_spec_gen_within tmpReg envBaseReg envAddr i3 cur
    (BitVec.ofNat 12 blockNumberOff) (base + 28) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blockNumberOff)
        = BitVec.ofNat 64 blockNumberOff from
        signExtend12_ofNat_small (by decide)] at hldc
  have hbgeu_raw := bgeu_spec_gen_within tgtReg tmpReg (BitVec.ofNat 13 64) i0 cur (base + 32)
  rw [show (base + 32 : Word) + 4 = base + 36 from by bv_omega] at hbgeu_raw
  have hbgeu := cpsBranchWithin_ntakenStripPure2 hbgeu_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact ((sepConj_pure_right _).mp h_rest).2 hlt)
  -- +36 SUB tgtReg tmpReg tgtReg (rd = rs2): tgtReg := age = cur - i0
  have hsuba := sub_spec_gen_rd_eq_rs2_within tgtReg tmpReg cur i0 (base + 36) htgt
  -- +40 LD tmpReg envBaseReg 560 (count); +44 BLTU not taken
  have hldcnt := ld_spec_gen_within tmpReg envBaseReg envAddr cur count
    (BitVec.ofNat 12 blockHashCountOff) (base + 40) htmp
  rw [show signExtend12 (BitVec.ofNat 12 blockHashCountOff)
        = BitVec.ofNat 64 blockHashCountOff from
        signExtend12_ofNat_small (by decide)] at hldcnt
  have hbltu_raw := bltu_spec_gen_within tmpReg tgtReg (BitVec.ofNat 13 52) count (cur - i0)
    (base + 44)
  rw [show (base + 44 : Word) + 4 = base + 48 from by bv_omega] at hbltu_raw
  have hbltu := cpsBranchWithin_ntakenStripPure2 hbltu_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact hge ((sepConj_pure_right _).mp h_rest).2)
  -- +48 SUB tmpReg tmpReg tgtReg (rd = rs1): tmpReg := index = count - age
  have hsubi := sub_spec_gen_rd_eq_rs1_within tmpReg tgtReg count (cur - i0) (base + 48) htmp
  -- +52 SLLI tmpReg tmpReg 5 (32-byte entry stride)
  have hslli := slli_spec_gen_same_within tmpReg (count - (cur - i0)) 5 (base + 52) htmp
  rw [show ((5 : BitVec 6)).toNat = 5 from rfl] at hslli
  -- +56 ADD tableBaseReg tableBaseReg tmpReg (entry address)
  have hadd := add_spec_gen_rd_eq_rs1_within tableBaseReg tmpReg tblAddr
    ((count - (cur - i0)) <<< 5) (base + 56) htbl
  -- +60 .. +88 copy the four entry limbs to the stack top
  have hldv0 := ld_spec_gen_within valReg tableBaseReg (tblAddr + ((count - (cur - i0)) <<< 5))
    valOld v0 0 (base + 60) hval
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show ((tblAddr + ((count - (cur - i0)) <<< 5)) + 0 : Word)
        = tblAddr + ((count - (cur - i0)) <<< 5) from by bv_omega] at hldv0
  have hsd0 := sd_spec_gen_within .x12 valReg nsp v0 i0 0 (base + 64)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (nsp + 0 : Word) = nsp from by bv_omega] at hsd0
  have hldv1 := ld_spec_gen_within valReg tableBaseReg (tblAddr + ((count - (cur - i0)) <<< 5))
    v0 v1 8 (base + 68) hval
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show ((tblAddr + ((count - (cur - i0)) <<< 5)) + BitVec.ofNat 64 8 : Word)
        = tblAddr + ((count - (cur - i0)) <<< 5) + 8 from by bv_omega] at hldv1
  have hsd1 := sd_spec_gen_within .x12 valReg nsp v1 i1 8 (base + 72)
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      show (nsp + BitVec.ofNat 64 8 : Word) = nsp + 8 from by bv_omega] at hsd1
  have hldv2 := ld_spec_gen_within valReg tableBaseReg (tblAddr + ((count - (cur - i0)) <<< 5))
    v1 v2 16 (base + 76) hval
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show ((tblAddr + ((count - (cur - i0)) <<< 5)) + BitVec.ofNat 64 16 : Word)
        = tblAddr + ((count - (cur - i0)) <<< 5) + 16 from by bv_omega] at hldv2
  have hsd2 := sd_spec_gen_within .x12 valReg nsp v2 i2 16 (base + 80)
  rw [show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from by decide,
      show (nsp + BitVec.ofNat 64 16 : Word) = nsp + 16 from by bv_omega] at hsd2
  have hldv3 := ld_spec_gen_within valReg tableBaseReg (tblAddr + ((count - (cur - i0)) <<< 5))
    v2 v3 24 (base + 84) hval
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show ((tblAddr + ((count - (cur - i0)) <<< 5)) + BitVec.ofNat 64 24 : Word)
        = tblAddr + ((count - (cur - i0)) <<< 5) + 24 from by bv_omega] at hldv3
  have hsd3 := sd_spec_gen_within .x12 valReg nsp v3 i3 24 (base + 88)
  rw [show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from by decide,
      show (nsp + BitVec.ofNat 64 24 : Word) = nsp + 24 from by bv_omega] at hsd3
  -- +92 JAL x0 +20 over the zero arm → base + 112
  have hjal := jal_x0_spec_gen_within (BitVec.ofNat 21 20) (base + 92)
  rw [show signExtend21 (BitVec.ofNat 21 20) = BitVec.ofNat 64 20 from by decide,
      show (base + 92 : Word) + BitVec.ofNat 64 20 = base + 112 from by bv_omega] at hjal
  runBlock hld1 hbne1 hld2 hbne2 hld3 hbne3 hld0 hldc hbgeu hsuba hldcnt hbltu
    hsubi hslli hadd hldv0 hsd0 hldv1 hsd1 hldv2 hsd2 hldv3 hsd3 hjal

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

/-- **BLOCKHASH stack spec** (the `.proven` witness): pops the target block
    number `w` and pushes, in place at the stack top (`x12` unchanged),
    `hashes[count - (cur - w)]` when `w` has zero high limbs, `w <u cur`, and
    the age `cur - w` is within the loaded window (`¬ count <u cur - w`), and
    `0` otherwise — as a single merged if-then-else postcondition.
    Unconditional over all inputs: the only hypotheses are register shape
    conditions (scratch registers distinct from `x0`) and the
    dispatcher-guaranteed table shape `count.toNat ≤ hashes.length` (the
    guards force `1 ≤ (cur - w.getLimbN 0).toNat ≤ count.toNat`, so the
    `getD` index is strictly below `hashes.length` on the valid path). The
    scratch registers (`tableBaseReg`, `tgtReg`, `tmpReg`, `valReg`) end
    clobbered (`regOwn`); the two env cells (`cur` at
    `envAddr + blockNumberOff`, `count` at `envAddr + blockHashCountOff`)
    and the hash table are framed. -/
theorem evm_blockhash_stack_spec_within
    (envBaseReg tableBaseReg tgtReg tmpReg valReg : Reg)
    (htbl : tableBaseReg ≠ .x0) (htgt : tgtReg ≠ .x0)
    (htmp : tmpReg ≠ .x0) (hval : valReg ≠ .x0)
    (nsp base envAddr tblAddr tgtOld tmpOld valOld : Word)
    (w : EvmWord) (cur count : Word) (hashes : List EvmWord) (rest : List EvmWord)
    (hcount : count.toNat ≤ hashes.length) :
    let code := evm_blockhash_code envBaseReg tableBaseReg tgtReg tmpReg valReg base
    cpsTripleWithin 24 base (base + 112) code
      ((tableBaseReg ↦ᵣ tblAddr) ** (tgtReg ↦ᵣ tgtOld) **
       (tmpReg ↦ᵣ tmpOld) ** (valReg ↦ᵣ valOld) **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp (w :: rest) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
       evmStackIs tblAddr hashes)
      (regOwn tableBaseReg ** regOwn tgtReg ** regOwn tmpReg ** regOwn valReg **
       (envBaseReg ↦ᵣ envAddr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ nsp) **
       evmStackIs nsp
         ((if w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
              BitVec.ult (w.getLimbN 0) cur ∧
              ¬ BitVec.ult count (cur - w.getLimbN 0)
           then hashes.getD (count - (cur - w.getLimbN 0)).toNat 0 else 0) :: rest) **
       ((envAddr + BitVec.ofNat 64 blockNumberOff) ↦ₘ cur) **
       ((envAddr + BitVec.ofNat 64 blockHashCountOff) ↦ₘ count) **
       evmStackIs tblAddr hashes) := by
  intro code
  by_cases hc : w.getLimbN 1 = 0 ∧ w.getLimbN 2 = 0 ∧ w.getLimbN 3 = 0 ∧
      BitVec.ult (w.getLimbN 0) cur ∧ ¬ BitVec.ult count (cur - w.getLimbN 0)
  · -- Valid path: table read.
    rw [if_pos hc]
    obtain ⟨hz1, hz2, hz3, hlt, hge⟩ := hc
    -- The guards force the getD index below the table length:
    -- `1 ≤ age.toNat ≤ count.toNat` with `age = cur - w.getLimbN 0`, so
    -- `(count - age).toNat = count.toNat - age.toNat < count.toNat ≤ len`.
    have hltn : (w.getLimbN 0).toNat < cur.toNat := by
      have h := hlt
      rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
      exact h
    have hagen : (cur - w.getLimbN 0).toNat = cur.toNat - (w.getLimbN 0).toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    have hgen : (cur - w.getLimbN 0).toNat ≤ count.toNat := by
      have h := hge
      rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
      omega
    have hidxn : (count - (cur - w.getLimbN 0)).toNat
        = count.toNat - (cur - w.getLimbN 0).toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr hgen)
    have hklt : (count - (cur - w.getLimbN 0)).toNat < hashes.length := by omega
    -- The stack top becomes the table entry.
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt, Option.getD_some]
    -- Byte offset of entry k: `32 * k = idx <<< 5` (modulo `2^64`).
    have hshift : BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32)
        = (count - (cur - w.getLimbN 0)) <<< 5 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    -- Split the table at entry k.
    have hsplit := evmStackIs_split_at tblAddr hashes
      (count - (cur - w.getLimbN 0)).toNat hklt
    refine cpsTripleWithin_weaken
      (fun h hp => ?_) (fun h hq => ?_)
      (cpsTripleWithin_frameR
        (evmStackIs (nsp + 32) rest **
         evmStackIs tblAddr (hashes.take (count - (cur - w.getLimbN 0)).toNat) **
         evmStackIs
           (tblAddr + BitVec.ofNat 64 (((count - (cur - w.getLimbN 0)).toNat + 1) * 32))
           (hashes.drop ((count - (cur - w.getLimbN 0)).toNat + 1)))
        (pcFree_sepConj pcFree_evmStackIs
          (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs))
        (evm_blockhash_valid_spec_within envBaseReg tableBaseReg tgtReg tmpReg valReg
          htbl htgt htmp hval nsp base envAddr tblAddr tgtOld tmpOld valOld
          (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) cur count
          ((hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 0)
          ((hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 1)
          ((hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 2)
          ((hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 3)
          hz1 hz2 hz3 hlt hge))
    · -- Pre: unfold the stack word and split the table.
      rw [evmStackIs_cons,
          show evmWordIs nsp w
              = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                 ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl,
          hsplit,
          show evmWordIs
                (tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32))
                (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt)
              = (((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32)) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 0) **
                 ((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32) + 8) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 1) **
                 ((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32) + 16) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 2) **
                 ((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32) + 24) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 3)) from rfl,
          hshift] at hp
      xperm_hyp hp
    · -- Post: fold the stack word and reassemble the table, then weaken the
      -- scratch registers to regOwn (via sepConj_own4 on the framed core post).
      rw [evmStackIs_cons,
          show evmWordIs nsp (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt)
              = ((nsp ↦ₘ (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 0) **
                 ((nsp + 8) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 1) **
                 ((nsp + 16) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 2) **
                 ((nsp + 24) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 3)) from rfl,
          hsplit,
          show evmWordIs
                (tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32))
                (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt)
              = (((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32)) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 0) **
                 ((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32) + 8) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 1) **
                 ((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32) + 16) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 2) **
                 ((tblAddr + BitVec.ofNat 64 ((count - (cur - w.getLimbN 0)).toNat * 32) + 24) ↦ₘ
                    (hashes[(count - (cur - w.getLimbN 0)).toNat]'hklt).getLimbN 3)) from rfl,
          hshift]
      have hq' := sepConj_mono_left
        (sepConj_own4 (r1 := tableBaseReg) (r2 := tgtReg) (r3 := tmpReg) (r4 := valReg))
        h hq
      xperm_hyp hq'
  · -- Zero paths: dispatch on which guard fires.
    rw [if_neg hc]
    by_cases hz1 : w.getLimbN 1 = 0
    · by_cases hz2 : w.getLimbN 2 = 0
      · by_cases hz3 : w.getLimbN 3 = 0
        · by_cases hlt : BitVec.ult (w.getLimbN 0) cur
          · -- BLTU guard: high limbs zero, target in the past, but too old.
            have hoob : BitVec.ult count (cur - w.getLimbN 0) := by
              by_contra hgeu
              exact hc ⟨hz1, hz2, hz3, hlt, hgeu⟩
            refine cpsTripleWithin_weaken
              (fun h hp => ?_) (fun h hq => ?_)
              (cpsTripleWithin_frameR
                (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
                (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
                (cpsTripleWithin_mono_nSteps (by omega)
                  (evm_blockhash_zero_ancient_spec_within envBaseReg tableBaseReg tgtReg
                    tmpReg valReg htmp htgt nsp base envAddr tblAddr tgtOld tmpOld valOld
                    (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) cur count
                    hz1 hz2 hz3 hlt hoob)))
            · rw [evmStackIs_cons,
                  show evmWordIs nsp w
                      = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                         ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
              xperm_hyp hp
            · rw [evmStackIs_cons, evmWordIs_zero]
              have hq' := sepConj_mono_left
                (sepConj_own4 (r1 := tableBaseReg) (r2 := tgtReg) (r3 := tmpReg) (r4 := valReg))
                h hq
              xperm_hyp hq'
          · -- BGEU guard: high limbs zero but target ≥ cur.
            refine cpsTripleWithin_weaken
              (fun h hp => ?_) (fun h hq => ?_)
              (cpsTripleWithin_frameR
                (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
                (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
                (cpsTripleWithin_mono_nSteps (by omega)
                  (evm_blockhash_zero_future_spec_within envBaseReg tableBaseReg tgtReg
                    tmpReg valReg htmp htgt nsp base envAddr tblAddr tgtOld tmpOld valOld
                    (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) cur count
                    hz1 hz2 hz3 hlt)))
            · rw [evmStackIs_cons,
                  show evmWordIs nsp w
                      = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                         ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
              xperm_hyp hp
            · rw [evmStackIs_cons, evmWordIs_zero]
              have hq' := sepConj_mono_left
                (sepConj_own4 (r1 := tableBaseReg) (r2 := tgtReg) (r3 := tmpReg) (r4 := valReg))
                h hq
              xperm_hyp hq'
        · -- Third high-limb guard.
          refine cpsTripleWithin_weaken
            (fun h hp => ?_) (fun h hq => ?_)
            (cpsTripleWithin_frameR
              (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
              (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
              (cpsTripleWithin_mono_nSteps (by omega)
                (evm_blockhash_zero_high3_spec_within envBaseReg tableBaseReg tgtReg
                  tmpReg valReg htmp nsp base envAddr tblAddr tgtOld tmpOld valOld
                  (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) cur count
                  hz1 hz2 hz3)))
          · rw [evmStackIs_cons,
                show evmWordIs nsp w
                    = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                       ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
            xperm_hyp hp
          · rw [evmStackIs_cons, evmWordIs_zero]
            have hq' := sepConj_mono_left
              (sepConj_own4 (r1 := tableBaseReg) (r2 := tgtReg) (r3 := tmpReg) (r4 := valReg))
              h hq
            xperm_hyp hq'
      · -- Second high-limb guard.
        refine cpsTripleWithin_weaken
          (fun h hp => ?_) (fun h hq => ?_)
          (cpsTripleWithin_frameR
            (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
            (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
            (cpsTripleWithin_mono_nSteps (by omega)
              (evm_blockhash_zero_high2_spec_within envBaseReg tableBaseReg tgtReg
                tmpReg valReg htmp nsp base envAddr tblAddr tgtOld tmpOld valOld
                (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) cur count
                hz1 hz2)))
        · rw [evmStackIs_cons,
              show evmWordIs nsp w
                  = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                     ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
          xperm_hyp hp
        · rw [evmStackIs_cons, evmWordIs_zero]
          have hq' := sepConj_mono_left
            (sepConj_own4 (r1 := tableBaseReg) (r2 := tgtReg) (r3 := tmpReg) (r4 := valReg))
            h hq
          xperm_hyp hq'
    · -- First high-limb guard.
      refine cpsTripleWithin_weaken
        (fun h hp => ?_) (fun h hq => ?_)
        (cpsTripleWithin_frameR
          (evmStackIs (nsp + 32) rest ** evmStackIs tblAddr hashes)
          (pcFree_sepConj pcFree_evmStackIs pcFree_evmStackIs)
          (cpsTripleWithin_mono_nSteps (by omega)
            (evm_blockhash_zero_high1_spec_within envBaseReg tableBaseReg tgtReg
              tmpReg valReg htmp nsp base envAddr tblAddr tgtOld tmpOld valOld
              (w.getLimbN 0) (w.getLimbN 1) (w.getLimbN 2) (w.getLimbN 3) cur count
              hz1)))
      · rw [evmStackIs_cons,
            show evmWordIs nsp w
                = ((nsp ↦ₘ w.getLimbN 0) ** ((nsp + 8) ↦ₘ w.getLimbN 1) **
                   ((nsp + 16) ↦ₘ w.getLimbN 2) ** ((nsp + 24) ↦ₘ w.getLimbN 3)) from rfl] at hp
        xperm_hyp hp
      · rw [evmStackIs_cons, evmWordIs_zero]
        have hq' := sepConj_mono_left
          (sepConj_own4 (r1 := tableBaseReg) (r2 := tgtReg) (r3 := tmpReg) (r4 := valReg))
          h hq
        xperm_hyp hq'

-- #print axioms evm_blockhash_stack_spec_within
--   (and all six per-path cores): [propext, Classical.choice, Quot.sound]

end BlockHash
end EvmAsm.Evm64
