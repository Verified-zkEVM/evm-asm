/-
  EvmAsm.Rv64.SailEquiv.VmemPresent

  Presence layer for the SAIL load-equivalence lemmas.

  The seven `*_sail_equiv` load lemmas each take one `hm_k : sSail.mem.get? (a+k) = some b_k`
  hypothesis per accessed byte (8 for `LD`, 4 for `LW`/`LWU`, 2 for `LH`/`LHU`, 1 for
  `LB`/`LBU`), together with the existentially-chosen byte values themselves.  Nothing in
  the codebase derives those: `StateRel.mem_agree` is an equation about `reconstructDword`,
  which uses total `getD` lookups and therefore says nothing about *key presence* — yet SAIL
  `readByte` throws `.OutOfMemoryRange` on a missing key, so presence is exactly what a load
  needs.

  This file closes that gap.  `BytesPresent mem a w` (defined in `StateRel.lean`) is the
  per-access presence predicate; the `BytesPresent.elimN` eliminators below turn it into the
  `w` byte witnesses plus their `get? = some` facts, and the seven `*_of_present` wrappers
  restate each load lemma with the byte binders and `hm_k` hypotheses replaced by a single
  `BytesPresent` argument.  Callers then discharge presence once, from the range-level
  invariant `MemPresent lo hi` via `MemPresent.bytesPresent`, instead of per access.
-/

import EvmAsm.Rv64.SailEquiv.VmemReductionLoads

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Byte-witness eliminators
-- ============================================================================

/-- Eliminate a width-1 presence fact into its byte witness. -/
theorem BytesPresent.elim1 {mem : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (h : BytesPresent mem a 1) :
    ∃ b0 : BitVec 8, mem.get? a = some b0 := by
  have h0 : (mem.get? a).isSome := by simpa using h 0 (by omega)
  exact Option.isSome_iff_exists.mp h0

/-- Eliminate a width-2 presence fact into its two byte witnesses. -/
theorem BytesPresent.elim2 {mem : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (h : BytesPresent mem a 2) :
    ∃ b0 b1 : BitVec 8,
      mem.get? a = some b0 ∧ mem.get? (a+1) = some b1 := by
  have h0 : (mem.get? a).isSome := by simpa using h 0 (by omega)
  have h1 : (mem.get? (a+1)).isSome := h 1 (by omega)
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨b1, hb1⟩ := Option.isSome_iff_exists.mp h1
  exact ⟨b0, b1, hb0, hb1⟩

/-- Eliminate a width-4 presence fact into its four byte witnesses. -/
theorem BytesPresent.elim4 {mem : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (h : BytesPresent mem a 4) :
    ∃ b0 b1 b2 b3 : BitVec 8,
      mem.get? a = some b0 ∧ mem.get? (a+1) = some b1 ∧ mem.get? (a+2) = some b2 ∧
      mem.get? (a+3) = some b3 := by
  have h0 : (mem.get? a).isSome := by simpa using h 0 (by omega)
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨b1, hb1⟩ := Option.isSome_iff_exists.mp (h 1 (by omega))
  obtain ⟨b2, hb2⟩ := Option.isSome_iff_exists.mp (h 2 (by omega))
  obtain ⟨b3, hb3⟩ := Option.isSome_iff_exists.mp (h 3 (by omega))
  exact ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3⟩

/-- Eliminate a width-8 presence fact into its eight byte witnesses. -/
theorem BytesPresent.elim8 {mem : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    (h : BytesPresent mem a 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      mem.get? a = some b0 ∧ mem.get? (a+1) = some b1 ∧ mem.get? (a+2) = some b2 ∧
      mem.get? (a+3) = some b3 ∧ mem.get? (a+4) = some b4 ∧ mem.get? (a+5) = some b5 ∧
      mem.get? (a+6) = some b6 ∧ mem.get? (a+7) = some b7 := by
  have h0 : (mem.get? a).isSome := by simpa using h 0 (by omega)
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨b1, hb1⟩ := Option.isSome_iff_exists.mp (h 1 (by omega))
  obtain ⟨b2, hb2⟩ := Option.isSome_iff_exists.mp (h 2 (by omega))
  obtain ⟨b3, hb3⟩ := Option.isSome_iff_exists.mp (h 3 (by omega))
  obtain ⟨b4, hb4⟩ := Option.isSome_iff_exists.mp (h 4 (by omega))
  obtain ⟨b5, hb5⟩ := Option.isSome_iff_exists.mp (h 5 (by omega))
  obtain ⟨b6, hb6⟩ := Option.isSome_iff_exists.mp (h 6 (by omega))
  obtain ⟨b7, hb7⟩ := Option.isSome_iff_exists.mp (h 7 (by omega))
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩

-- ============================================================================
-- Presence-based load equivalences
-- ============================================================================

/-- **`ld_sail_equiv` from byte presence.** Same statement as `ld_sail_equiv`, with the
    eight byte binders and their `get? = some` hypotheses replaced by a single
    `BytesPresent` fact for the 8-byte access.  Callers get this from a range invariant
    via `MemPresent.bytesPresent`. -/
theorem ld_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 8)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 8) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 8) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LD rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hpres.elim8
  exact ld_sail_equiv sRv sSail rd rs1 offset hrel bm region b0 b1 b2 b3 b4 b5 b6 b7
    h_valign h_match h_read h_palign hclint hsig hhtif h0 h1 h2 h3 h4 h5 h6 h7

/-- **`lw_sail_equiv` from byte presence.** As `lw_sail_equiv`, with the four byte binders
    and their `get? = some` hypotheses replaced by one `BytesPresent` fact. -/
theorem lw_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 4) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LW rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3⟩ := hpres.elim4
  exact lw_sail_equiv sRv sSail rd rs1 offset hrel bm region b0 b1 b2 b3
    h_valign h_match h_read h_palign hclint hsig hhtif h0 h1 h2 h3

/-- **`lwu_sail_equiv` from byte presence.** As `lwu_sail_equiv`, with the four byte binders
    and their `get? = some` hypotheses replaced by one `BytesPresent` fact. -/
theorem lwu_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 4) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LWU rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3⟩ := hpres.elim4
  exact lwu_sail_equiv sRv sSail rd rs1 offset hrel bm region b0 b1 b2 b3
    h_valign h_match h_read h_palign hclint hsig hhtif h0 h1 h2 h3

/-- **`lh_sail_equiv` from byte presence.** As `lh_sail_equiv`, with the two byte binders
    and their `get? = some` hypotheses replaced by one `BytesPresent` fact. -/
theorem lh_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 2) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LH rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, b1, h0, h1⟩ := hpres.elim2
  exact lh_sail_equiv sRv sSail rd rs1 offset hrel bm region b0 b1
    h_valign h_match h_read h_palign hclint hsig hhtif h0 h1

/-- **`lhu_sail_equiv` from byte presence.** As `lhu_sail_equiv`, with the two byte binders
    and their `get? = some` hypotheses replaced by one `BytesPresent` fact. -/
theorem lhu_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 2) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LHU rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, b1, h0, h1⟩ := hpres.elim2
  exact lhu_sail_equiv sRv sSail rd rs1 offset hrel bm region b0 b1
    h_valign h_match h_read h_palign hclint hsig hhtif h0 h1

/-- **`lb_sail_equiv` from byte presence.** As `lb_sail_equiv`, with the byte binder and its
    `get? = some` hypothesis replaced by one `BytesPresent` fact. -/
theorem lb_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 1) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LB rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, h0⟩ := hpres.elim1
  exact lb_sail_equiv sRv sSail rd rs1 offset hrel bm region b0
    h_valign h_match h_read h_palign hclint hsig hhtif h0

/-- **`lbu_sail_equiv` from byte presence.** As `lbu_sail_equiv`, with the byte binder and
    its `get? = some` hypothesis replaced by one `BytesPresent` fact. -/
theorem lbu_sail_equiv_of_present (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (h_valign : is_aligned_vaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true)
    (h_match : matching_pma_region bm.regions
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr
      (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1 = true)
    (hclint : (within_clint (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hsig : (within_sig (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1)
      sSail = .ok false sSail)
    (hpres : BytesPresent sSail.mem (sRv.getReg rs1 + signExtend12 offset).toNat 1) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LBU rd rs1 offset)) sSail' ∧
      sSail'.regs.get? Register.nextPC = sSail.regs.get? Register.nextPC ∧
      PlatformFrame sSail sSail' := by
  obtain ⟨b0, h0⟩ := hpres.elim1
  exact lbu_sail_equiv sRv sSail rd rs1 offset hrel bm region b0
    h_valign h_match h_read h_palign hclint hsig hhtif h0

-- ============================================================================
-- Stores preserve range presence
-- ============================================================================

/-- **A store preserves range byte-presence.** Each `*_sail_equiv` store lemma exports
    `PlatformFrame sSail sSail'` as the last conjunct of its conclusion; a store's effect on
    memory is a pure chain of `Std.ExtHashMap.insert`s, so the frame's `mem_mono` field
    already records that memory only grew.  Presence over any range therefore transports to
    the post-state.

    This is literally `MemPresent.of_frame` specialised to a store's frame conjunct — it
    adds no new content, only a name for the step a caller takes to carry a `MemPresent`
    invariant across a store. -/
theorem memPresent_of_store {lo hi : Nat} {sSail sSail' : SailState}
    (fr : PlatformFrame sSail sSail') (hpres : MemPresent lo hi sSail.mem) :
    MemPresent lo hi sSail'.mem :=
  MemPresent.of_frame fr hpres

end EvmAsm.Rv64.SailEquiv
