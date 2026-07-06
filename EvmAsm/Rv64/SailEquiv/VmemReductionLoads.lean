/-
  EvmAsm.Rv64.SailEquiv.VmemReductionLoads

  Unconditional per-instruction equivalence for the six sub-doubleword loads
  `LW / LWU / LH / LHU / LB / LBU`, discharging the `h_exec` hypotheses the original
  `MemProofs` lemmas carried.  Built on the width-N reduction chain in `VmemReductionN`
  (`readBytesN_raw → … → vmem_read_load_N`) and the read bridges
  (`extractWord32/Halfword/Byte_recon`), plus the alignment plumbing below that ties the
  toy `getWord32/Halfword/Byte` (`alignToDword`/`byteOffset`) to the access address.

  Mirrors the Tier-A `ld_sail_equiv` discharge in `VmemReduction.lean`; the only new work
  is the real sign/zero `extend_value` (for LD width 8 it was the identity).
-/

import EvmAsm.Rv64.SailEquiv.VmemReductionN
import EvmAsm.Rv64.ByteOps

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Alignment plumbing
-- ============================================================================

/-- The aligned base plus the byte offset reconstructs the original address, in `Nat` form.
    Disjoint-bit decomposition (proved WITHOUT `bv_decide`): the aligned base holds the high
    bits (`addr.toNat / 8 * 8`), the byte offset the low 3 bits (`addr.toNat % 8`).
    (Lived in `ByteOps.lean` before the toy-model files were evolved upstream; its only
    consumers are the SailEquiv load bridges below.) -/
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

/-- Aligned base + the rounded byte offset reconstructs the access address (Nat form).
    For a `w`-aligned address (`w ∈ {1,2,4}`), `(byteOffset addr / w) * w = byteOffset addr`. -/
theorem alignToDword_offset_eq (addr : Word) (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4)
    (halign : addr.toNat % w = 0) :
    (alignToDword addr).toNat + (byteOffset addr / w) * w = addr.toNat := by
  have hbo_eq : byteOffset addr = addr.toNat % 8 := by
    unfold byteOffset
    rw [BitVec.toNat_and]
    have h7 : (7#64).toNat = 7 := by decide
    rw [h7]
    have key := Nat.and_two_pow_sub_one_eq_mod addr.toNat 3
    simp only [show (2:Nat)^3 = 8 from rfl] at key
    exact key
  have hnat_eq : (alignToDword addr).toNat + byteOffset addr = addr.toNat :=
    alignToDword_add_byteOffset_toNat addr
  rcases hw with rfl | rfl | rfl <;> omega

/-- A `w`-aligned virtual address has `addr.toNat % w = 0`. -/
theorem is_aligned_vaddr_toNat (addr : Word) (w : Nat)
    (h : is_aligned_vaddr (virtaddr.Virtaddr addr) w = true) : addr.toNat % w = 0 := by
  unfold is_aligned_vaddr Sail.BitVec.toNatInt at h
  rw [beq_iff_eq] at h
  have h2 : (Int.ofNat (addr.toNat % w)) = Int.ofNat 0 := h
  exact Int.ofNat_inj.mp h2

/-- The dword-aligned base is 8-aligned in `Nat` form — discharges the alignment
    hypothesis of `StateRel.mem_agree` at `alignToDword` addresses. -/
theorem alignToDword_toNat_mod8 (addr : Word) : (alignToDword addr).toNat % 8 = 0 := by
  have h := alignToDword_byteOffset_zero addr
  unfold byteOffset at h
  rw [BitVec.toNat_and, show (7#64).toNat = 7 from rfl] at h
  have key : (alignToDword addr).toNat &&& 7 = (alignToDword addr).toNat % 8 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod (alignToDword addr).toNat 3
  rw [← key]; exact h

-- ============================================================================
-- Word loads (LW / LWU), width 4
-- ============================================================================

/-- **`lw_sail_equiv` discharged.** Bare-mode aligned readable word load: the SAIL
    `execute_LOAD` (width 4, signed) succeeds and the post-state is `StateRel`-related to
    the toy `LW` (sign-extended 32-bit word). -/
theorem lw_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 b1 b2 b3 : BitVec 8)
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
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0)
    (hm1 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1)
    (hm2 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+2) = some b2)
    (hm3 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+3) = some b3) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LW rd rs1 offset)) sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hread : (readBytes 4 (bits_of_virtaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))).toNat
      : SailM ((BitVec (8*4)) × Option Bool)) sSail
      = .ok (((b3.append b2).append b1).append b0, none) sSail := by
    simpa using readBytes4_raw sSail (sRv.getReg rs1 + signExtend12 offset).toNat
      b0 b1 b2 b3 hm0 hm1 hm2 hm3
  have hvra := vmem_read_addr_load_core 4 (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))
    sSail bm.mst (((b3.append b2).append b1).append b0)
    bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inr rfl))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif) hread
  have hvr := vmem_read_load_N 4 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    (((b3.append b2).append b1).append b0) bm h_rs (by simpa using hvra)
  have hbridge : sRv.getWord32 (sRv.getReg rs1 + signExtend12 offset)
      = ((b3.append b2).append b1).append b0 := by
    simp only [MachineState.getWord32]
    rw [← hrel.mem_agree (alignToDword (sRv.getReg rs1 + signExtend12 offset))
          (alignToDword_toNat_mod8 _)]
    have hpos : byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 < 2 := by
      have := byteOffset_lt_8 (addr := sRv.getReg rs1 + signExtend12 offset); omega
    have hbase : (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
        + (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4) * 4
        = (sRv.getReg rs1 + signExtend12 offset).toNat :=
      alignToDword_offset_eq _ 4 (Or.inr (Or.inr rfl))
        (is_aligned_vaddr_toNat _ 4 h_valign)
    apply extractWord32_recon sSail.mem
      (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
      (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4) b0 b1 b2 b3 hpos
    · rw [hbase, Std.ExtHashMap.getD_eq_getD_getElem?,
        ← Std.ExtHashMap.get?_eq_getElem?, hm0]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 * 4 + 1
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 1 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm1]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 * 4 + 2
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 2 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm2]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 * 4 + 3
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 3 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm3]; rfl
  refine ⟨sailStateWithReg sSail rd
      ((sRv.getWord32 (sRv.getReg rs1 + signExtend12 offset)).signExtend 64), ?_, ?_⟩
  · unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 4
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok (((b3.append b2).append b1).append b0), sSail) from by
      simp only [runSail, hvr]]
    simp only [extend_value, Bool.false_eq_true, if_false, sign_extend,
      Sail.BitVec.signExtend, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure, hbridge]
  · refine ⟨fun r => ?_, fun a ha => ?_⟩
    · simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha

/-- **`lwu_sail_equiv` discharged.** Word load, zero-extended (unsigned). -/
theorem lwu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 b1 b2 b3 : BitVec 8)
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
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 4) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0)
    (hm1 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1)
    (hm2 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+2) = some b2)
    (hm3 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+3) = some b3) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 4) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LWU rd rs1 offset)) sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hread : (readBytes 4 (bits_of_virtaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))).toNat
      : SailM ((BitVec (8*4)) × Option Bool)) sSail
      = .ok (((b3.append b2).append b1).append b0, none) sSail := by
    simpa using readBytes4_raw sSail (sRv.getReg rs1 + signExtend12 offset).toNat
      b0 b1 b2 b3 hm0 hm1 hm2 hm3
  have hvra := vmem_read_addr_load_core 4 (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))
    sSail bm.mst (((b3.append b2).append b1).append b0)
    bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inr rfl))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif) hread
  have hvr := vmem_read_load_N 4 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    (((b3.append b2).append b1).append b0) bm h_rs (by simpa using hvra)
  have hbridge : sRv.getWord32 (sRv.getReg rs1 + signExtend12 offset)
      = ((b3.append b2).append b1).append b0 := by
    simp only [MachineState.getWord32]
    rw [← hrel.mem_agree (alignToDword (sRv.getReg rs1 + signExtend12 offset))
          (alignToDword_toNat_mod8 _)]
    have hpos : byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 < 2 := by
      have := byteOffset_lt_8 (addr := sRv.getReg rs1 + signExtend12 offset); omega
    have hbase : (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
        + (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4) * 4
        = (sRv.getReg rs1 + signExtend12 offset).toNat :=
      alignToDword_offset_eq _ 4 (Or.inr (Or.inr rfl))
        (is_aligned_vaddr_toNat _ 4 h_valign)
    apply extractWord32_recon sSail.mem
      (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
      (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4) b0 b1 b2 b3 hpos
    · rw [hbase, Std.ExtHashMap.getD_eq_getD_getElem?,
        ← Std.ExtHashMap.get?_eq_getElem?, hm0]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 * 4 + 1
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 1 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm1]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 * 4 + 2
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 2 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm2]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 4 * 4 + 3
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 3 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm3]; rfl
  refine ⟨sailStateWithReg sSail rd
      ((sRv.getWord32 (sRv.getReg rs1 + signExtend12 offset)).zeroExtend 64), ?_, ?_⟩
  · unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 4
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok (((b3.append b2).append b1).append b0), sSail) from by
      simp only [runSail, hvr]]
    simp only [extend_value, if_true, zero_extend, Sail.BitVec.zeroExtend,
      BitVec.zeroExtend_eq_setWidth, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure, hbridge]
  · refine ⟨fun r => ?_, fun a ha => ?_⟩
    · simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha

-- ============================================================================
-- Halfword loads (LH / LHU), width 2
-- ============================================================================

/-- **`lh_sail_equiv` discharged.** Halfword load, sign-extended. -/
theorem lh_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 b1 : BitVec 8)
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
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0)
    (hm1 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LH rd rs1 offset)) sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hread : (readBytes 2 (bits_of_virtaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))).toNat
      : SailM ((BitVec (8*2)) × Option Bool)) sSail
      = .ok (b1.append b0, none) sSail := by
    simpa using readBytes2_raw sSail (sRv.getReg rs1 + signExtend12 offset).toNat b0 b1 hm0 hm1
  have hvra := vmem_read_addr_load_core 2 (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))
    sSail bm.mst (b1.append b0)
    bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inl rfl))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif) hread
  have hvr := vmem_read_load_N 2 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    (b1.append b0) bm h_rs (by simpa using hvra)
  have hbridge : sRv.getHalfword (sRv.getReg rs1 + signExtend12 offset) = b1.append b0 := by
    simp only [MachineState.getHalfword]
    rw [← hrel.mem_agree (alignToDword (sRv.getReg rs1 + signExtend12 offset))
          (alignToDword_toNat_mod8 _)]
    have hpos : byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2 < 4 := by
      have := byteOffset_lt_8 (addr := sRv.getReg rs1 + signExtend12 offset); omega
    have hbase : (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
        + (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2) * 2
        = (sRv.getReg rs1 + signExtend12 offset).toNat :=
      alignToDword_offset_eq _ 2 (Or.inr (Or.inl rfl))
        (is_aligned_vaddr_toNat _ 2 h_valign)
    apply extractHalfword_recon sSail.mem
      (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
      (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2) b0 b1 hpos
    · rw [hbase, Std.ExtHashMap.getD_eq_getD_getElem?,
        ← Std.ExtHashMap.get?_eq_getElem?, hm0]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2 * 2 + 1
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 1 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm1]; rfl
  refine ⟨sailStateWithReg sSail rd
      ((sRv.getHalfword (sRv.getReg rs1 + signExtend12 offset)).signExtend 64), ?_, ?_⟩
  · unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 2
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok (b1.append b0), sSail) from by simp only [runSail, hvr]]
    simp only [extend_value, Bool.false_eq_true, if_false, sign_extend,
      Sail.BitVec.signExtend, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure, hbridge]
  · refine ⟨fun r => ?_, fun a ha => ?_⟩
    · simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha

/-- **`lhu_sail_equiv` discharged.** Halfword load, zero-extended (unsigned). -/
theorem lhu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 b1 : BitVec 8)
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
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 2) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0)
    (hm1 : sSail.mem.get? ((sRv.getReg rs1 + signExtend12 offset).toNat+1) = some b1) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 2) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LHU rd rs1 offset)) sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hread : (readBytes 2 (bits_of_virtaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))).toNat
      : SailM ((BitVec (8*2)) × Option Bool)) sSail
      = .ok (b1.append b0, none) sSail := by
    simpa using readBytes2_raw sSail (sRv.getReg rs1 + signExtend12 offset).toNat b0 b1 hm0 hm1
  have hvra := vmem_read_addr_load_core 2 (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))
    sSail bm.mst (b1.append b0)
    bm.cfgs bm.pmpaddrs bm.regions region (Or.inr (Or.inl rfl))
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif) hread
  have hvr := vmem_read_load_N 2 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    (b1.append b0) bm h_rs (by simpa using hvra)
  have hbridge : sRv.getHalfword (sRv.getReg rs1 + signExtend12 offset) = b1.append b0 := by
    simp only [MachineState.getHalfword]
    rw [← hrel.mem_agree (alignToDword (sRv.getReg rs1 + signExtend12 offset))
          (alignToDword_toNat_mod8 _)]
    have hpos : byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2 < 4 := by
      have := byteOffset_lt_8 (addr := sRv.getReg rs1 + signExtend12 offset); omega
    have hbase : (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
        + (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2) * 2
        = (sRv.getReg rs1 + signExtend12 offset).toNat :=
      alignToDword_offset_eq _ 2 (Or.inr (Or.inl rfl))
        (is_aligned_vaddr_toNat _ 2 h_valign)
    apply extractHalfword_recon sSail.mem
      (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
      (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2) b0 b1 hpos
    · rw [hbase, Std.ExtHashMap.getD_eq_getD_getElem?,
        ← Std.ExtHashMap.get?_eq_getElem?, hm0]; rfl
    · rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
            + byteOffset (sRv.getReg rs1 + signExtend12 offset) / 2 * 2 + 1
          = (sRv.getReg rs1 + signExtend12 offset).toNat + 1 from by omega,
        Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm1]; rfl
  refine ⟨sailStateWithReg sSail rd
      ((sRv.getHalfword (sRv.getReg rs1 + signExtend12 offset)).zeroExtend 64), ?_, ?_⟩
  · unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 2
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok (b1.append b0), sSail) from by simp only [runSail, hvr]]
    simp only [extend_value, if_true, zero_extend, Sail.BitVec.zeroExtend,
      BitVec.zeroExtend_eq_setWidth, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure, hbridge]
  · refine ⟨fun r => ?_, fun a ha => ?_⟩
    · simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha

-- ============================================================================
-- Byte loads (LB / LBU), width 1
-- ============================================================================

/-- **`lb_sail_equiv` discharged.** Byte load, sign-extended. -/
theorem lb_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 : BitVec 8)
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
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) false 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LB rd rs1 offset)) sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hread : (readBytes 1 (bits_of_virtaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))).toNat
      : SailM ((BitVec (8*1)) × Option Bool)) sSail
      = .ok (b0, none) sSail := by
    simpa using readBytes1_raw sSail (sRv.getReg rs1 + signExtend12 offset).toNat b0 hm0
  have hvra := vmem_read_addr_load_core 1 (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))
    sSail bm.mst b0
    bm.cfgs bm.pmpaddrs bm.regions region (Or.inl rfl)
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif) hread
  have hvr := vmem_read_load_N 1 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    b0 bm h_rs (by simpa using hvra)
  have hbridge : sRv.getByte (sRv.getReg rs1 + signExtend12 offset) = b0 := by
    simp only [MachineState.getByte]
    rw [← hrel.mem_agree (alignToDword (sRv.getReg rs1 + signExtend12 offset))
          (alignToDword_toNat_mod8 _)]
    have hbase : (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
        + (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 1) * 1
        = (sRv.getReg rs1 + signExtend12 offset).toNat :=
      alignToDword_offset_eq _ 1 (Or.inl rfl) (is_aligned_vaddr_toNat _ 1 h_valign)
    apply extractByte_recon sSail.mem
      (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
      (byteOffset (sRv.getReg rs1 + signExtend12 offset)) b0
      (byteOffset_lt_8 (addr := sRv.getReg rs1 + signExtend12 offset))
    rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
          + byteOffset (sRv.getReg rs1 + signExtend12 offset)
        = (sRv.getReg rs1 + signExtend12 offset).toNat from by omega,
      Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm0]; rfl
  refine ⟨sailStateWithReg sSail rd
      ((sRv.getByte (sRv.getReg rs1 + signExtend12 offset)).signExtend 64), ?_, ?_⟩
  · unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 1
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok b0, sSail) from by simp only [runSail, hvr]]
    simp only [extend_value, Bool.false_eq_true, if_false, sign_extend,
      Sail.BitVec.signExtend, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure, hbridge]
  · refine ⟨fun r => ?_, fun a ha => ?_⟩
    · simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha

/-- **`lbu_sail_equiv` discharged.** Byte load, zero-extended (unsigned). -/
theorem lbu_sail_equiv (sRv : MachineState) (sSail : SailState)
    (rd rs1 : Reg) (offset : BitVec 12)
    (hrel : StateRel sRv sSail) (bm : BareModeInv sSail) (region : PMA_Region)
    (b0 : BitVec 8)
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
    (hhtif : (within_htif_readable (physaddr.Physaddr (sRv.getReg rs1 + signExtend12 offset)) 1) sSail
      = .ok false sSail)
    (hm0 : sSail.mem.get? (sRv.getReg rs1 + signExtend12 offset).toNat = some b0) :
    ∃ sSail',
      runSail (execute_LOAD offset (regToRegidx rs1) (regToRegidx rd) true 1) sSail
        = some (RETIRE_SUCCESS, sSail') ∧
      StateRel (execInstrBr sRv (.LBU rd rs1 offset)) sSail' := by
  have soff : sign_extend (m := 64) offset = signExtend12 offset := by
    unfold sign_extend signExtend12 Sail.BitVec.signExtend; rfl
  have h_rs : (rX_bits (regToRegidx rs1)) sSail = .ok (sRv.getReg rs1) sSail :=
    runSail_eq_ok (runSail_rX_bits_of_stateRel hrel rs1)
  have hread : (readBytes 1 (bits_of_virtaddr
      (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))).toNat
      : SailM ((BitVec (8*1)) × Option Bool)) sSail
      = .ok (b0, none) sSail := by
    simpa using readBytes1_raw sSail (sRv.getReg rs1 + signExtend12 offset).toNat b0 hm0
  have hvra := vmem_read_addr_load_core 1 (virtaddr.Virtaddr (sRv.getReg rs1 + signExtend12 offset))
    sSail bm.mst b0
    bm.cfgs bm.pmpaddrs bm.regions region (Or.inl rfl)
    h_valign bm.h_priv bm.h_mst bm.h_mprv bm.h_cfg bm.h_pmpaddr bm.h_off bm.h_reg
    (by simpa using h_match) h_read (by simpa using h_palign)
    (by simpa using hclint) (by simpa using hsig) (by simpa using hhtif) hread
  have hvr := vmem_read_load_N 1 (regToRegidx rs1) (signExtend12 offset) (sRv.getReg rs1) sSail
    b0 bm h_rs (by simpa using hvra)
  have hbridge : sRv.getByte (sRv.getReg rs1 + signExtend12 offset) = b0 := by
    simp only [MachineState.getByte]
    rw [← hrel.mem_agree (alignToDword (sRv.getReg rs1 + signExtend12 offset))
          (alignToDword_toNat_mod8 _)]
    have hbase : (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
        + (byteOffset (sRv.getReg rs1 + signExtend12 offset) / 1) * 1
        = (sRv.getReg rs1 + signExtend12 offset).toNat :=
      alignToDword_offset_eq _ 1 (Or.inl rfl) (is_aligned_vaddr_toNat _ 1 h_valign)
    apply extractByte_recon sSail.mem
      (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
      (byteOffset (sRv.getReg rs1 + signExtend12 offset)) b0
      (byteOffset_lt_8 (addr := sRv.getReg rs1 + signExtend12 offset))
    rw [show (alignToDword (sRv.getReg rs1 + signExtend12 offset)).toNat
          + byteOffset (sRv.getReg rs1 + signExtend12 offset)
        = (sRv.getReg rs1 + signExtend12 offset).toNat from by omega,
      Std.ExtHashMap.getD_eq_getD_getElem?, ← Std.ExtHashMap.get?_eq_getElem?, hm0]; rfl
  refine ⟨sailStateWithReg sSail rd
      ((sRv.getByte (sRv.getReg rs1 + signExtend12 offset)).zeroExtend 64), ?_, ?_⟩
  · unfold execute_LOAD
    simp +decide only [soff, runSail_bind, runSail_pure, PreSail.assert, if_true]
    rw [show runSail (vmem_read (regToRegidx rs1) (signExtend12 offset) 1
          (MemoryAccessType.Load mem_payload.Data) false false false) sSail
        = some (Result.Ok b0, sSail) from by simp only [runSail, hvr]]
    simp only [extend_value, if_true, zero_extend, Sail.BitVec.zeroExtend,
      BitVec.zeroExtend_eq_setWidth, runSail_bind, runSail_wX_bits_of_reg,
      runSail_pure, hbridge]
  · refine ⟨fun r => ?_, fun a ha => ?_⟩
    · simpa [execInstrBr, MachineState.setPC]
        using reg_agree_after_insert sSail sRv hrel rd _ r
    · simpa [execInstrBr, MachineState.setPC, MachineState.getMem, sailStateWithReg_mem]
        using hrel.mem_agree a ha

end EvmAsm.Rv64.SailEquiv
