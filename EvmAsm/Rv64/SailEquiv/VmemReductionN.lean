/-
  EvmAsm.Rv64.SailEquiv.VmemReductionN

  Width-N (sub-doubleword) generalisation of the Tier-A doubleword-load discharge in
  `VmemReduction.lean`.  Discharges the `h_exec` hypotheses carried by the six
  sub-doubleword loads `LW / LWU / LH / LHU / LB / LBU` (`execute_LOAD` widths 4/2/1).

  The bare-mode reduction chain (`read_ram → checked_mem_read → mem_read →
  vmem_read_addr → vmem_read`) is the *same* as the width-8 case — the PMP/PMA/translate
  leaves in `VmemReduction.lean` are already width-generic and reused verbatim.  Only two
  things are genuinely new:

  * **`reconstructDword_getLsbD` (Lemma A).**  The per-bit characterisation of
    `reconstructDword`: bit `p` is bit `p % 8` of the byte at `base + p / 8`.  This is the
    keystone — from it the width-N read bridge is pure index arithmetic with no case split
    on the byte offset.
  * **The read bridge.**  The little-endian byte assembly that the Sail `readBytes w`
    produces equals `extractWord32/Halfword/Byte` of the toy doubleword at the aligned
    base — i.e. the Sail value the load writes back is exactly the toy's
    `getWord32 / getHalfword / getByte`.
-/

import EvmAsm.Rv64.SailEquiv.VmemReduction

open Out
open Out.Functions
open Sail
open PreSail

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Pure BitVec foundations
-- ============================================================================

/-- **Lemma A — `reconstructDword` per-bit characterisation.** Bit `p` (for `p < 64`) of
    the little-endian doubleword reconstructed from `mem` at `base` is bit `p % 8` of the
    byte stored at `base + p / 8`.  Keystone for the width-N read bridge. -/
theorem reconstructDword_getLsbD (mem : Std.ExtHashMap Nat (BitVec 8)) (base p : Nat)
    (hp : p < 64) :
    (reconstructDword mem base).getLsbD p = (mem.getD (base + p / 8) 0).getLsbD (p % 8) := by
  simp only [reconstructDword, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  -- After simp, the goal has the form:
  --   (decide (p < 64) && getLsbD b0 p || (decide (p < 64) && !decide (p < 8)) && ...
  -- We case-split over the 8 intervals [8k, 8k+8). In interval k:
  --   * terms j > k vanish: decide (p < 8*j) = true, so !decide(p < 8*j) = false
  --   * terms j < k vanish: getLsbD bj (p - 8*j) = false since p - 8*j ≥ 8
  --   * term j = k survives; RHS: p/8 = k, p%8 = p - 8*k
  -- We use `simp` with explicit decidability witnesses derived via `omega`.
  have hp64 : decide (p < 64) = true := by simp [hp]
  rcases Nat.lt_or_ge p 8 with h0 | h0
  · -- [0, 8): byte 0 active; p/8 = 0, p%8 = p
    have hd0 : decide (p < 8) = true := by simp [h0]
    have hd8  : decide (p < 16) = true := by simp; omega
    have hd16 : decide (p < 24) = true := by simp; omega
    have hd24 : decide (p < 32) = true := by simp; omega
    have hd32 : decide (p < 40) = true := by simp; omega
    have hd40 : decide (p < 48) = true := by simp; omega
    have hd48 : decide (p < 56) = true := by simp; omega
    simp only [hp64, hd0, hd8, hd16, hd24, hd32, hd40, hd48,
               Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
    rw [show p / 8 = 0 from Nat.div_eq_of_lt h0, show p % 8 = p from Nat.mod_eq_of_lt h0]
    simp
  rcases Nat.lt_or_ge p 16 with h1 | h1
  · -- [8, 16): byte 1 active; p/8 = 1, p%8 = p - 8
    have hge0  : decide (p < 8) = false := by simp; omega
    have hd8   : decide (p < 16) = true := by simp [h1]
    have hd16  : decide (p < 24) = true := by simp; omega
    have hd24  : decide (p < 32) = true := by simp; omega
    have hd32  : decide (p < 40) = true := by simp; omega
    have hd40  : decide (p < 48) = true := by simp; omega
    have hd48  : decide (p < 56) = true := by simp; omega
    have hd_s  : decide (p - 8 < 64) = true := by simp; omega
    simp only [hp64, hge0, hd8, hd16, hd24, hd32, hd40, hd48, hd_s,
               Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and,
               Bool.or_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega), Bool.false_or]
    rw [show p / 8 = 1 from by omega, show p % 8 = p - 8 from by omega]
  rcases Nat.lt_or_ge p 24 with h2 | h2
  · -- [16, 24): byte 2 active; p/8 = 2, p%8 = p - 16
    have hge0  : decide (p < 8) = false := by simp; omega
    have hge8  : decide (p < 16) = false := by simp; omega
    have hd16  : decide (p < 24) = true := by simp [h2]
    have hd24  : decide (p < 32) = true := by simp; omega
    have hd32  : decide (p < 40) = true := by simp; omega
    have hd40  : decide (p < 48) = true := by simp; omega
    have hd48  : decide (p < 56) = true := by simp; omega
    have hd_s  : decide (p - 16 < 64) = true := by simp; omega
    simp only [hp64, hge0, hge8, hd16, hd24, hd32, hd40, hd48, hd_s,
               Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and,
               Bool.or_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 1) 0) (p - 8) (by omega), Bool.and_false, Bool.false_or]
    rw [show p / 8 = 2 from by omega, show p % 8 = p - 16 from by omega]
  rcases Nat.lt_or_ge p 32 with h3 | h3
  · -- [24, 32): byte 3 active; p/8 = 3, p%8 = p - 24
    have hge0  : decide (p < 8) = false := by simp; omega
    have hge8  : decide (p < 16) = false := by simp; omega
    have hge16 : decide (p < 24) = false := by simp; omega
    have hd24  : decide (p < 32) = true := by simp [h3]
    have hd32  : decide (p < 40) = true := by simp; omega
    have hd40  : decide (p < 48) = true := by simp; omega
    have hd48  : decide (p < 56) = true := by simp; omega
    have hd_s  : decide (p - 24 < 64) = true := by simp; omega
    simp only [hp64, hge0, hge8, hge16, hd24, hd32, hd40, hd48, hd_s,
               Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and,
               Bool.or_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 1) 0) (p - 8) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 2) 0) (p - 16) (by omega),
               Bool.and_false, Bool.false_or]
    rw [show p / 8 = 3 from by omega, show p % 8 = p - 24 from by omega]
  rcases Nat.lt_or_ge p 40 with h4 | h4
  · -- [32, 40): byte 4 active; p/8 = 4, p%8 = p - 32
    have hge0  : decide (p < 8) = false := by simp; omega
    have hge8  : decide (p < 16) = false := by simp; omega
    have hge16 : decide (p < 24) = false := by simp; omega
    have hge24 : decide (p < 32) = false := by simp; omega
    have hd32  : decide (p < 40) = true := by simp [h4]
    have hd40  : decide (p < 48) = true := by simp; omega
    have hd48  : decide (p < 56) = true := by simp; omega
    have hd_s  : decide (p - 32 < 64) = true := by simp; omega
    simp only [hp64, hge0, hge8, hge16, hge24, hd32, hd40, hd48, hd_s,
               Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and,
               Bool.or_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 1) 0) (p - 8) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 2) 0) (p - 16) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 3) 0) (p - 24) (by omega),
               Bool.and_false, Bool.false_or]
    rw [show p / 8 = 4 from by omega, show p % 8 = p - 32 from by omega]
  rcases Nat.lt_or_ge p 48 with h5 | h5
  · -- [40, 48): byte 5 active; p/8 = 5, p%8 = p - 40
    have hge0  : decide (p < 8) = false := by simp; omega
    have hge8  : decide (p < 16) = false := by simp; omega
    have hge16 : decide (p < 24) = false := by simp; omega
    have hge24 : decide (p < 32) = false := by simp; omega
    have hge32 : decide (p < 40) = false := by simp; omega
    have hd40  : decide (p < 48) = true := by simp [h5]
    have hd48  : decide (p < 56) = true := by simp; omega
    have hd_s  : decide (p - 40 < 64) = true := by simp; omega
    simp only [hp64, hge0, hge8, hge16, hge24, hge32, hd40, hd48, hd_s,
               Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and,
               Bool.or_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 1) 0) (p - 8) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 2) 0) (p - 16) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 3) 0) (p - 24) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 4) 0) (p - 32) (by omega),
               Bool.and_false, Bool.false_or]
    rw [show p / 8 = 5 from by omega, show p % 8 = p - 40 from by omega]
  rcases Nat.lt_or_ge p 56 with h6 | h6
  · -- [48, 56): byte 6 active; p/8 = 6, p%8 = p - 48
    have hge0  : decide (p < 8) = false := by simp; omega
    have hge8  : decide (p < 16) = false := by simp; omega
    have hge16 : decide (p < 24) = false := by simp; omega
    have hge24 : decide (p < 32) = false := by simp; omega
    have hge32 : decide (p < 40) = false := by simp; omega
    have hge40 : decide (p < 48) = false := by simp; omega
    have hd48  : decide (p < 56) = true := by simp [h6]
    have hd_s  : decide (p - 48 < 64) = true := by simp; omega
    simp only [hp64, hge0, hge8, hge16, hge24, hge32, hge40, hd48, hd_s,
               Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_and,
               Bool.or_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 1) 0) (p - 8) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 2) 0) (p - 16) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 3) 0) (p - 24) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 4) 0) (p - 32) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 5) 0) (p - 40) (by omega),
               Bool.and_false, Bool.false_or]
    rw [show p / 8 = 6 from by omega, show p % 8 = p - 48 from by omega]
  · -- [56, 64): byte 7 active; p/8 = 7, p%8 = p - 56
    have hge0  : decide (p < 8) = false := by simp; omega
    have hge8  : decide (p < 16) = false := by simp; omega
    have hge16 : decide (p < 24) = false := by simp; omega
    have hge24 : decide (p < 32) = false := by simp; omega
    have hge32 : decide (p < 40) = false := by simp; omega
    have hge40 : decide (p < 48) = false := by simp; omega
    have hge48 : decide (p < 56) = false := by simp; omega
    have hd_s  : decide (p - 56 < 64) = true := by simp; omega
    simp only [hp64, hge0, hge8, hge16, hge24, hge32, hge40, hge48, hd_s,
               Bool.true_and, Bool.not_false]
    simp only [BitVec.getLsbD_of_ge (mem.getD base 0) p (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 1) 0) (p - 8) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 2) 0) (p - 16) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 3) 0) (p - 24) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 4) 0) (p - 32) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 5) 0) (p - 40) (by omega),
               BitVec.getLsbD_of_ge (mem.getD (base + 6) 0) (p - 48) (by omega),
               Bool.and_false, Bool.false_or]
    rw [show p / 8 = 7 from by omega, show p % 8 = p - 56 from by omega]

-- (`updateSubrange'_full` now lives in `VmemReduction.lean`, next to its width-8
-- sibling `updateSubrange_full`, where the `checked_mem_read` loop reduction needs it.)

-- ============================================================================
-- readBytesN leaves: the little-endian value of `w` present bytes
-- ============================================================================

/-- `readBytes 4` of four present bytes is their little-endian assembly (b0 lowest). -/
theorem readBytes4_raw (sSail : SailState) (a : Nat) (b0 b1 b2 b3 : BitVec 8)
    (h0 : sSail.mem.get? a = some b0) (h1 : sSail.mem.get? (a+1) = some b1)
    (h2 : sSail.mem.get? (a+2) = some b2) (h3 : sSail.mem.get? (a+3) = some b3) :
    (readBytes 4 a : SailM ((BitVec (8*4)) × Option Bool)) sSail
      = .ok (((b3.append b2).append b1).append b0, none) sSail := by
  simp only [readBytes, readByte, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, h0, h1, h2, h3]

/-- `readBytes 2` of two present bytes is their little-endian assembly (b0 lowest). -/
theorem readBytes2_raw (sSail : SailState) (a : Nat) (b0 b1 : BitVec 8)
    (h0 : sSail.mem.get? a = some b0) (h1 : sSail.mem.get? (a+1) = some b1) :
    (readBytes 2 a : SailM ((BitVec (8*2)) × Option Bool)) sSail
      = .ok (b1.append b0, none) sSail := by
  simp only [readBytes, readByte, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, h0, h1]

/-- `readBytes 1` of one present byte is that byte. -/
theorem readBytes1_raw (sSail : SailState) (a : Nat) (b0 : BitVec 8)
    (h0 : sSail.mem.get? a = some b0) :
    (readBytes 1 a : SailM ((BitVec (8*1)) × Option Bool)) sSail
      = .ok (b0, none) sSail := by
  simp only [readBytes, readByte, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, h0]

-- ============================================================================
-- Width-N read bridges: extract*(reconstructDword) = the little-endian assembly
-- (the value the Sail read produces equals the toy `getWord32/Halfword/Byte`).
-- Pure index arithmetic on top of `reconstructDword_getLsbD` (Lemma A).
-- ============================================================================

/-- `extractWord32` of the reconstructed dword at the aligned base equals the 4-byte
    little-endian assembly at the access offset. -/
theorem extractWord32_recon (mem : Std.ExtHashMap Nat (BitVec 8)) (base pos : Nat)
    (b0 b1 b2 b3 : BitVec 8) (hpos : pos < 2)
    (g0 : mem.getD (base + pos*4) 0 = b0) (g1 : mem.getD (base + pos*4 + 1) 0 = b1)
    (g2 : mem.getD (base + pos*4 + 2) 0 = b2) (g3 : mem.getD (base + pos*4 + 3) 0 = b3) :
    extractWord32 (reconstructDword mem base) pos = ((b3.append b2).append b1).append b0 := by
  rw [show (((b3.append b2).append b1).append b0 : BitVec 32) = b3 ++ b2 ++ b1 ++ b0 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, show i < 32 from hi, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  rw [reconstructDword_getLsbD mem base (pos*32 + i) (by omega),
    show (pos*32 + i) % 8 = i % 8 from by omega]
  rcases Nat.lt_or_ge i 8 with h0i | h0i
  · rw [show (pos*32 + i) / 8 = pos*4 by omega]
    simp only [show i < 8 by omega, if_true, ← g0]
    congr 1 <;> omega
  rcases Nat.lt_or_ge i 16 with h1i | h1i
  · rw [show (pos*32 + i) / 8 = pos*4 + 1 by omega]
    simp only [show ¬ i < 8 by omega, if_false, show i - 8 < 8 by omega, if_true, ← g1]
    congr 1 <;> omega
  rcases Nat.lt_or_ge i 24 with h2i | h2i
  · rw [show (pos*32 + i) / 8 = pos*4 + 2 by omega]
    simp only [show ¬ i < 8 by omega, if_false, show ¬ i - 8 < 8 by omega,
      show i - 8 - 8 < 8 by omega, if_true, ← g2]
    congr 1 <;> omega
  · rw [show (pos*32 + i) / 8 = pos*4 + 3 by omega]
    simp only [show ¬ i < 8 by omega, if_false, show ¬ i - 8 < 8 by omega,
      show ¬ i - 8 - 8 < 8 by omega, if_false, ← g3]
    congr 1 <;> omega

/-- `extractHalfword` of the reconstructed dword equals the 2-byte little-endian assembly. -/
theorem extractHalfword_recon (mem : Std.ExtHashMap Nat (BitVec 8)) (base pos : Nat)
    (b0 b1 : BitVec 8) (hpos : pos < 4)
    (g0 : mem.getD (base + pos*2) 0 = b0) (g1 : mem.getD (base + pos*2 + 1) 0 = b1) :
    extractHalfword (reconstructDword mem base) pos = b1.append b0 := by
  rw [show (b1.append b0 : BitVec 16) = b1 ++ b0 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, show i < 16 from hi, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  rw [reconstructDword_getLsbD mem base (pos*16 + i) (by omega),
    show (pos*16 + i) % 8 = i % 8 from by omega]
  rcases Nat.lt_or_ge i 8 with h0i | h0i
  · rw [show (pos*16 + i) / 8 = pos*2 by omega]
    simp only [show i < 8 by omega, if_true, ← g0]
    congr 1 <;> omega
  · rw [show (pos*16 + i) / 8 = pos*2 + 1 by omega]
    simp only [show ¬ i < 8 by omega, if_false, ← g1]
    congr 1 <;> omega

/-- `extractByte` of the reconstructed dword equals the single byte at the access offset. -/
theorem extractByte_recon (mem : Std.ExtHashMap Nat (BitVec 8)) (base pos : Nat)
    (b0 : BitVec 8) (hpos : pos < 8)
    (g0 : mem.getD (base + pos) 0 = b0) :
    extractByte (reconstructDword mem base) pos = b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, show i < 8 from hi, decide_true, Bool.true_and]
  rw [reconstructDword_getLsbD mem base (pos*8 + i) (by omega),
    show (pos*8 + i) % 8 = i from by omega, show (pos*8 + i) / 8 = pos by omega, g0]

-- ============================================================================
-- Generic width-N reduction chain (read value `v` abstracted).
-- The PMP/PMA/translate leaves in `VmemReduction.lean` are already width-generic.
-- ============================================================================

-- (`read_ram_load_N` and the width-generic `checked_mem_read` / `mem_read` chain now
-- live in `VmemReduction.lean` as `read_ram_load_N` / `checked_mem_read_load_w` /
-- `mem_read_load_w` — the split-misaligned loop moved inside `checked_mem_read`, so
-- the loop reduction is shared with the width-8 Tier-A chain.)

-- ============================================================================
-- `vmem_read_addr` per width (concrete writeback index, à la Tier A's width-8 case).
-- ============================================================================

theorem vmem_read_addr_load_core (w : Nat) (vaddr : virtaddr) (s : SailState)
    (mst : BitVec 64) (v : BitVec (8*w))
    (cfgs : Vector (BitVec 8) 64) (pmpaddrs : Vector (BitVec 64) 64)
    (regions : List PMA_Region) (region : PMA_Region)
    (hwlit : w = 1 ∨ w = 2 ∨ w = 4)
    (h_valign : is_aligned_vaddr vaddr w = true)
    (h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (h_mst : s.regs.get? Register.mstatus = some mst)
    (h_mprv : _get_Mstatus_MPRV mst = 0#1)
    (h_cfg : s.regs.get? Register.pmpcfg_n = some cfgs)
    (h_pmpaddr : s.regs.get? Register.pmpaddr_n = some pmpaddrs)
    (h_off : ∀ i : Nat,
      pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF)
    (h_reg : s.regs.get? Register.pma_regions = some regions)
    (h_match : matching_pma_region regions
      (physaddr.Physaddr (bits_of_virtaddr vaddr)) w = some region)
    (h_read : region.attributes.readable = true)
    (h_palign : is_aligned_paddr (physaddr.Physaddr (bits_of_virtaddr vaddr)) w = true)
    (hclint : (within_clint (physaddr.Physaddr (bits_of_virtaddr vaddr)) w) s = .ok false s)
    (hsig : (within_sig (physaddr.Physaddr (bits_of_virtaddr vaddr)) w) s = .ok false s)
    (hhtif : (within_htif_readable (physaddr.Physaddr (bits_of_virtaddr vaddr)) w) s = .ok false s)
    (hread : (readBytes w (bits_of_virtaddr vaddr).toNat : SailM ((BitVec (8*w)) × Option Bool)) s
      = .ok (v, none) s) :
    (vmem_read_addr vaddr w (MemoryAccessType.Load mem_payload.Data) false false false) s
      = .ok (Result.Ok v) s := by
  have hwlit8 : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 := hwlit.imp id (Or.imp id Or.inl)
  have halignN : (bits_of_virtaddr vaddr).toNat % w = 0 :=
    toNat_mod_of_is_aligned_vaddr vaddr w hwlit8 h_valign
  have hpage := split_on_page_boundary_aligned (bits_of_virtaddr vaddr) w s hwlit8 halignN
  have hmem := mem_read_load_w w (bits_of_virtaddr vaddr) s mst v cfgs pmpaddrs regions region
    hwlit8 h_priv h_mst h_mprv h_cfg h_pmpaddr h_off h_reg h_match h_read h_palign
    hclint hsig hhtif hread
  have htrv := translate_and_read_value_load_bare vaddr w s mst v h_priv h_mst h_mprv hmem
  unfold vmem_read_addr
  simp +decide only [h_valign, Functions.not, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false,
    SailME.run, PreSail.PreSailME.run,
    hpage, PreSail.readReg, h_priv, h_mst,
    effectivePrivilege_machine s _ mst _ h_mprv, translationMode_machine,
    sys_misaligned_order_decreasing, bne,
    show (SATPMode.Bare == SATPMode.Bare) = true from rfl,
    Bool.false_and, Bool.true_and,
    EStateM.map, bind, EStateM.bind, pure, EStateM.pure, EStateM.get,
    get, MonadState.get, getThe, MonadStateOf.get,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure,
    MonadLift.monadLift, monadLift, liftM, Functor.map]
  rw [show (if (false = true) then ((w : Nat) : Int) else ((w : Nat) : Int))
        = ((w : Nat) : Int) from rfl]
  erw [htrv]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont]
  rw [show ((8 : Int) * ((w : Nat) : Int) - 1).toNat = 8 * w - 1 from by omega]
  rcases hwlit with rfl | rfl | rfl <;>
    (simp only [Sail.BitVec.updateSubrange, updateSubrange'_full]; erw [BitVec.setWidth_eq])

-- ============================================================================
-- `vmem_read` (generic in `w`; consumes `vmem_read_addr` abstractly).
-- ============================================================================

theorem vmem_read_load_N (w : Nat) (rs : regidx) (offset rsval : BitVec 64) (s : SailState)
    (v : BitVec (8*w)) (bm : BareModeInv s)
    (h_rs : (rX_bits rs) s = .ok rsval s)
    (hvra : (vmem_read_addr (virtaddr.Virtaddr (rsval + offset)) w
      (MemoryAccessType.Load mem_payload.Data) false false false) s = .ok (Result.Ok v) s) :
    (vmem_read rs offset w (MemoryAccessType.Load mem_payload.Data) false false false) s
      = .ok (Result.Ok v) s := by
  obtain ⟨mst, msec, cfgs, pmpaddrs, regions, h_priv, h_mst, h_mprv, h_sec, h_pmm,
    h_cfg, h_pmpaddr, h_off, h_reg⟩ := bm
  have htransform := transform_effective_address_bare s
    (virtaddr.Virtaddr (rsval + offset)) mst msec h_priv h_mst h_mprv h_sec h_pmm
  unfold vmem_read get_transformed_data_addr ext_data_get_addr
  sail_reduce [h_rs, htransform, pm_transform_PA_zero, bits_of_virtaddr_mk, hvra]

end EvmAsm.Rv64.SailEquiv
