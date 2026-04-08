/-
  EvmAsm.Rv64.SailEquiv.HelperEquiv

  Equivalence lemmas for helper functions that differ between
  the Rv64 model and the SAIL spec.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.Instructions
import LeanRV64D

open LeanRV64D.Functions
open LeanRV64D.Defs

namespace EvmAsm.Rv64.SailEquiv

-- ============================================================================
-- Sign/zero extension equivalences
-- ============================================================================

/-- SAIL's sign_extend on BitVec 12 equals Rv64's signExtend12. -/
theorem sign_extend_12_eq (imm : BitVec 12) :
    sign_extend (m := 64) imm = signExtend12 imm := by
  sorry

/-- SAIL's sign_extend on BitVec 13 equals Rv64's signExtend13. -/
theorem sign_extend_13_eq (imm : BitVec 13) :
    sign_extend (m := 64) imm = signExtend13 imm := by
  sorry

/-- SAIL's sign_extend on BitVec 21 equals Rv64's signExtend21. -/
theorem sign_extend_21_eq (imm : BitVec 21) :
    sign_extend (m := 64) imm = signExtend21 imm := by
  sorry

-- ============================================================================
-- Shift equivalences
-- ============================================================================

/-- shift_bits_left is just (<<<). -/
theorem shift_bits_left_eq (v : BitVec n) (sh : BitVec m) :
    shift_bits_left v sh = v <<< sh := by
  sorry

/-- shift_bits_right is just (>>>). -/
theorem shift_bits_right_eq (v : BitVec n) (sh : BitVec m) :
    shift_bits_right v sh = v >>> sh := by
  sorry

/-- shift_bits_right_arith equals BitVec.sshiftRight. -/
theorem shift_bits_right_arith_eq (v : BitVec n) (sh : BitVec m) :
    shift_bits_right_arith v sh = BitVec.sshiftRight v sh.toNat := by
  sorry

/-- Extracting bits [5:0] from a 64-bit value and using as shift amount
    is equivalent to toNat % 64. -/
theorem extractLsb_shamt_mod64 (rs2 : BitVec 64) :
    (Sail.BitVec.extractLsb rs2 5 0).toNat = rs2.toNat % 64 := by
  sorry

/-- For shift operations: using extractLsb as a shift amount produces
    the same result as using toNat % 64. -/
theorem sll_extractLsb_eq (v rs2 : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb rs2 5 0) =
    v <<< (rs2.toNat % 64) := by
  sorry

theorem srl_extractLsb_eq (v rs2 : BitVec 64) :
    shift_bits_right v (Sail.BitVec.extractLsb rs2 5 0) =
    v >>> (rs2.toNat % 64) := by
  sorry

theorem sra_extractLsb_eq (v rs2 : BitVec 64) :
    shift_bits_right_arith v (Sail.BitVec.extractLsb rs2 5 0) =
    BitVec.sshiftRight v (rs2.toNat % 64) := by
  sorry

-- ============================================================================
-- Comparison equivalences
-- ============================================================================

/-- SAIL's signed less-than (zopz0zI_s) equals BitVec.slt. -/
theorem slt_equiv (a b : BitVec 64) :
    zopz0zI_s a b = BitVec.slt a b := by
  sorry

/-- SAIL's unsigned less-than (zopz0zI_u) equals BitVec.ult. -/
theorem ult_equiv (a b : BitVec 64) :
    zopz0zI_u a b = BitVec.ult a b := by
  sorry

/-- SAIL's signed greater-or-equal (zopz0zKzJ_s) equals ¬ BitVec.slt. -/
theorem sge_equiv (a b : BitVec 64) :
    zopz0zKzJ_s a b = ¬ BitVec.slt a b := by
  sorry

/-- SAIL's unsigned greater-or-equal (zopz0zKzJ_u) equals ¬ BitVec.ult. -/
theorem uge_equiv (a b : BitVec 64) :
    zopz0zKzJ_u a b = ¬ BitVec.ult a b := by
  sorry

/-- bool_to_bit + zero_extend produces 0 or 1 as BitVec 64. -/
theorem bool_to_bit_if (b : Bool) :
    zero_extend (m := 64) (bool_to_bit b) = if b then (1 : BitVec 64) else 0 := by
  sorry

-- ============================================================================
-- LUI equivalence
-- ============================================================================

/-- The two ways to compute LUI produce the same result:
    Rv64:  (imm.zeroExtend 32 <<< 12).signExtend 64
    SAIL:  sign_extend (m := 64) (imm +++ 0x000#12)
-/
theorem lui_equiv (imm : BitVec 20) :
    (imm.zeroExtend 32 <<< 12).signExtend 64 =
    sign_extend (m := 64) (imm ++ (0 : BitVec 12)) := by
  sorry

-- ============================================================================
-- ADDIW equivalence
-- ============================================================================

/-- ADDIW: truncate-then-add equals add-then-truncate for lower 32 bits.
    Rv64:  ((rs1.truncate 32) + (sext(imm).truncate 32)).signExtend 64
    SAIL:  sign_extend (Sail.BitVec.extractLsb (rs1 + sign_extend imm) 31 0)
-/
theorem addiw_equiv (rs1 : BitVec 64) (imm : BitVec 12) :
    ((rs1.truncate 32 : BitVec 32) + ((signExtend12 imm).truncate 32 : BitVec 32)).signExtend 64 =
    (Sail.BitVec.extractLsb (rs1 + signExtend12 imm) 31 0).signExtend 64 := by
  sorry

-- ============================================================================
-- Division/remainder equivalences
-- ============================================================================

/-- Signed division: BitVec.sdiv matches SAIL's Int.tdiv-based computation.
    When b ≠ 0 and no overflow. -/
theorem sdiv_equiv (a b : BitVec 64) (hb : b ≠ 0) :
    BitVec.sdiv a b = to_bits_truncate (l := 64) (Int.tdiv a.toInt b.toInt) := by
  sorry

/-- Unsigned division: a / b matches SAIL's computation. -/
theorem udiv_equiv (a b : BitVec 64) (hb : b ≠ 0) :
    a / b = to_bits_truncate (l := 64) (Int.tdiv (BitVec.toNatInt a) (BitVec.toNatInt b)) := by
  sorry

/-- rv64_div matches SAIL's execute_DIV for signed division. -/
theorem rv64_div_sail_equiv (a b : BitVec 64) :
    rv64_div a b = (
      let rs1_int := BitVec.toInt a
      let rs2_int := BitVec.toInt b
      let quotient := if rs2_int == 0 then -1 else Int.tdiv rs1_int rs2_int
      let quotient := if quotient ≥ (2 ^ 63 : Int) then -(2 ^ 63 : Int) else quotient
      to_bits_truncate (l := 64) quotient) := by
  sorry

/-- rv64_divu matches SAIL's execute_DIV for unsigned division. -/
theorem rv64_divu_sail_equiv (a b : BitVec 64) :
    rv64_divu a b = (
      let rs1_int := BitVec.toNatInt a
      let rs2_int := BitVec.toNatInt b
      let quotient := if rs2_int == 0 then -1 else Int.tdiv rs1_int rs2_int
      to_bits_truncate (l := 64) quotient) := by
  sorry

/-- rv64_rem matches SAIL's execute_REM for signed remainder. -/
theorem rv64_rem_sail_equiv (a b : BitVec 64) :
    rv64_rem a b = (
      let rs1_int := BitVec.toInt a
      let rs2_int := BitVec.toInt b
      let remainder := if rs2_int == 0 then rs1_int else Int.tmod rs1_int rs2_int
      to_bits_truncate (l := 64) remainder) := by
  sorry

/-- rv64_remu matches SAIL's execute_REM for unsigned remainder. -/
theorem rv64_remu_sail_equiv (a b : BitVec 64) :
    rv64_remu a b = (
      let rs1_int := BitVec.toNatInt a
      let rs2_int := BitVec.toNatInt b
      let remainder := if rs2_int == 0 then rs1_int else Int.tmod rs1_int rs2_int
      to_bits_truncate (l := 64) remainder) := by
  sorry

-- ============================================================================
-- Multiply equivalences
-- ============================================================================

/-- MUL (low bits): a * b equals mult_to_bits_half Low. -/
theorem mul_low_equiv (a b : BitVec 64) :
    a * b = mult_to_bits_half (l := 64) Signed Signed a b Low := by
  sorry

/-- MULH: rv64_mulh equals mult_to_bits_half Signed Signed High. -/
theorem mulh_equiv (a b : BitVec 64) :
    rv64_mulh a b = mult_to_bits_half (l := 64) Signed Signed a b High := by
  sorry

/-- MULHSU: rv64_mulhsu equals mult_to_bits_half Signed Unsigned High. -/
theorem mulhsu_equiv (a b : BitVec 64) :
    rv64_mulhsu a b = mult_to_bits_half (l := 64) Signed Unsigned a b High := by
  sorry

/-- MULHU: rv64_mulhu equals mult_to_bits_half Unsigned Unsigned High. -/
theorem mulhu_equiv (a b : BitVec 64) :
    rv64_mulhu a b = mult_to_bits_half (l := 64) Unsigned Unsigned a b High := by
  sorry

-- ============================================================================
-- Memory access equivalences (bare mode)
-- ============================================================================

/-- Under bare mode (Machine privilege, satp = 0), vmem_read reduces to
    a direct physical memory read with no address translation. -/
theorem bare_mode_vmem_read (rs1 : regidx) (offset : BitVec 64) (width : Int)
    (s : SailState) (h_bare : True /- TODO: bare mode predicate -/) :
    True := by  -- TODO: state the full theorem once vmem_read is better understood
  sorry

/-- JALR bit-0 masking: BitVec.update target 0 0#1 equals target &&& ~~~1. -/
theorem jalr_mask_equiv (target : BitVec 64) :
    BitVec.update target 0 (0 : BitVec 1) = target &&& ~~~1#64 := by
  sorry

end EvmAsm.Rv64.SailEquiv
