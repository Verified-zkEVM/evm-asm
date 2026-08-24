/-
  EvmAsm.Codegen.Programs.Step2ParentHashLayout

  Declaration facts for the Step-2 parent-hash scratch.  These are kept
  separate from the producer and caller contracts: the data declarations
  determine capacities and linked addresses, while a producer contract is
  responsible for showing that a runtime byte list still has that capacity.
-/

import EvmAsm.Codegen.Programs.Step2Verdict
import EvmAsm.Codegen.Programs.HeadersParentHashSpec

namespace EvmAsm.Codegen

open EvmAsm EvmAsm.Rv64

/-! The source declarations are the evidence for these capacities.  The
    `#guard`s intentionally check the emitted data strings, rather than
    silently duplicating the numbers in a comment or theorem name. -/

#guard ziskStep2VerdictDataSection.contains "hvph_claimed:\n  .zero 32\n"
#guard ziskStep2VerdictDataSection.contains "hvph_computed:\n  .zero 32\n"
#guard ziskMptWalkDataSection.contains "zk3_state:\n  .zero 200\n"

/-- The zero-initialized image represented by the `hvph_claimed` declaration.

    This is the declaration's initial image, not a claim that a later
    producer's runtime contents are all zero.  A producer contract must keep
    the length invariant when it replaces these bytes. -/
abbrev step2HvphClaimedImage : List (BitVec 8) := List.replicate 32 0

/-- The zero-initialized image represented by the `zk3_state` declaration. -/
abbrev step2Zk3StateImage : List (BitVec 8) := List.replicate 200 0

theorem step2HvphClaimedImage_length : step2HvphClaimedImage.length = 32 := by
  simp only [step2HvphClaimedImage, List.length_replicate]

theorem step2Zk3StateImage_length : step2Zk3StateImage.length = 200 := by
  simp only [step2Zk3StateImage, List.length_replicate]

/-- Linked address of the 32-byte claimed parent-hash slot. -/
abbrev step2HvphClaimedBase : Word := BitVec.ofNat 64 GuestAddrs.hvph_claimed

/-- Linked address of the 200-byte MPT/withdrawals scratch arena. -/
abbrev step2Zk3StateBase : Word := BitVec.ofNat 64 GuestAddrs.zk3_state

theorem step2HvphClaimedBase_toNat :
    step2HvphClaimedBase.toNat = GuestAddrs.hvph_claimed := by
  exact hphClaimed_toNat

theorem step2HvphClaimedBase_aligned : step2HvphClaimedBase.toNat % 8 = 0 := by
  exact hphClaimed_align

theorem step2HvphClaimedBase_range (i : Nat) (hi : i < 32) :
    step2HvphClaimedBase.toNat + i < 2 ^ 64 := by
  exact hphClaimed_over i hi

theorem step2HvphClaimedBase_valid_byte (i : Nat) (hi : i < 32) :
    isValidByteAccess (step2HvphClaimedBase + BitVec.ofNat 64 i) = true := by
  exact hphClaimed_valid i hi

theorem step2Zk3StateBase_toNat :
    step2Zk3StateBase.toNat = 0xa3a4c0e0 := by
  decide

theorem step2Zk3StateBase_aligned : step2Zk3StateBase.toNat % 8 = 0 := by
  decide

theorem step2Zk3StateBase_range :
    step2Zk3StateBase.toNat + 200 < 2 ^ 64 := by
  decide

private theorem ram_byte_valid_of_range (base i : Nat)
    (hbase : 0xa0000000 ≤ base)
    (hend : base + i ≤ 0xc0000000) :
    isValidByteAccess (BitVec.ofNat 64 base + BitVec.ofNat 64 i) = true := by
  have hbase64 : base < 2 ^ 64 := by omega
  have hi64 : i < 2 ^ 64 := by omega
  have hsum64 : base + i < 2 ^ 64 := by omega
  have hto :
      (BitVec.ofNat 64 base + BitVec.ofNat 64 i).toNat = base + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbase64, Nat.mod_eq_of_lt hi64,
      Nat.mod_eq_of_lt hsum64]
  simp only [isValidByteAccess, isValidMemAddr, hto,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  show ((0x20 ≤ base + i ∧ base + i ≤ 0x78000000) ∨
      (0x40000000 ≤ base + i ∧ base + i ≤ 0x40002000)) ∨
    (0xa0000000 ≤ base + i ∧ base + i ≤ 0xc0000000)
  exact Or.inr ⟨by omega, hend⟩

theorem step2Zk3StateBase_valid_byte (i : Nat) (hi : i < 200) :
    isValidByteAccess (step2Zk3StateBase + BitVec.ofNat 64 i) = true := by
  rw [show step2Zk3StateBase = BitVec.ofNat 64 0xa3a4c0e0 by rfl]
  apply ram_byte_valid_of_range 0xa3a4c0e0 i
  · omega
  · omega

theorem step2Zk3StateBase_valid_mem (i : Nat) (hi : i < 200) :
    isValidMemAddr (step2Zk3StateBase + BitVec.ofNat 64 i) = true := by
  exact step2Zk3StateBase_valid_byte i hi

end EvmAsm.Codegen
