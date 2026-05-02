/-
  EvmAsm.Evm64.MLoad.Expansion

  Small executable helpers for MLOAD memory-size bookkeeping.
-/

import EvmAsm.Evm64.Memory
import EvmAsm.Rv64.SyscallSpecs

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
  Store a precomputed 32-byte-access expanded high-water mark into the EVM
  memory-size cell. The arithmetic that computes
  `evmMemExpand sizeBytes offset 32` can be supplied by a caller or a later
  arithmetic subroutine; this block is the one-instruction ownership update.
-/
def mload_write_expanded_size (sizeLocReg sizeReg : Reg) : Program :=
  SD sizeLocReg sizeReg 0

abbrev mload_write_expanded_size_code
    (sizeLocReg sizeReg : Reg) (base : Word) : CodeReq :=
  CodeReq.singleton base (.SD sizeLocReg sizeReg 0)

theorem mload_write_expanded_size_code_eq_ofProg
    (sizeLocReg sizeReg : Reg) (base : Word) :
    mload_write_expanded_size_code sizeLocReg sizeReg base =
      CodeReq.ofProg base (mload_write_expanded_size sizeLocReg sizeReg) := by
  unfold mload_write_expanded_size_code mload_write_expanded_size SD single
  rfl

/--
  One-instruction size-cell update for a 32-byte MLOAD access, assuming the
  expanded high-water mark has already been computed into `sizeReg`.
-/
theorem mload_write_expanded_size_spec_within
    (sizeLocReg sizeReg : Reg)
    (sizeLoc : Word) (sizeBytes offset : Nat) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (mload_write_expanded_size_code sizeLocReg sizeReg base)
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 (evmMemExpand sizeBytes offset 32)) **
       evmMemSizeIs sizeLoc sizeBytes)
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 (evmMemExpand sizeBytes offset 32)) **
       evmMemSizeIsWordExpanded sizeLoc sizeBytes offset) := by
  rw [evmMemSizeIs_unfold, evmMemSizeIsWordExpanded_unfold, evmMemSizeIs_unfold]
  convert
    (sd_spec_gen_within sizeLocReg sizeReg sizeLoc
      (BitVec.ofNat 64 (evmMemExpand sizeBytes offset 32))
      (BitVec.ofNat 64 sizeBytes) 0 base) using 1
  · rw [signExtend12_0]
    simp
  · rw [signExtend12_0]
    simp

theorem mload_write_expanded_size_ofProg_spec_within
    (sizeLocReg sizeReg : Reg)
    (sizeLoc : Word) (sizeBytes offset : Nat) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base (mload_write_expanded_size sizeLocReg sizeReg))
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 (evmMemExpand sizeBytes offset 32)) **
       evmMemSizeIs sizeLoc sizeBytes)
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 (evmMemExpand sizeBytes offset 32)) **
       evmMemSizeIsWordExpanded sizeLoc sizeBytes offset) := by
  rw [← mload_write_expanded_size_code_eq_ofProg]
  exact mload_write_expanded_size_spec_within
    sizeLocReg sizeReg sizeLoc sizeBytes offset base

/--
  No-expansion specialization of `mload_write_expanded_size_ofProg_spec_within`:
  when the 32-byte MLOAD access already fits inside the current 32-byte-aligned
  high-water mark, writing the current size back preserves `evmMemSizeIs`.
-/
theorem mload_write_current_size_no_expansion_spec_within
    (sizeLocReg sizeReg : Reg)
    (sizeLoc : Word) (sizeBytes offset : Nat) (base : Word)
    (h_end : offset + 32 ≤ sizeBytes) (h_size_dvd : 32 ∣ sizeBytes) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base (mload_write_expanded_size sizeLocReg sizeReg))
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 sizeBytes) **
       evmMemSizeIs sizeLoc sizeBytes)
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 sizeBytes) **
       evmMemSizeIs sizeLoc sizeBytes) := by
  convert
    (mload_write_expanded_size_ofProg_spec_within
      sizeLocReg sizeReg sizeLoc sizeBytes offset base) using 1
  · rw [evmMemExpand_word_eq_old_of_end_le sizeBytes offset h_end h_size_dvd]
  · rw [evmMemExpand_word_eq_old_of_end_le sizeBytes offset h_end h_size_dvd,
      evmMemSizeIsWordExpanded_eq_current_of_mload_within h_end h_size_dvd]

end EvmAsm.Evm64
