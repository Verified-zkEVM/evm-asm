/-
  EvmAsm.Evm64.MLoad.Expansion

  Small executable helpers for MLOAD memory-size bookkeeping.
-/

import EvmAsm.Evm64.Memory
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
  Compute the byte just past a 32-byte MLOAD access. This is the first
  arithmetic stage of the memory high-water update: later blocks round this
  value up to a 32-byte boundary and select the max with the current size.
-/
def mload_compute_access_end (endReg offReg : Reg) : Program :=
  ADDI endReg offReg 32

abbrev mload_compute_access_end_code
    (endReg offReg : Reg) (base : Word) : CodeReq :=
  CodeReq.singleton base (.ADDI endReg offReg 32)

theorem mload_compute_access_end_code_eq_ofProg
    (endReg offReg : Reg) (base : Word) :
    mload_compute_access_end_code endReg offReg base =
      CodeReq.ofProg base (mload_compute_access_end endReg offReg) := by
  unfold mload_compute_access_end_code mload_compute_access_end ADDI single
  rfl

/--
  One-instruction executable bridge for `offset + 32`, the exclusive end of a
  32-byte MLOAD access.
-/
theorem mload_compute_access_end_spec_within
    (endReg offReg : Reg) (offset endOld : Word) (base : Word)
    (h_end_ne_x0 : endReg ≠ .x0) :
    cpsTripleWithin 1 base (base + 4)
      (mload_compute_access_end_code endReg offReg base)
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32))) := by
  have h := addi_spec_gen_within endReg offReg endOld offset 32 base h_end_ne_x0
  simp only [signExtend12_32] at h
  exact h

theorem mload_compute_access_end_ofProg_spec_within
    (endReg offReg : Reg) (offset endOld : Word) (base : Word)
    (h_end_ne_x0 : endReg ≠ .x0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base (mload_compute_access_end endReg offReg))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32))) := by
  rw [← mload_compute_access_end_code_eq_ofProg]
  exact mload_compute_access_end_spec_within
    endReg offReg offset endOld base h_end_ne_x0

/--
  Round an already-computed MLOAD access end up to the next 32-byte boundary
  in executable RV64 code: add 31, then clear the low five bits.
-/
def mload_round_access_end (roundReg endReg : Reg) : Program :=
  ADDI roundReg endReg 31 ;;
  ANDI roundReg roundReg (-32)

abbrev mload_round_access_end_code
    (roundReg endReg : Reg) (base : Word) : CodeReq :=
  (CodeReq.singleton base (.ADDI roundReg endReg 31)).union
    (CodeReq.singleton (base + 4) (.ANDI roundReg roundReg (-32)))

theorem mload_round_access_end_code_eq_ofProg
    (roundReg endReg : Reg) (base : Word) :
    mload_round_access_end_code roundReg endReg base =
      CodeReq.ofProg base (mload_round_access_end roundReg endReg) := by
  unfold mload_round_access_end_code mload_round_access_end ADDI ANDI single seq
  rfl

/--
  Executable bridge for the 32-byte alignment stage of MLOAD memory expansion.
  The resulting word is `(accessEnd + 31) &&& -32`, i.e. the usual round-up
  mask for a 32-byte boundary.
-/
theorem mload_round_access_end_spec_within
    (roundReg endReg : Reg) (accessEnd roundOld : Word) (base : Word)
    (h_round_ne_x0 : roundReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mload_round_access_end_code roundReg endReg base)
      ((endReg ↦ᵣ accessEnd) ** (roundReg ↦ᵣ roundOld))
      ((endReg ↦ᵣ accessEnd) **
       (roundReg ↦ᵣ ((accessEnd + 31) &&& signExtend12 (-32 : BitVec 12)))) := by
  unfold mload_round_access_end_code
  have h_add :=
    addi_spec_gen_within roundReg endReg roundOld accessEnd 31 base h_round_ne_x0
  have h_andi :=
    andi_spec_gen_same_within roundReg (accessEnd + signExtend12 (31 : BitVec 12))
      (-32 : BitVec 12) (base + 4) h_round_ne_x0
  simp only [show signExtend12 (31 : BitVec 12) = (31 : Word) from by decide] at h_add h_andi
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at h_andi
  runBlock h_add h_andi

theorem mload_round_access_end_ofProg_spec_within
    (roundReg endReg : Reg) (accessEnd roundOld : Word) (base : Word)
    (h_round_ne_x0 : roundReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base (mload_round_access_end roundReg endReg))
      ((endReg ↦ᵣ accessEnd) ** (roundReg ↦ᵣ roundOld))
      ((endReg ↦ᵣ accessEnd) **
       (roundReg ↦ᵣ ((accessEnd + 31) &&& signExtend12 (-32 : BitVec 12)))) := by
  rw [← mload_round_access_end_code_eq_ofProg]
  exact mload_round_access_end_spec_within
    roundReg endReg accessEnd roundOld base h_round_ne_x0

/--
  Compute both the exclusive MLOAD access end (`offset + 32`) and its
  executable 32-byte rounded form.
-/
def mload_compute_rounded_access_end
    (roundReg endReg offReg : Reg) : Program :=
  mload_compute_access_end endReg offReg ;;
  mload_round_access_end roundReg endReg

abbrev mload_compute_rounded_access_end_code
    (roundReg endReg offReg : Reg) (base : Word) : CodeReq :=
  (mload_compute_access_end_code endReg offReg base).union
    (mload_round_access_end_code roundReg endReg (base + 4))

theorem mload_compute_rounded_access_end_code_eq_ofProg
    (roundReg endReg offReg : Reg) (base : Word) :
    mload_compute_rounded_access_end_code roundReg endReg offReg base =
      CodeReq.ofProg base
        (mload_compute_rounded_access_end roundReg endReg offReg) := by
  unfold mload_compute_rounded_access_end_code mload_compute_rounded_access_end
    mload_compute_access_end_code mload_round_access_end_code
    mload_compute_access_end mload_round_access_end ADDI ANDI single seq
  change (CodeReq.singleton base (Instr.ADDI endReg offReg 32)).union
      ((CodeReq.singleton (base + 4) (Instr.ADDI roundReg endReg 31)).union
        (CodeReq.singleton ((base + 4) + 4)
          (Instr.ANDI roundReg roundReg (-32)))) =
    CodeReq.ofProg base [Instr.ADDI endReg offReg 32,
      Instr.ADDI roundReg endReg 31, Instr.ANDI roundReg roundReg (-32)]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

/--
  Composed executable bridge for the first two arithmetic stages of MLOAD
  memory expansion.
-/
theorem mload_compute_rounded_access_end_spec_within
    (roundReg endReg offReg : Reg)
    (offset endOld roundOld : Word) (base : Word)
    (h_end_ne_x0 : endReg ≠ .x0)
    (h_round_ne_x0 : roundReg ≠ .x0) :
    cpsTripleWithin 3 base (base + 12)
      (mload_compute_rounded_access_end_code roundReg endReg offReg base)
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld) ** (roundReg ↦ᵣ roundOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12)))) := by
  unfold mload_compute_rounded_access_end_code
  have h_end :=
    mload_compute_access_end_spec_within endReg offReg offset endOld base h_end_ne_x0
  have h_round :=
    mload_round_access_end_spec_within roundReg endReg (offset + 32) roundOld
      (base + 4) h_round_ne_x0
  rw [show (base + 4 : Word) + 8 = base + 12 from by bv_omega] at h_round
  have hd :
      (mload_compute_access_end_code endReg offReg base).Disjoint
        (mload_round_access_end_code roundReg endReg (base + 4)) := by
    unfold mload_compute_access_end_code mload_round_access_end_code
    exact CodeReq.Disjoint.union_right
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.singleton (by bv_omega))
  have h_end_framed : cpsTripleWithin 1 base (base + 4)
      (mload_compute_access_end_code endReg offReg base)
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld) ** (roundReg ↦ᵣ roundOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) ** (roundReg ↦ᵣ roundOld)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR (roundReg ↦ᵣ roundOld) (by pcFree) h_end)
  have h_round_framed : cpsTripleWithin 2 (base + 4) (base + 12)
      (mload_round_access_end_code roundReg endReg (base + 4))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) ** (roundReg ↦ᵣ roundOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12)))) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameL (offReg ↦ᵣ offset) (by pcFree) h_round)
  exact cpsTripleWithin_seq hd h_end_framed h_round_framed

theorem mload_compute_rounded_access_end_ofProg_spec_within
    (roundReg endReg offReg : Reg)
    (offset endOld roundOld : Word) (base : Word)
    (h_end_ne_x0 : endReg ≠ .x0)
    (h_round_ne_x0 : roundReg ≠ .x0) :
    cpsTripleWithin 3 base (base + 12)
      (CodeReq.ofProg base
        (mload_compute_rounded_access_end roundReg endReg offReg))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld) ** (roundReg ↦ᵣ roundOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12)))) := by
  rw [← mload_compute_rounded_access_end_code_eq_ofProg]
  exact mload_compute_rounded_access_end_spec_within
    roundReg endReg offReg offset endOld roundOld base h_end_ne_x0 h_round_ne_x0

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
  Max-form variant of `mload_write_expanded_size_ofProg_spec_within`, for
  callers that compute the 32-byte MLOAD high-water mark explicitly as a
  maximum rather than through `evmMemExpand`.
-/
theorem mload_write_expanded_size_max_spec_within
    (sizeLocReg sizeReg : Reg)
    (sizeLoc : Word) (sizeBytes offset : Nat) (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base (mload_write_expanded_size sizeLocReg sizeReg))
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 (max sizeBytes (roundUpTo32 (offset + 32)))) **
       evmMemSizeIs sizeLoc sizeBytes)
      ((sizeLocReg ↦ᵣ sizeLoc) **
       (sizeReg ↦ᵣ BitVec.ofNat 64 (max sizeBytes (roundUpTo32 (offset + 32)))) **
       evmMemSizeIs sizeLoc (max sizeBytes (roundUpTo32 (offset + 32)))) := by
  convert
    (mload_write_expanded_size_ofProg_spec_within
      sizeLocReg sizeReg sizeLoc sizeBytes offset base) using 1
  · rw [evmMemSizeIsWordExpanded_unfold_max, evmMemExpand_word_eq]

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
