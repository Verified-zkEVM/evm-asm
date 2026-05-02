/-
  EvmAsm.Evm64.MLoad.Expansion

  Small executable helpers for MLOAD memory-size bookkeeping.
-/

import EvmAsm.Evm64.Memory
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.ExtractPure
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
  Compare the current memory size against the rounded access end. The result
  is the executable branch flag for the later high-water max/select stage.
-/
def mload_compute_expand_flag
    (flagReg sizeReg roundReg : Reg) : Program :=
  single (.SLTU flagReg sizeReg roundReg)

abbrev mload_compute_expand_flag_code
    (flagReg sizeReg roundReg : Reg) (base : Word) : CodeReq :=
  CodeReq.singleton base (.SLTU flagReg sizeReg roundReg)

theorem mload_compute_expand_flag_code_eq_ofProg
    (flagReg sizeReg roundReg : Reg) (base : Word) :
    mload_compute_expand_flag_code flagReg sizeReg roundReg base =
      CodeReq.ofProg base (mload_compute_expand_flag flagReg sizeReg roundReg) := by
  unfold mload_compute_expand_flag_code mload_compute_expand_flag single
  rfl

/--
  One-instruction executable bridge for the unsigned comparison
  `currentSize < roundedAccessEnd`.
-/
theorem mload_compute_expand_flag_spec_within
    (flagReg sizeReg roundReg : Reg)
    (sizeBytesWord roundedAccessEnd flagOld : Word) (base : Word)
    (h_flag_ne_x0 : flagReg ≠ .x0) :
    cpsTripleWithin 1 base (base + 4)
      (mload_compute_expand_flag_code flagReg sizeReg roundReg base)
      ((sizeReg ↦ᵣ sizeBytesWord) **
       (roundReg ↦ᵣ roundedAccessEnd) **
       (flagReg ↦ᵣ flagOld))
      ((sizeReg ↦ᵣ sizeBytesWord) **
       (roundReg ↦ᵣ roundedAccessEnd) **
       (flagReg ↦ᵣ
        (if BitVec.ult sizeBytesWord roundedAccessEnd then (1 : Word) else 0))) :=
  sltu_spec_gen_within flagReg sizeReg roundReg flagOld
    sizeBytesWord roundedAccessEnd base h_flag_ne_x0

theorem mload_compute_expand_flag_ofProg_spec_within
    (flagReg sizeReg roundReg : Reg)
    (sizeBytesWord roundedAccessEnd flagOld : Word) (base : Word)
    (h_flag_ne_x0 : flagReg ≠ .x0) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base (mload_compute_expand_flag flagReg sizeReg roundReg))
      ((sizeReg ↦ᵣ sizeBytesWord) **
       (roundReg ↦ᵣ roundedAccessEnd) **
       (flagReg ↦ᵣ flagOld))
      ((sizeReg ↦ᵣ sizeBytesWord) **
       (roundReg ↦ᵣ roundedAccessEnd) **
       (flagReg ↦ᵣ
        (if BitVec.ult sizeBytesWord roundedAccessEnd then (1 : Word) else 0))) := by
  rw [← mload_compute_expand_flag_code_eq_ofProg]
  exact mload_compute_expand_flag_spec_within
    flagReg sizeReg roundReg sizeBytesWord roundedAccessEnd flagOld base h_flag_ne_x0

/--
  Compute the MLOAD access end, round it to the EVM memory word boundary, and
  compare it against the current memory size.
-/
def mload_compute_rounded_access_flag
    (flagReg sizeReg roundReg endReg offReg : Reg) : Program :=
  mload_compute_rounded_access_end roundReg endReg offReg ;;
  mload_compute_expand_flag flagReg sizeReg roundReg

abbrev mload_compute_rounded_access_flag_code
    (flagReg sizeReg roundReg endReg offReg : Reg) (base : Word) : CodeReq :=
  (mload_compute_rounded_access_end_code roundReg endReg offReg base).union
    (mload_compute_expand_flag_code flagReg sizeReg roundReg (base + 12))

theorem mload_compute_rounded_access_flag_code_eq_ofProg
    (flagReg sizeReg roundReg endReg offReg : Reg) (base : Word) :
    mload_compute_rounded_access_flag_code flagReg sizeReg roundReg endReg offReg base =
      CodeReq.ofProg base
        (mload_compute_rounded_access_flag flagReg sizeReg roundReg endReg offReg) := by
  unfold mload_compute_rounded_access_flag_code mload_compute_rounded_access_flag
    mload_compute_rounded_access_end_code mload_compute_expand_flag_code
    mload_compute_rounded_access_end mload_compute_access_end mload_round_access_end
    mload_compute_expand_flag mload_compute_access_end_code mload_round_access_end_code
    ADDI ANDI single seq
  change ((CodeReq.singleton base (Instr.ADDI endReg offReg 32)).union
      ((CodeReq.singleton (base + 4) (Instr.ADDI roundReg endReg 31)).union
        (CodeReq.singleton ((base + 4) + 4)
          (Instr.ANDI roundReg roundReg (-32))))).union
      (CodeReq.singleton (base + 12) (Instr.SLTU flagReg sizeReg roundReg)) =
    CodeReq.ofProg base [Instr.ADDI endReg offReg 32,
      Instr.ADDI roundReg endReg 31, Instr.ANDI roundReg roundReg (-32),
      Instr.SLTU flagReg sizeReg roundReg]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_cons,
    CodeReq.ofProg_cons, CodeReq.ofProg_nil, CodeReq.union_empty_right]
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega]
  rw [show (base + 8 : Word) + 4 = base + 12 from by bv_omega]
  rw [CodeReq.union_assoc, CodeReq.union_assoc]

/--
  Composed executable bridge for the rounded access-end arithmetic and the
  unsigned comparison against the current memory size.
-/
theorem mload_compute_rounded_access_flag_spec_within
    (flagReg sizeReg roundReg endReg offReg : Reg)
    (offset endOld roundOld sizeBytesWord flagOld : Word) (base : Word)
    (h_end_ne_x0 : endReg ≠ .x0)
    (h_round_ne_x0 : roundReg ≠ .x0)
    (h_flag_ne_x0 : flagReg ≠ .x0) :
    cpsTripleWithin 4 base (base + 16)
      (mload_compute_rounded_access_flag_code flagReg sizeReg roundReg endReg offReg base)
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld) **
       (roundReg ↦ᵣ roundOld) ** (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ flagOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12))) **
       (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ
        (if BitVec.ult sizeBytesWord
          (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12))
         then (1 : Word) else 0))) := by
  unfold mload_compute_rounded_access_flag_code
  let roundedAccessEnd :=
    (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12))
  have h_rounded :=
    mload_compute_rounded_access_end_spec_within roundReg endReg offReg
      offset endOld roundOld base h_end_ne_x0 h_round_ne_x0
  have h_flag :=
    mload_compute_expand_flag_spec_within flagReg sizeReg roundReg
      sizeBytesWord roundedAccessEnd flagOld (base + 12) h_flag_ne_x0
  rw [show (base + 12 : Word) + 4 = base + 16 from by bv_omega] at h_flag
  have hd :
      (mload_compute_rounded_access_end_code roundReg endReg offReg base).Disjoint
        (mload_compute_expand_flag_code flagReg sizeReg roundReg (base + 12)) := by
    unfold mload_compute_rounded_access_end_code mload_compute_access_end_code
      mload_round_access_end_code mload_compute_expand_flag_code
    exact CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton (by bv_omega))
      (CodeReq.Disjoint.union_left
        (CodeReq.Disjoint.singleton (by bv_omega))
        (CodeReq.Disjoint.singleton (by bv_omega)))
  have h_rounded_framed : cpsTripleWithin 3 base (base + 12)
      (mload_compute_rounded_access_end_code roundReg endReg offReg base)
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld) **
       (roundReg ↦ᵣ roundOld) ** (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ flagOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ roundedAccessEnd) ** (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ flagOld)) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((sizeReg ↦ᵣ sizeBytesWord) ** (flagReg ↦ᵣ flagOld)) (by pcFree)
        h_rounded)
  have h_flag_framed : cpsTripleWithin 1 (base + 12) (base + 16)
      (mload_compute_expand_flag_code flagReg sizeReg roundReg (base + 12))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ roundedAccessEnd) ** (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ flagOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ roundedAccessEnd) ** (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ
        (if BitVec.ult sizeBytesWord roundedAccessEnd then (1 : Word) else 0))) :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTripleWithin_frameL
        ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32))) (by pcFree)
        h_flag)
  exact cpsTripleWithin_seq hd h_rounded_framed h_flag_framed

theorem mload_compute_rounded_access_flag_ofProg_spec_within
    (flagReg sizeReg roundReg endReg offReg : Reg)
    (offset endOld roundOld sizeBytesWord flagOld : Word) (base : Word)
    (h_end_ne_x0 : endReg ≠ .x0)
    (h_round_ne_x0 : roundReg ≠ .x0)
    (h_flag_ne_x0 : flagReg ≠ .x0) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base
        (mload_compute_rounded_access_flag flagReg sizeReg roundReg endReg offReg))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ endOld) **
       (roundReg ↦ᵣ roundOld) ** (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ flagOld))
      ((offReg ↦ᵣ offset) ** (endReg ↦ᵣ (offset + 32)) **
       (roundReg ↦ᵣ (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12))) **
       (sizeReg ↦ᵣ sizeBytesWord) **
       (flagReg ↦ᵣ
        (if BitVec.ult sizeBytesWord
          (((offset + 32) + 31) &&& signExtend12 (-32 : BitVec 12))
         then (1 : Word) else 0))) := by
  rw [← mload_compute_rounded_access_flag_code_eq_ofProg]
  exact mload_compute_rounded_access_flag_spec_within
    flagReg sizeReg roundReg endReg offReg offset endOld roundOld sizeBytesWord flagOld
    base h_end_ne_x0 h_round_ne_x0 h_flag_ne_x0

/--
  Select the expanded MLOAD memory size after the comparison flag has been
  computed. If the flag is zero, keep the current size; otherwise copy the
  rounded access end into the size register.
-/
def mload_select_expanded_size
    (sizeReg roundReg flagReg : Reg) : Program :=
  single (.BEQ flagReg .x0 8) ;;
  ADDI sizeReg roundReg 0

abbrev mload_select_expanded_size_code
    (sizeReg roundReg flagReg : Reg) (base : Word) : CodeReq :=
  (CodeReq.singleton base (.BEQ flagReg .x0 8)).union
    (CodeReq.singleton (base + 4) (.ADDI sizeReg roundReg 0))

theorem mload_select_expanded_size_code_eq_ofProg
    (sizeReg roundReg flagReg : Reg) (base : Word) :
    mload_select_expanded_size_code sizeReg roundReg flagReg base =
      CodeReq.ofProg base (mload_select_expanded_size sizeReg roundReg flagReg) := by
  unfold mload_select_expanded_size_code mload_select_expanded_size ADDI single seq
  change (CodeReq.singleton base (Instr.BEQ flagReg .x0 8)).union
      (CodeReq.singleton (base + 4) (Instr.ADDI sizeReg roundReg 0)) =
    CodeReq.ofProg base [Instr.BEQ flagReg .x0 8, Instr.ADDI sizeReg roundReg 0]
  rw [CodeReq.ofProg_cons, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]

/--
  Branching bridge for the MLOAD memory high-water select stage. The taken
  path skips the copy when the comparison flag is zero; the fall-through path
  proceeds to the copy instruction when the flag is nonzero.
-/
theorem mload_select_expanded_size_spec_within
    (sizeReg roundReg flagReg : Reg)
    (sizeOld roundedAccessEnd flagVal : Word) (base : Word) :
    cpsBranchWithin 1 base
      (mload_select_expanded_size_code sizeReg roundReg flagReg base)
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd))
      (base + 8)
        ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
         (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
         ⌜flagVal = (0 : Word)⌝)
      (base + 4)
        ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
         (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
         ⌜flagVal ≠ (0 : Word)⌝) := by
  unfold mload_select_expanded_size_code
  have hbeq :=
    beq_spec_gen_within flagReg .x0 (8 : BitVec 13) flagVal (0 : Word) base
  have hbeq_framed : cpsBranchWithin 1 base
      (CodeReq.singleton base (Instr.BEQ flagReg .x0 8))
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd))
      (base + 8)
        ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
         (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
         ⌜flagVal = (0 : Word)⌝)
      (base + 4)
        ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
         (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
         ⌜flagVal ≠ (0 : Word)⌝) := by
    exact cpsBranchWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranchWithin_frameR
        ((sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd)) (by pcFree)
        hbeq)
  exact cpsBranchWithin_extend_code
    (cr' := (CodeReq.singleton base (Instr.BEQ flagReg .x0 8)).union
      (CodeReq.singleton (base + 4) (Instr.ADDI sizeReg roundReg 0)))
    (h := hbeq_framed)
    (hmono := CodeReq.union_mono_left)

theorem mload_select_expanded_size_ofProg_spec_within
    (sizeReg roundReg flagReg : Reg)
    (sizeOld roundedAccessEnd flagVal : Word) (base : Word) :
    cpsBranchWithin 1 base
      (CodeReq.ofProg base (mload_select_expanded_size sizeReg roundReg flagReg))
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd))
      (base + 8)
        ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
         (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
         ⌜flagVal = (0 : Word)⌝)
      (base + 4)
        ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
         (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
         ⌜flagVal ≠ (0 : Word)⌝) := by
  rw [← mload_select_expanded_size_code_eq_ofProg]
  exact mload_select_expanded_size_spec_within
    sizeReg roundReg flagReg sizeOld roundedAccessEnd flagVal base

/--
  Fall-through copy step for `mload_select_expanded_size`: when the dispatch
  does not branch, this instruction copies the rounded access end into the
  size register.
-/
theorem mload_select_expanded_size_copy_spec_within
    (sizeReg roundReg flagReg : Reg)
    (sizeOld roundedAccessEnd flagVal : Word) (base : Word)
    (h_size_ne_x0 : sizeReg ≠ .x0) :
    cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (Instr.ADDI sizeReg roundReg 0))
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd))
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ roundedAccessEnd) ** (roundReg ↦ᵣ roundedAccessEnd)) := by
  have haddi :=
    addi_spec_gen_within sizeReg roundReg sizeOld roundedAccessEnd
      (0 : BitVec 12) (base + 4) h_size_ne_x0
  simp only [signExtend12_0] at haddi
  rw [EvmAsm.Rv64.AddrNorm.word_add_zero] at haddi
  rw [show (base + 4 : Word) + 4 = base + 8 from by bv_omega] at haddi
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTripleWithin_frameL
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word))) (by pcFree)
      haddi)

/--
  Composed select bridge for the MLOAD memory high-water update. The branch
  keeps the old memory size when the comparison flag is zero and otherwise
  executes the copy step that selects the rounded access end.
-/
theorem mload_select_expanded_size_merged_spec_within
    (sizeReg roundReg flagReg : Reg)
    (sizeOld roundedAccessEnd flagVal : Word) (base : Word)
    (h_size_ne_x0 : sizeReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mload_select_expanded_size_code sizeReg roundReg flagReg base)
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd))
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ
        (if flagVal = (0 : Word) then sizeOld else roundedAccessEnd)) **
       (roundReg ↦ᵣ roundedAccessEnd)) := by
  let finalPost : Assertion :=
    ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
     (sizeReg ↦ᵣ
      (if flagVal = (0 : Word) then sizeOld else roundedAccessEnd)) **
     (roundReg ↦ᵣ roundedAccessEnd))
  have hbr :=
    mload_select_expanded_size_spec_within
      sizeReg roundReg flagReg sizeOld roundedAccessEnd flagVal base
  have ht_empty : cpsTripleWithin 1 (base + 8) (base + 8) CodeReq.empty
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
       ⌜flagVal = (0 : Word)⌝)
      finalPost :=
    cpsTripleWithin_mono_nSteps (by decide)
      (cpsTripleWithin_refl (fun h hp => by
        open EvmAsm.Rv64.Tactics in extract_pure hp
        obtain ⟨h_eq, hp⟩ := hp
        simp only [finalPost, if_pos h_eq]
        xperm_hyp hp))
  have ht : cpsTripleWithin 1 (base + 8) (base + 8)
      (mload_select_expanded_size_code sizeReg roundReg flagReg base)
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
       ⌜flagVal = (0 : Word)⌝)
      finalPost :=
    cpsTripleWithin_extend_code (fun a i h => by
      simp [CodeReq.empty] at h)
      ht_empty
  have hf_raw :=
    mload_select_expanded_size_copy_spec_within
      sizeReg roundReg flagReg sizeOld roundedAccessEnd flagVal base h_size_ne_x0
  have hf_with_pure : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (Instr.ADDI sizeReg roundReg 0))
      (((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd)) **
       ⌜flagVal ≠ (0 : Word)⌝)
      (((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
        (sizeReg ↦ᵣ roundedAccessEnd) ** (roundReg ↦ᵣ roundedAccessEnd)) **
       ⌜flagVal ≠ (0 : Word)⌝) :=
    cpsTripleWithin_frameR ⌜flagVal ≠ (0 : Word)⌝ (by pcFree) hf_raw
  have hf_single : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) (Instr.ADDI sizeReg roundReg 0))
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
       ⌜flagVal ≠ (0 : Word)⌝)
      finalPost :=
    cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        open EvmAsm.Rv64.Tactics in extract_pure hp
        obtain ⟨hp, h_ne⟩ := hp
        simp only [finalPost, if_neg h_ne]
        xperm_hyp hp)
      hf_with_pure
  have hf : cpsTripleWithin 1 (base + 4) (base + 8)
      (mload_select_expanded_size_code sizeReg roundReg flagReg base)
      ((flagReg ↦ᵣ flagVal) ** (.x0 ↦ᵣ (0 : Word)) **
       (sizeReg ↦ᵣ sizeOld) ** (roundReg ↦ᵣ roundedAccessEnd) **
       ⌜flagVal ≠ (0 : Word)⌝)
      finalPost :=
    cpsTripleWithin_extend_code (fun a i h => by
      unfold mload_select_expanded_size_code
      unfold CodeReq.union
      unfold CodeReq.singleton at h ⊢
      by_cases ha4 : a == base + 4
      · simp at h
        obtain ⟨ha_eq, hi_eq⟩ := h
        by_cases hb : a == base
        ·
          have hb_eq : a = base := by simpa using hb
          bv_omega
        · simp [ha_eq, hi_eq]
      · simp at h
        obtain ⟨ha_eq, _hi_eq⟩ := h
        have ha4_true : (a == base + 4) = true := by simp [ha_eq]
        exact False.elim (ha4 ha4_true))
      hf_single
  simpa only [Nat.reduceAdd, finalPost] using
    cpsBranchWithin_merge_same_cr hbr ht hf

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
