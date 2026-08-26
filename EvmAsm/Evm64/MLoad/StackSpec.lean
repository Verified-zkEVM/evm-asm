/-
  EvmAsm.Evm64.MLoad.StackSpec

  Stack-level bridge helpers for MLOAD.
-/

module

public import EvmAsm.Evm64.Stack
public import EvmAsm.Evm64.MLoad.Spec
public import EvmAsm.Evm64.MLoad.UnalignedSpec

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for all four MLOAD output-limb byte-pack blocks, placed after the
    two-instruction address prologue. -/
def mloadFourLimbsCode
    (addrReg byteReg accReg : Reg) (base : Word) : CodeReq :=
  (mloadOneLimbCode addrReg byteReg accReg
      24 25 26 27 28 29 30 31 0 (base + 8)).union
    ((mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100)).union
      ((mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)).union
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284))))

/-- Program form of the four MLOAD output-limb byte-pack blocks, placed after
    the two-instruction address prologue. -/
def mloadFourLimbsProg
    (addrReg byteReg accReg : Reg) : Program :=
  mloadTwoLimbsProg addrReg byteReg accReg
    24 25 26 27 28 29 30 31 0
    16 17 18 19 20 21 22 23 8 ;;
  mloadTwoLimbsProg addrReg byteReg accReg
    8 9 10 11 12 13 14 15 16
    0 1 2 3 4 5 6 7 24

theorem mloadFourLimbsCode_eq_ofProg
    (addrReg byteReg accReg : Reg) (base : Word) :
    mloadFourLimbsCode addrReg byteReg accReg base =
      CodeReq.ofProg (base + 8)
        (mloadFourLimbsProg addrReg byteReg accReg) := by
  have hshape :
      mloadFourLimbsCode addrReg byteReg accReg base =
        (mloadTwoLimbsCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0
          16 17 18 19 20 21 22 23 8 (base + 8)).union
        (mloadTwoLimbsCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16
          0 1 2 3 4 5 6 7 24 (base + 192)) := by
    unfold mloadFourLimbsCode mloadTwoLimbsCode
    rw [← CodeReq.union_assoc]
    rw [show (base + 8 : Word) + 92 = base + 100 from by bv_addr]
    rw [show (base + 192 : Word) + 92 = base + 284 from by bv_addr]
  rw [hshape, mloadTwoLimbsCode_eq_ofProg, mloadTwoLimbsCode_eq_ofProg]
  let p1 := mloadTwoLimbsProg addrReg byteReg accReg
    24 25 26 27 28 29 30 31 0
    16 17 18 19 20 21 22 23 8
  let p2 := mloadTwoLimbsProg addrReg byteReg accReg
    8 9 10 11 12 13 14 15 16
    0 1 2 3 4 5 6 7 24
  change (CodeReq.ofProg (base + 8) p1).union (CodeReq.ofProg (base + 192) p2) =
    CodeReq.ofProg (base + 8) (List.append p1 p2)
  rw [show base + 192 = (base + 8) + BitVec.ofNat 64 (4 * p1.length) from by
    unfold p1 mloadTwoLimbsProg mloadOneLimbProg mloadBytePackEightProg
      LBU SLLI OR' SD single seq
    symm
    bv_addr]
  exact (@CodeReq.ofProg_append (base + 8) p1 p2).symm

/-- Compact CodeReq for the full MLOAD program: address prologue followed by
    the four unaligned output-limb blocks. -/
def mloadStackCode
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) : CodeReq :=
  (mloadPrologueCode offReg addrReg memBaseReg base).union
    (mloadFourLimbsCode addrReg byteReg accReg base)

theorem mloadStackCode_prologue_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mloadPrologueCode offReg addrReg memBaseReg base) a = some i →
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  unfold mloadStackCode
  exact CodeReq.union_mono_left

theorem mloadPrologueCode_disjoint_mloadFourLimbsCode
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadPrologueCode offReg addrReg memBaseReg base)
      (mloadFourLimbsCode addrReg byteReg accReg base) := by
  rw [mloadFourLimbsCode_eq_ofProg]
  unfold mloadPrologueCode
  refine CodeReq.Disjoint.union_left ?_ ?_
  · apply CodeReq.Disjoint.singleton_ofProg
    apply CodeReq.ofProg_none_range
    intro k hk h_eq
    have hk_lt : k < 92 := by
      simpa [mloadFourLimbsProg, mloadTwoLimbsProg, mloadOneLimbProg,
        mloadBytePackEightProg, LBU, SLLI, OR', SD, single, seq] using hk
    have h_ne :
        base ≠ (base + 8) + BitVec.ofNat 64 (4 * k) := by
      bv_omega
    exact h_ne h_eq
  · apply CodeReq.Disjoint.singleton_ofProg
    apply CodeReq.ofProg_none_range
    intro k hk h_eq
    have hk_lt : k < 92 := by
      simpa [mloadFourLimbsProg, mloadTwoLimbsProg, mloadOneLimbProg,
        mloadBytePackEightProg, LBU, SLLI, OR', SD, single, seq] using hk
    have h_ne :
        base + 4 ≠ (base + 8) + BitVec.ofNat 64 (4 * k) := by
      bv_omega
    exact h_ne h_eq

theorem mloadStackCode_four_limbs_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i, (mloadFourLimbsCode addrReg byteReg accReg base) a = some i →
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  unfold mloadStackCode
  exact CodeReq.mono_union_right
    (mloadPrologueCode_disjoint_mloadFourLimbsCode
      offReg byteReg accReg addrReg memBaseReg base)
    (fun _ _ h => h)

/-- Decompose `evm_mload` as the two-instruction address prologue followed by
    the four output-limb byte-pack blocks (`mloadFourLimbsProg`).  This is the
    program-level analog of `mloadStackCode = mloadPrologueCode ∪ mloadFourLimbsCode`
    and bridges the program produced by `Program.lean` (a right-nested
    `;;` chain of `mload_one_limb` blocks) to the bundled `mloadFourLimbsProg`
    used by the stack-spec compositions.

    Distinctive token: evm_mload_eq_prologue_append_mloadFourLimbsProg #53. -/
theorem evm_mload_eq_prologue_append_mloadFourLimbsProg
    (offReg byteReg accReg addrReg memBaseReg : Reg) :
    evm_mload offReg byteReg accReg addrReg memBaseReg =
      (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) ++
        mloadFourLimbsProg addrReg byteReg accReg := by
  rfl

/-- Program form of the full MLOAD stack helper: load the offset, compute the
    target memory address, then unpack all four output limbs.  Direct MLOAD
    analog of `mstoreStackProg`. -/
def mloadStackProg
    (offReg byteReg accReg addrReg memBaseReg : Reg) : Program :=
  (LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg) ;;
  mloadFourLimbsProg addrReg byteReg accReg

/-- `mloadStackCode = ofProg base mloadStackProg`.  Direct MLOAD analog of
    `mstoreStackCode_eq_ofProg`. -/
theorem mloadStackCode_eq_ofProg
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    mloadStackCode offReg byteReg accReg addrReg memBaseReg base =
      CodeReq.ofProg base
        (mloadStackProg offReg byteReg accReg addrReg memBaseReg) := by
  unfold mloadStackCode mloadStackProg seq
  rw [mloadPrologueCode_eq_ofProg, mloadFourLimbsCode_eq_ofProg]
  let p0 : List Instr := LD offReg .x12 0 ;; ADD addrReg memBaseReg offReg
  let p1 : List Instr := mloadFourLimbsProg addrReg byteReg accReg
  change (CodeReq.ofProg base p0).union (CodeReq.ofProg (base + 8) p1) =
    CodeReq.ofProg base (p0 ++ p1)
  rw [show base + 8 = base + BitVec.ofNat 64 (4 * p0.length) by
    rw [show p0.length = 2 by
      unfold p0 LD ADD single seq
      rfl]
    rfl]
  exact (CodeReq.ofProg_append (base := base) (p1 := p0) (p2 := p1)).symm

/-- The bundled `mloadStackProg` is exactly the `evm_mload` instruction
    sequence.  Direct MLOAD analog of `mstoreStackProg_eq_evm_mstore`. -/
theorem mloadStackProg_eq_evm_mload
    (offReg byteReg accReg addrReg memBaseReg : Reg) :
    mloadStackProg offReg byteReg accReg addrReg memBaseReg =
      evm_mload offReg byteReg accReg addrReg memBaseReg :=
  (evm_mload_eq_prologue_append_mloadFourLimbsProg
    offReg byteReg accReg addrReg memBaseReg).symm

/-- `evm_mload_code = mloadStackCode` as `CodeReq`s.  Both encode the same
    94 instructions placed at `base..base+376`; the equality lets stack-level
    triples proved over `mloadStackCode` (e.g.
    `mload_combined_*_stack_spec_within`) be transported to `evm_mload_code`
    without any manual lifting.

    Distinctive token: mloadStackCode_eq_evm_mload_code #53. -/
theorem mloadStackCode_eq_evm_mload_code
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    mloadStackCode offReg byteReg accReg addrReg memBaseReg base =
      evm_mload_code offReg byteReg accReg addrReg memBaseReg base := by
  rw [mloadStackCode_eq_ofProg,
    mloadStackProg_eq_evm_mload offReg byteReg accReg addrReg memBaseReg]

/-- Sub-CodeReq lift: anything `mloadStackCode` defines, `evm_mload_code` also
    defines.  Companion to `evm_mload_code_prologue_sub` covering the entire
    `mloadStackCode` surface in one step.

    Distinctive token: evm_mload_code_stack_sub #53. -/
theorem evm_mload_code_stack_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i →
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  rw [mloadStackCode_eq_evm_mload_code]
  intro _ _ h; exact h

/-- Transport a `cpsTripleWithin` over `mloadStackCode` to one over
    `evm_mload_code`.  Subsequent slices use this to land
    `evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53 follow-up) by
    composing the existing `mload_combined_*_stack_spec_within` lemmas
    (over `mloadStackCode`) with concrete byte-load triples.

    Distinctive token: cpsTripleWithin_evm_mload_of_stack #53. -/
theorem cpsTripleWithin_evm_mload_of_stack
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base pcEnd : Word)
    (h :
      cpsTripleWithin n base pcEnd
        (mloadStackCode offReg byteReg accReg addrReg memBaseReg base) P Q) :
    cpsTripleWithin n base pcEnd
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mload_code_stack_sub
      offReg byteReg accReg addrReg memBaseReg base)

theorem mload_prologue_stack_spec_within
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
       (sp ↦ₘ offset)) := by
  exact cpsTripleWithin_extend_code
    (h := mload_prologue_spec_within offReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)
    (hmono := mloadStackCode_prologue_sub offReg byteReg accReg addrReg memBaseReg base)

theorem mload_four_limb_sequence_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadFourLimbsCode addrReg byteReg accReg base) P0 P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (mloadFourLimbsCode addrReg byteReg accReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (mloadFourLimbsCode addrReg byteReg accReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (mloadFourLimbsCode addrReg byteReg accReg base) P3 P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 376)
      (mloadFourLimbsCode addrReg byteReg accReg base) P0 P4 := by
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr h0 h1)
      h2)
    h3

/-- Subsumption witness: the q0 (least-significant) one-limb byte-pack block,
    placed at `base + 8 .. base + 100`, is the leftmost union member of
    `mloadFourLimbsCode`. Proved by left-bias of `CodeReq.union`.

    Consumer: `calldataload_window_one_limb_q0_stack_spec_within`
    (Calldata/LoadStackCode.lean) which lets callers supply a concrete
    `mloadOneLimbCode` byte-load triple in place of an `mloadFourLimbsCode`
    triple when wiring the four-limb byte-window read in
    `evm_calldataload_stack_spec` (evm-asm-pgeuo / GH #104). -/
theorem mloadFourLimbsCode_one_limb_q0_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8)) a = some i →
      (mloadFourLimbsCode addrReg byteReg accReg base) a = some i := by
  unfold mloadFourLimbsCode
  exact CodeReq.union_mono_left

/-- Disjointness of the q0 and q1 one-limb byte-pack blocks within
    `mloadFourLimbsCode`. q0 spans `base + 8 .. base + 100`, q1 spans
    `base + 100 .. base + 192`; both are 23-instruction `mloadOneLimbProg`
    blocks expressible as `CodeReq.ofProg`. -/
private theorem mloadFourLimbs_q0_disjoint_q1
    (addrReg byteReg accReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100)) := by
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  refine CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 23 ?_ ?_ ?_
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · intro k1 k2 hk1 hk2; bv_omega

/-- Subsumption witness: the q1 one-limb byte-pack block, placed at
    `base + 100 .. base + 192`, is the second union member of
    `mloadFourLimbsCode`. Proved by stepping past the q0 head with
    `mono_union_right` (using disjointness with q0) into the leftmost
    position of the inner union via `union_mono_left`.

    Consumer: `calldataload_window_one_limb_q1_stack_spec_within`
    (Calldata/LoadStackCode.lean) — sister to the q0 witness. -/
theorem mloadFourLimbsCode_one_limb_q1_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) a = some i →
      (mloadFourLimbsCode addrReg byteReg accReg base) a = some i := by
  unfold mloadFourLimbsCode
  exact CodeReq.mono_union_right
    (mloadFourLimbs_q0_disjoint_q1 addrReg byteReg accReg base)
    CodeReq.union_mono_left

/-- Disjointness of the q0 and q2 one-limb byte-pack blocks within
    `mloadFourLimbsCode`. q0 spans `base + 8 .. base + 100`, q2 spans
    `base + 192 .. base + 284`; both are 23-instruction `mloadOneLimbProg`
    blocks expressible as `CodeReq.ofProg`. -/
private theorem mloadFourLimbs_q0_disjoint_q2
    (addrReg byteReg accReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192)) := by
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  refine CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 23 ?_ ?_ ?_
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · intro k1 k2 hk1 hk2; bv_omega

/-- Disjointness of the q1 and q2 one-limb byte-pack blocks within
    `mloadFourLimbsCode`. q1 spans `base + 100 .. base + 192`, q2 spans
    `base + 192 .. base + 284`; both are 23-instruction `mloadOneLimbProg`
    blocks expressible as `CodeReq.ofProg`. -/
private theorem mloadFourLimbs_q1_disjoint_q2
    (addrReg byteReg accReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100))
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192)) := by
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  refine CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 23 ?_ ?_ ?_
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · intro k1 k2 hk1 hk2; bv_omega

/-- Subsumption witness: the q2 one-limb byte-pack block, placed at
    `base + 192 .. base + 284`, is the third union member of
    `mloadFourLimbsCode`. Proved by stepping past q0 and q1 with
    `mono_union_right` (using disjointness with each), then taking
    `union_mono_left` into the leftmost position of the innermost union.

    Consumer: `calldataload_window_one_limb_q2_stack_spec_within`
    (Calldata/LoadStackCode.lean) — sister to the q0 / q1 witnesses. -/
theorem mloadFourLimbsCode_one_limb_q2_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) a = some i →
      (mloadFourLimbsCode addrReg byteReg accReg base) a = some i := by
  unfold mloadFourLimbsCode
  exact CodeReq.mono_union_right
    (mloadFourLimbs_q0_disjoint_q2 addrReg byteReg accReg base)
    (CodeReq.mono_union_right
      (mloadFourLimbs_q1_disjoint_q2 addrReg byteReg accReg base)
      CodeReq.union_mono_left)

/-- Disjointness of the q0 and q3 one-limb byte-pack blocks within
    `mloadFourLimbsCode`. q0 spans `base + 8 .. base + 100`, q3 spans
    `base + 284 .. base + 376`; both are 23-instruction `mloadOneLimbProg`
    blocks expressible as `CodeReq.ofProg`. -/
private theorem mloadFourLimbs_q0_disjoint_q3
    (addrReg byteReg accReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284)) := by
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  refine CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 23 ?_ ?_ ?_
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · intro k1 k2 hk1 hk2; bv_omega

/-- Disjointness of the q1 and q3 one-limb byte-pack blocks within
    `mloadFourLimbsCode`. q1 spans `base + 100 .. base + 192`, q3 spans
    `base + 284 .. base + 376`; both are 23-instruction `mloadOneLimbProg`
    blocks expressible as `CodeReq.ofProg`. -/
private theorem mloadFourLimbs_q1_disjoint_q3
    (addrReg byteReg accReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100))
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284)) := by
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  refine CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 23 ?_ ?_ ?_
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · intro k1 k2 hk1 hk2; bv_omega

/-- Disjointness of the q2 and q3 one-limb byte-pack blocks within
    `mloadFourLimbsCode`. q2 spans `base + 192 .. base + 284`, q3 spans
    `base + 284 .. base + 376`; both are 23-instruction `mloadOneLimbProg`
    blocks expressible as `CodeReq.ofProg`. -/
private theorem mloadFourLimbs_q2_disjoint_q3
    (addrReg byteReg accReg : Reg) (base : Word) :
    CodeReq.Disjoint
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192))
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284)) := by
  rw [mloadOneLimbCode_eq_ofProg, mloadOneLimbCode_eq_ofProg]
  refine CodeReq.ofProg_disjoint_range_len _ _ 23 _ _ 23 ?_ ?_ ?_
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · unfold mloadOneLimbProg mloadBytePackEightProg LBU SLLI OR' SD single seq; rfl
  · intro k1 k2 hk1 hk2; bv_omega

/-- Subsumption witness: the q3 one-limb byte-pack block, placed at
    `base + 284 .. base + 376`, is the fourth (rightmost) union member of
    `mloadFourLimbsCode`. Proved by stepping past q0, q1, and q2 with
    `mono_union_right` (using disjointness with each), reaching the tail
    position of the innermost union which is itself the q3 block.

    Consumer: `calldataload_window_one_limb_q3_stack_spec_within`
    (Calldata/LoadStackCode.lean) — sister to the q0 / q1 / q2 witnesses,
    closing the four sub-slices of `evm-asm-pgeuo` (#104). -/
theorem mloadFourLimbsCode_one_limb_q3_sub
    (addrReg byteReg accReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) a = some i →
      (mloadFourLimbsCode addrReg byteReg accReg base) a = some i := by
  unfold mloadFourLimbsCode
  exact CodeReq.mono_union_right
    (mloadFourLimbs_q0_disjoint_q3 addrReg byteReg accReg base)
    (CodeReq.mono_union_right
      (mloadFourLimbs_q1_disjoint_q3 addrReg byteReg accReg base)
      (CodeReq.mono_union_right
        (mloadFourLimbs_q2_disjoint_q3 addrReg byteReg accReg base)
        (fun _ _ h => h)))

theorem mload_four_limbs_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 376)
        (mloadFourLimbsCode addrReg byteReg accReg base) P Q) :
    cpsTripleWithin n (base + 8) (base + 376)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base) P Q := by
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := mloadStackCode_four_limbs_sub
      offReg byteReg accReg addrReg memBaseReg base)

/--
MLOAD combined stack spec: sequentially compose the prologue half
(`mload_prologue_stack_spec_within`) with a caller-supplied four-limbs
core triple (over `mloadStackCode`) via `cpsTripleWithin_seq_same_cr`.

Direct MLOAD analog of
`Calldata.LoadStackCode.calldataload_window_combined_stack_spec_within`.
The prologue threads `(sp ↦ₘ offset)` and the resolved address registers
through to the four-limbs side; the caller only needs to supply a
four-limbs triple whose precondition matches the prologue's postcondition
(after the `addrReg ← memBase + offset` resolve) and whose postcondition
is an arbitrary `Q`.

Foundation lemma toward the upcoming `evm_mload_stack_spec_within`
(evm-asm-lrhou / GH #53 follow-up): subsequent slices instantiate the
four-limbs hypothesis with a concrete byte-window read (e.g. via
`mload_four_limbs_stack_spec_within` together with a concrete byte-window
core spec).

Distinctive token: mload_combined_stack_spec_within #53.
-/
theorem mload_combined_stack_spec_within
    {n : Nat} {Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h4 :
      cpsTripleWithin n (base + 8) (base + 376)
        (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        Q) :
    cpsTripleWithin (2 + n) base (base + 376)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_seq_same_cr
    (mload_prologue_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0)
    h4

/--
MLOAD combined four-limb sequence stack spec: combine the prologue half
(`mload_prologue_stack_spec_within`) with the four byte-window quarter
triples (composed via `mload_four_limb_sequence_spec_within`) into a single
triple from `base` to `base + 376` over `mloadStackCode`.

Direct MLOAD analog of
`Calldata.LoadStackCode.calldataload_window_combined_four_limb_sequence_stack_spec_within`.
This is a one-line composition of `mload_combined_stack_spec_within` (which
takes a single four-limbs core triple over `mloadStackCode`) with
`mload_four_limb_sequence_spec_within` (which produces that consolidated
four-limbs triple from four quarter triples over `mloadFourLimbsCode`),
transported to `mloadStackCode` via `mload_four_limbs_stack_spec_within`.

Subsequent slices instantiate each `hN` with a concrete byte-load triple
to land the full `evm_mload_stack_spec_within` (evm-asm-lrhou /
GH #53 follow-up) without re-doing the prologue/transport plumbing.

Distinctive token: mload_combined_four_limb_sequence_stack_spec_within #53.
-/
theorem mload_combined_four_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadFourLimbsCode addrReg byteReg accReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (mloadFourLimbsCode addrReg byteReg accReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (mloadFourLimbsCode addrReg byteReg accReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (mloadFourLimbsCode addrReg byteReg accReg base) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 376)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  mload_combined_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
    (mload_four_limbs_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg base
      (mload_four_limb_sequence_spec_within
        addrReg byteReg accReg base h0 h1 h2 h3))

/--
MLOAD q0 one-limb spec on `mloadFourLimbsCode`: transport a concrete
`mloadOneLimbCode` byte-load triple at `base + 8 .. base + 100` (the
leftmost one-limb byte-pack block within `mloadFourLimbsCode`) to the
larger `mloadFourLimbsCode` surface via `mloadFourLimbsCode_one_limb_q0_sub`.

Lets followup MLOAD slices instantiate `h0` of
`mload_four_limb_sequence_spec_within` directly with a concrete byte-load
triple, mirroring the calldata `calldataload_window_one_limb_q0_stack_spec_within`
shape but at the `mloadFourLimbsCode` level (no prologue / `mloadStackCode`
lift).

Distinctive token: mload_one_limb_q0_spec_within #53.
-/
theorem mload_one_limb_q0_spec_within
    {n : Nat} {P Q : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8)) P Q) :
    cpsTripleWithin n (base + 8) (base + 100)
      (mloadFourLimbsCode addrReg byteReg accReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := mloadFourLimbsCode_one_limb_q0_sub addrReg byteReg accReg base)

/-- MLOAD q1 one-limb spec on `mloadFourLimbsCode`: sister to
`mload_one_limb_q0_spec_within` for the second one-limb byte-pack block
at `base + 100 .. base + 192`. -/
theorem mload_one_limb_q1_spec_within
    {n : Nat} {P Q : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 100) (base + 192)
        (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) P Q) :
    cpsTripleWithin n (base + 100) (base + 192)
      (mloadFourLimbsCode addrReg byteReg accReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := mloadFourLimbsCode_one_limb_q1_sub addrReg byteReg accReg base)

/-- MLOAD q2 one-limb spec on `mloadFourLimbsCode`: sister to
`mload_one_limb_q0/q1_spec_within` for the third one-limb byte-pack block
at `base + 192 .. base + 284`. -/
theorem mload_one_limb_q2_spec_within
    {n : Nat} {P Q : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 192) (base + 284)
        (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) P Q) :
    cpsTripleWithin n (base + 192) (base + 284)
      (mloadFourLimbsCode addrReg byteReg accReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := mloadFourLimbsCode_one_limb_q2_sub addrReg byteReg accReg base)

/-- MLOAD q3 one-limb spec on `mloadFourLimbsCode`: sister to
`mload_one_limb_q{0,1,2}_spec_within` for the fourth (most-significant)
one-limb byte-pack block at `base + 284 .. base + 376`. -/
theorem mload_one_limb_q3_spec_within
    {n : Nat} {P Q : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 284) (base + 376)
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) P Q) :
    cpsTripleWithin n (base + 284) (base + 376)
      (mloadFourLimbsCode addrReg byteReg accReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := mloadFourLimbsCode_one_limb_q3_sub addrReg byteReg accReg base)

/--
MLOAD one-limb sequence spec on `mloadFourLimbsCode`: compose the four
per-quarter `mload_one_limb_q{0,1,2,3}_spec_within` transports into a
single `cpsTripleWithin` over `(base + 8) .. (base + 376)` taking four
concrete `mloadOneLimbCode` byte-load triples (h0, h1, h2, h3) directly.
Mirrors `mload_four_limb_sequence_spec_within` but on the smaller
`mloadOneLimbCode` surface — eliminates an intermediate transport step
when wiring concrete byte-load triples for the upcoming
`evm_mload_stack_spec_within`.

Distinctive token: mload_one_limb_sequence_spec_within #53.
-/
theorem mload_one_limb_sequence_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (addrReg byteReg accReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8)) P0 P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) P3 P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 376)
      (mloadFourLimbsCode addrReg byteReg accReg base) P0 P4 :=
  mload_four_limb_sequence_spec_within addrReg byteReg accReg base
    (mload_one_limb_q0_spec_within addrReg byteReg accReg base h0)
    (mload_one_limb_q1_spec_within addrReg byteReg accReg base h1)
    (mload_one_limb_q2_spec_within addrReg byteReg accReg base h2)
    (mload_one_limb_q3_spec_within addrReg byteReg accReg base h3)

/--
MLOAD combined one-limb sequence stack spec: combine the prologue half
(`mload_prologue_stack_spec_within`) with the four byte-window quarter
triples on `mloadOneLimbCode` (composed via
`mload_one_limb_sequence_spec_within`) and lifted to `mloadStackCode`
via `mload_four_limbs_stack_spec_within`, into a single triple from
`base` to `base + 376` over `mloadStackCode`.

Direct MLOAD analog of
`Calldata.LoadStackCode.calldataload_window_combined_four_limb_sequence_stack_spec_within`
but at the smaller `mloadOneLimbCode` granularity: subsequent slices
instantiate each `hN` with a concrete byte-load triple to land the full
`evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53 follow-up) without
re-doing the prologue + per-quarter subsumption + transport plumbing.

Distinctive token: mload_combined_one_limb_sequence_stack_spec_within #53.
-/
theorem mload_combined_one_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8))
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 376)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  mload_combined_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
    (mload_four_limbs_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg base
      (mload_one_limb_sequence_spec_within
        addrReg byteReg accReg base h0 h1 h2 h3))

/--
MLOAD evm_mload_code lift of `mload_combined_one_limb_sequence_stack_spec_within`:
the same combined prologue + four byte-pack one-limb triples, transported from
`mloadStackCode` to `evm_mload_code` via `cpsTripleWithin_evm_mload_of_stack`.

Subsequent slices toward `evm_mload_stack_spec_within` (evm-asm-lrhou / GH #53
follow-up) instantiate each `hN` with a concrete five-dword byte-load triple and
apply this helper to land a `cpsTripleWithin` over `evm_mload_code` in one step,
without re-applying the stack-code → evm_mload_code transport at every call
site. Direct analog of
`Calldata.calldataload_window_combined_one_limb_sequence_stack_spec_within`,
which already targets `evm_calldataload_window_code`.

Distinctive token: evm_mload_combined_one_limb_sequence_stack_spec_within #53.
-/
theorem evm_mload_combined_one_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8))
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_evm_mload_of_stack
    offReg byteReg accReg addrReg memBaseReg base (base + 376)
    (mload_combined_one_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
      h0 h1 h2 h3)

/--
MLOAD evm_mload_code lift of `mload_combined_stack_spec_within`: the same
combined prologue + single four-limbs body triple, transported from
`mloadStackCode` to `evm_mload_code` via `cpsTripleWithin_evm_mload_of_stack`.

Coarse-granularity sibling of `evm_mload_combined_one_limb_sequence_stack_spec_within`
and `evm_mload_combined_four_limb_sequence_stack_spec_within`: callers that
already produce a single consolidated four-limbs triple over `mloadStackCode`
(rather than four quarter triples) get a direct transport to `evm_mload_code`
without bundling/unbundling the quarters.

Distinctive token: evm_mload_combined_stack_spec_within #53.
-/
theorem evm_mload_combined_stack_spec_within
    {n : Nat} {Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h4 :
      cpsTripleWithin n (base + 8) (base + 376)
        (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        Q) :
    cpsTripleWithin (2 + n) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_evm_mload_of_stack
    offReg byteReg accReg addrReg memBaseReg base (base + 376)
    (mload_combined_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
      h4)

/--
MLOAD evm_mload_code lift of `mload_combined_four_limb_sequence_stack_spec_within`:
the same combined prologue + four `mloadFourLimbsCode` quarter triples, transported
from `mloadStackCode` to `evm_mload_code` via `cpsTripleWithin_evm_mload_of_stack`.

Sister of `evm_mload_combined_one_limb_sequence_stack_spec_within` but at the
coarser `mloadFourLimbsCode` granularity: callers supply each quarter triple over
the four-limbs body program (not over the per-byte one-limb program), useful
when the concrete byte-load triple is naturally produced at that surface (e.g.
via `mload_four_limbs_stack_spec_within` composition with byte-window subspecs).

Distinctive token: evm_mload_combined_four_limb_sequence_stack_spec_within #53.
-/
theorem evm_mload_combined_four_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadFourLimbsCode addrReg byteReg accReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (mloadFourLimbsCode addrReg byteReg accReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (mloadFourLimbsCode addrReg byteReg accReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (mloadFourLimbsCode addrReg byteReg accReg base) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_evm_mload_of_stack
    offReg byteReg accReg addrReg memBaseReg base (base + 376)
    (mload_combined_four_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
      h0 h1 h2 h3)

/--
  The 256-bit value loaded by MLOAD when each output limb is assembled from
  an adjacent low/high dword pair. The four limbs are stored in EVM-stack
  little-endian order: limb 0 at `sp`, limb 3 at `sp + 24`.
-/
def mloadLoadedWordFromDwordPairs
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) : EvmWord :=
  mloadLoadedWord
    (mloadPackedLimbFromDwordPair lo0 hi0 start0)
    (mloadPackedLimbFromDwordPair lo1 hi1 start1)
    (mloadPackedLimbFromDwordPair lo2 hi2 start2)
    (mloadPackedLimbFromDwordPair lo3 hi3 start3)

theorem getLimbN_mloadLoadedWordFromDwordPairs_0
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 0 =
    mloadPackedLimbFromDwordPair lo0 hi0 start0 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_0]

theorem getLimbN_mloadLoadedWordFromDwordPairs_1
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 1 =
    mloadPackedLimbFromDwordPair lo1 hi1 start1 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_1]

theorem getLimbN_mloadLoadedWordFromDwordPairs_2
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 2 =
    mloadPackedLimbFromDwordPair lo2 hi2 start2 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_2]

theorem getLimbN_mloadLoadedWordFromDwordPairs_3
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    (mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3).getLimbN 3 =
    mloadPackedLimbFromDwordPair lo3 hi3 start3 := by
  rw [mloadLoadedWordFromDwordPairs, getLimbN_mloadLoadedWord_3]

/--
  Fold the four unaligned dword-pair MLOAD destination limbs into one
  `evmWordIs` assertion.
-/
theorem mloadLoadedWordFromDwordPairs_evmWordIs_fold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair lo0 hi0 start0) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair lo1 hi1 start1) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair lo2 hi2 start2) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair lo3 hi3 start3)) =
    evmWordIs sp
      (mloadLoadedWordFromDwordPairs
        lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3) := by
  rw [mloadLoadedWordFromDwordPairs, mloadLoadedWord_evmWordIs_fold]

/--
  The dword-pair representation used by the unaligned executable proof is the
  same byte-level MLOAD word as `mloadLoadedWordFromBytes`. Pair 3 supplies
  bytes 0..7 (the most-significant EVM bytes); pair 0 supplies bytes 24..31
  (the least-significant EVM bytes stored at stack limb 0).
-/
theorem mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 =
    mloadLoadedWordFromBytes
      (mloadByteFromDwordPair lo3 hi3 start3 0)
      (mloadByteFromDwordPair lo3 hi3 start3 1)
      (mloadByteFromDwordPair lo3 hi3 start3 2)
      (mloadByteFromDwordPair lo3 hi3 start3 3)
      (mloadByteFromDwordPair lo3 hi3 start3 4)
      (mloadByteFromDwordPair lo3 hi3 start3 5)
      (mloadByteFromDwordPair lo3 hi3 start3 6)
      (mloadByteFromDwordPair lo3 hi3 start3 7)
      (mloadByteFromDwordPair lo2 hi2 start2 0)
      (mloadByteFromDwordPair lo2 hi2 start2 1)
      (mloadByteFromDwordPair lo2 hi2 start2 2)
      (mloadByteFromDwordPair lo2 hi2 start2 3)
      (mloadByteFromDwordPair lo2 hi2 start2 4)
      (mloadByteFromDwordPair lo2 hi2 start2 5)
      (mloadByteFromDwordPair lo2 hi2 start2 6)
      (mloadByteFromDwordPair lo2 hi2 start2 7)
      (mloadByteFromDwordPair lo1 hi1 start1 0)
      (mloadByteFromDwordPair lo1 hi1 start1 1)
      (mloadByteFromDwordPair lo1 hi1 start1 2)
      (mloadByteFromDwordPair lo1 hi1 start1 3)
      (mloadByteFromDwordPair lo1 hi1 start1 4)
      (mloadByteFromDwordPair lo1 hi1 start1 5)
      (mloadByteFromDwordPair lo1 hi1 start1 6)
      (mloadByteFromDwordPair lo1 hi1 start1 7)
      (mloadByteFromDwordPair lo0 hi0 start0 0)
      (mloadByteFromDwordPair lo0 hi0 start0 1)
      (mloadByteFromDwordPair lo0 hi0 start0 2)
      (mloadByteFromDwordPair lo0 hi0 start0 3)
      (mloadByteFromDwordPair lo0 hi0 start0 4)
      (mloadByteFromDwordPair lo0 hi0 start0 5)
      (mloadByteFromDwordPair lo0 hi0 start0 6)
      (mloadByteFromDwordPair lo0 hi0 start0 7) := by
  rfl

/--
  Direct stack fold for the unaligned executable result into the byte-level
  MLOAD semantic word.
-/
theorem mloadLoadedWordFromDwordPairs_evmWordIs_fold_bytes
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair lo0 hi0 start0) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair lo1 hi1 start1) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair lo2 hi2 start2) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair lo3 hi3 start3)) =
    evmWordIs sp
      (mloadLoadedWordFromBytes
        (mloadByteFromDwordPair lo3 hi3 start3 0)
        (mloadByteFromDwordPair lo3 hi3 start3 1)
        (mloadByteFromDwordPair lo3 hi3 start3 2)
        (mloadByteFromDwordPair lo3 hi3 start3 3)
        (mloadByteFromDwordPair lo3 hi3 start3 4)
        (mloadByteFromDwordPair lo3 hi3 start3 5)
        (mloadByteFromDwordPair lo3 hi3 start3 6)
        (mloadByteFromDwordPair lo3 hi3 start3 7)
        (mloadByteFromDwordPair lo2 hi2 start2 0)
        (mloadByteFromDwordPair lo2 hi2 start2 1)
        (mloadByteFromDwordPair lo2 hi2 start2 2)
        (mloadByteFromDwordPair lo2 hi2 start2 3)
        (mloadByteFromDwordPair lo2 hi2 start2 4)
        (mloadByteFromDwordPair lo2 hi2 start2 5)
        (mloadByteFromDwordPair lo2 hi2 start2 6)
        (mloadByteFromDwordPair lo2 hi2 start2 7)
        (mloadByteFromDwordPair lo1 hi1 start1 0)
        (mloadByteFromDwordPair lo1 hi1 start1 1)
        (mloadByteFromDwordPair lo1 hi1 start1 2)
        (mloadByteFromDwordPair lo1 hi1 start1 3)
        (mloadByteFromDwordPair lo1 hi1 start1 4)
        (mloadByteFromDwordPair lo1 hi1 start1 5)
        (mloadByteFromDwordPair lo1 hi1 start1 6)
        (mloadByteFromDwordPair lo1 hi1 start1 7)
        (mloadByteFromDwordPair lo0 hi0 start0 0)
        (mloadByteFromDwordPair lo0 hi0 start0 1)
        (mloadByteFromDwordPair lo0 hi0 start0 2)
        (mloadByteFromDwordPair lo0 hi0 start0 3)
        (mloadByteFromDwordPair lo0 hi0 start0 4)
        (mloadByteFromDwordPair lo0 hi0 start0 5)
        (mloadByteFromDwordPair lo0 hi0 start0 6)
        (mloadByteFromDwordPair lo0 hi0 start0 7)) := by
  rw [mloadLoadedWordFromDwordPairs_evmWordIs_fold]
  rw [mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes]

/--
  The byte-level MLOAD result word described by the four unaligned dword-pair
  source windows. This names the semantic word used by the final stack-level
  MLOAD theorem without exposing all 32 byte projections in that theorem's
  postcondition.
-/
def mloadStackOutputWordFromDwordPairs
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) : EvmWord :=
  mloadLoadedWordFromBytes
    (mloadByteFromDwordPair lo3 hi3 start3 0)
    (mloadByteFromDwordPair lo3 hi3 start3 1)
    (mloadByteFromDwordPair lo3 hi3 start3 2)
    (mloadByteFromDwordPair lo3 hi3 start3 3)
    (mloadByteFromDwordPair lo3 hi3 start3 4)
    (mloadByteFromDwordPair lo3 hi3 start3 5)
    (mloadByteFromDwordPair lo3 hi3 start3 6)
    (mloadByteFromDwordPair lo3 hi3 start3 7)
    (mloadByteFromDwordPair lo2 hi2 start2 0)
    (mloadByteFromDwordPair lo2 hi2 start2 1)
    (mloadByteFromDwordPair lo2 hi2 start2 2)
    (mloadByteFromDwordPair lo2 hi2 start2 3)
    (mloadByteFromDwordPair lo2 hi2 start2 4)
    (mloadByteFromDwordPair lo2 hi2 start2 5)
    (mloadByteFromDwordPair lo2 hi2 start2 6)
    (mloadByteFromDwordPair lo2 hi2 start2 7)
    (mloadByteFromDwordPair lo1 hi1 start1 0)
    (mloadByteFromDwordPair lo1 hi1 start1 1)
    (mloadByteFromDwordPair lo1 hi1 start1 2)
    (mloadByteFromDwordPair lo1 hi1 start1 3)
    (mloadByteFromDwordPair lo1 hi1 start1 4)
    (mloadByteFromDwordPair lo1 hi1 start1 5)
    (mloadByteFromDwordPair lo1 hi1 start1 6)
    (mloadByteFromDwordPair lo1 hi1 start1 7)
    (mloadByteFromDwordPair lo0 hi0 start0 0)
    (mloadByteFromDwordPair lo0 hi0 start0 1)
    (mloadByteFromDwordPair lo0 hi0 start0 2)
    (mloadByteFromDwordPair lo0 hi0 start0 3)
    (mloadByteFromDwordPair lo0 hi0 start0 4)
    (mloadByteFromDwordPair lo0 hi0 start0 5)
    (mloadByteFromDwordPair lo0 hi0 start0 6)
    (mloadByteFromDwordPair lo0 hi0 start0 7)

theorem mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    mloadStackOutputWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 =
    mloadLoadedWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 := by
  rw [mloadStackOutputWordFromDwordPairs]
  rw [mloadLoadedWordFromDwordPairs_eq_mloadLoadedWordFromBytes]

/--
  Named stack postcondition for the four output limbs of unaligned MLOAD.
  The executable composition can target this compact assertion and use
  `mloadStackOutputPost_evmWordIs_fold` to consume the four produced cells.
-/
@[irreducible]
def mloadStackOutputPost
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) : Assertion :=
  evmWordIs sp
    (mloadStackOutputWordFromDwordPairs
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3)

theorem mloadStackOutputPost_unfold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    mloadStackOutputPost sp
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 =
    evmWordIs sp
      (mloadStackOutputWordFromDwordPairs
        lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3) := by
  delta mloadStackOutputPost
  rfl

theorem mloadStackOutputPost_evmWordIs_fold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair lo0 hi0 start0) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair lo1 hi1 start1) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair lo2 hi2 start2) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair lo3 hi3 start3)) =
    mloadStackOutputPost sp
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 := by
  rw [mloadStackOutputPost_unfold]
  rw [mloadStackOutputWordFromDwordPairs_eq_mloadLoadedWordFromDwordPairs]
  rw [mloadLoadedWordFromDwordPairs_evmWordIs_fold]

theorem mloadStackOutputPost_evmStackIs_fold
    (sp : Word)
    (lo0 hi0 : Word) (start0 : Nat)
    (lo1 hi1 : Word) (start1 : Nat)
    (lo2 hi2 : Word) (start2 : Nat)
    (lo3 hi3 : Word) (start3 : Nat)
    (rest : List EvmWord) :
    (mloadStackOutputPost sp
      lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp
      (mloadStackOutputWordFromDwordPairs
        lo0 hi0 start0 lo1 hi1 start1 lo2 hi2 start2 lo3 hi3 start3 :: rest) := by
  rw [mloadStackOutputPost_unfold]
  rfl

/--
  The 256-bit value loaded by a 32-byte unaligned MLOAD window spanning five
  consecutive RV64 dwords. The single `start` byte offset applies to each
  8-byte EVM limb window; adjacent limbs share boundary dwords.
-/
def mloadLoadedWordFromFiveDwords
    (d0 d1 d2 d3 d4 : Word) (start : Nat) : EvmWord :=
  mloadLoadedWordFromDwordPairs
    d3 d4 start
    d2 d3 start
    d1 d2 start
    d0 d1 start

theorem mloadLoadedWordFromFiveDwords_eq_mloadLoadedWordFromDwordPairs
    (d0 d1 d2 d3 d4 : Word) (start : Nat) :
    mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start =
      mloadLoadedWordFromDwordPairs
        d3 d4 start
        d2 d3 start
        d1 d2 start
        d0 d1 start := by
  rfl

/--
  Fold the four output limbs from a five-dword unaligned MLOAD source window
  into one `evmWordIs` assertion.
-/
theorem mloadLoadedWordFromFiveDwords_evmWordIs_fold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair d3 d4 start) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair d2 d3 start) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair d1 d2 start) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair d0 d1 start)) =
    evmWordIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start) := by
  rw [mloadLoadedWordFromFiveDwords_eq_mloadLoadedWordFromDwordPairs]
  rw [mloadLoadedWordFromDwordPairs_evmWordIs_fold]

theorem mloadLoadedWordFromFiveDwords_evmStackIs_fold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) (rest : List EvmWord) :
    (((sp ↦ₘ mloadPackedLimbFromDwordPair d3 d4 start) **
      ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair d2 d3 start) **
      ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair d1 d2 start) **
      ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair d0 d1 start)) **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start :: rest) := by
  rw [mloadLoadedWordFromFiveDwords_evmWordIs_fold]
  rfl

/--
  Compact stack postcondition for the five-dword unaligned MLOAD source shape.
-/
@[irreducible]
def mloadStackOutputPostFiveDwords
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) : Assertion :=
  evmWordIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start)

theorem mloadStackOutputPostFiveDwords_unfold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) :
    mloadStackOutputPostFiveDwords sp d0 d1 d2 d3 d4 start =
      evmWordIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start) := by
  delta mloadStackOutputPostFiveDwords
  rfl

theorem mloadStackOutputPostFiveDwords_evmWordIs_fold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) :
    ((sp ↦ₘ mloadPackedLimbFromDwordPair d3 d4 start) **
     ((sp + 8) ↦ₘ mloadPackedLimbFromDwordPair d2 d3 start) **
     ((sp + 16) ↦ₘ mloadPackedLimbFromDwordPair d1 d2 start) **
     ((sp + 24) ↦ₘ mloadPackedLimbFromDwordPair d0 d1 start)) =
    mloadStackOutputPostFiveDwords sp d0 d1 d2 d3 d4 start := by
  rw [mloadStackOutputPostFiveDwords_unfold]
  rw [mloadLoadedWordFromFiveDwords_evmWordIs_fold]

theorem mloadStackOutputPostFiveDwords_evmStackIs_fold
    (sp d0 d1 d2 d3 d4 : Word) (start : Nat) (rest : List EvmWord) :
    (mloadStackOutputPostFiveDwords sp d0 d1 d2 d3 d4 start **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp (mloadLoadedWordFromFiveDwords d0 d1 d2 d3 d4 start :: rest) := by
  rw [mloadStackOutputPostFiveDwords_unfold]
  rfl

end EvmAsm.Evm64
