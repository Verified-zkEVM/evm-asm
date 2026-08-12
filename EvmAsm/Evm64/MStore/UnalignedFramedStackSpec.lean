/-
  EvmAsm.Evm64.MStore.UnalignedFramedStackSpec

  Sibling-frame variants of the per-quarter stack specs in
  `EvmAsm/Evm64/MStore/UnalignedStackSpec.lean`. Each wrapper takes an
  arbitrary `pcFree` assertion `F` and frames it on both pre and post.

  These are the prerequisite for the four-quarter compose slice toward the
  public region-backed top `evm_mstore_stack_spec_within_region`
  (`MemoryRegionStackSpec.lean`; GH #11983 closed the eight-cell public alias).
  The compose helper `evm_mstore_combined_one_limb_sequence_stack_spec_within`
  (`EvmAsm/Evm64/MStore/StackSpec.lean`) chains four quarter triples whose
  intermediate `Pi` are abstract. To plug the concrete q0..q3 specs from
  `UnalignedStackSpec.lean` into that helper, each quarter's pre/post must
  thread the *other three* quarters' byte-window cells (as future-frame for
  not-yet-stored quarters; as already-stored cells for past quarters). The
  generic `F` parameter lets the compose slice instantiate `F` with
  exactly the sibling-cell sep_conj it needs at each step.

  Distinctive token: evm_mstore_unaligned_one_limb_q*_stack_spec_within_framed
  sibling-quarter cells #53.
-/

import EvmAsm.Evm64.MStore.StackSpec
import EvmAsm.Evm64.MStore.UnalignedStackSpec
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
Sibling-framed MSTORE prologue stack spec: `mstore_prologue_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

This is the prologue counterpart to the q0..q3 sibling-framed lemmas below.
The full unaligned MSTORE compose slice uses it to preserve the byte-window and
source-limb frame while the initial stack offset is loaded and the absolute
memory address is computed.

Distinctive token: mstore_prologue_stack_spec_within_framed sibling-quarter
cells #53.
-/
theorem mstore_prologue_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  have core := mstore_prologue_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base
    h_off_ne_x0 h_addr_ne_x0
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
EVM-code transport of `mstore_prologue_stack_spec_within_framed`.

Later full-stack unaligned MSTORE composition can use this theorem directly at
the public `evm_mstore_code` boundary instead of carrying an extra stack-code
transport step.

Distinctive token: evm_mstore_prologue_stack_spec_within_framed #53.
-/
theorem evm_mstore_prologue_stack_spec_within_framed
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  exact cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 8)
    (mstore_prologue_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)

/--
Framed version of `evm_mstore_combined_one_limb_sequence_stack_spec_within`.

This wrapper preserves an arbitrary `pcFree` frame across the whole prologue
plus four-quarter byte-window write sequence, which is useful once the concrete
q0..q3 lemmas have been composed into a single MSTORE sequence triple.

Distinctive token:
evm_mstore_combined_one_limb_sequence_stack_spec_within_framed #53.
-/
theorem evm_mstore_combined_one_limb_sequence_stack_spec_within_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreOneLimbCode addrReg byteReg accReg
          32 24 25 26 27 28 29 30 31 (base + 8))
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreOneLimbCode addrReg byteReg accReg
          40 16 17 18 19 20 21 22 23 (base + 76)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreOneLimbCode addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15 (base + 144)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreOneLimbCode addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7 (base + 212)) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mstore_combined_one_limb_sequence_stack_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h0 h1 h2 h3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Framed version of `evm_mstore_combined_stack_spec_within`.

This is the coarse-body counterpart of
`evm_mstore_combined_one_limb_sequence_stack_spec_within_framed`: callers that
already produce one consolidated MSTORE body triple can preserve an arbitrary
`pcFree` frame across the public prologue/body composition.

Distinctive token: evm_mstore_combined_stack_spec_within_framed #53.
-/
theorem evm_mstore_combined_stack_spec_within_framed
    {n : Nat} {Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h4 :
      cpsTripleWithin n (base + 8) (base + 280)
        (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        Q) :
    cpsTripleWithin (2 + n) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mstore_combined_stack_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h4)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Framed version of `evm_mstore_combined_four_limb_sequence_stack_spec_within`.

This wrapper preserves an arbitrary `pcFree` frame around the public MSTORE
prologue plus four `mstoreFourLimbsCode` quarter triples.

Distinctive token:
evm_mstore_combined_four_limb_sequence_stack_spec_within_framed #53.
-/
theorem evm_mstore_combined_four_limb_sequence_stack_spec_within_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreFourLimbsCode addrReg byteReg accReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreFourLimbsCode addrReg byteReg accReg base) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mstore_combined_four_limb_sequence_stack_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h0 h1 h2 h3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Threaded-frame variant of `evm_mstore_combined_one_limb_sequence_stack_spec_within`.

Unlike the whole-sequence frame wrapper above, this theorem starts q0 from the
prologue postcondition already combined with `F`. That matches the concrete
q0..q3 sibling-framed MSTORE lemmas below, where the frame carries the other
window cells through each quarter.

Distinctive token:
evm_mstore_combined_one_limb_sequence_stack_spec_within_threaded_frame #53.
-/
theorem evm_mstore_combined_one_limb_sequence_stack_spec_within_threaded_frame
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (mstoreOneLimbCode addrReg byteReg accReg
          32 24 25 26 27 28 29 30 31 (base + 8))
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (mstoreOneLimbCode addrReg byteReg accReg
          40 16 17 18 19 20 21 22 23 (base + 76)) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (mstoreOneLimbCode addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15 (base + 144)) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (mstoreOneLimbCode addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7 (base + 212)) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 280)
    (cpsTripleWithin_seq_same_cr
      (mstore_prologue_stack_spec_within_framed
        offReg byteReg accReg addrReg memBaseReg
        sp offset offOld addrOld memBase base F hF
        h_off_ne_x0 h_addr_ne_x0)
      (cpsTripleWithin_extend_code
        (h := mstore_one_limb_sequence_spec_within
          addrReg byteReg accReg base h0 h1 h2 h3)
        (hmono := mstoreStackCode_four_limbs_sub
          offReg byteReg accReg addrReg memBaseReg base)))

/--
Public-code subsumption for the q0 MSTORE one-limb byte-window write block.

This bridges the concrete quarter block directly to `evm_mstore_code`, avoiding
repeat composition through `mstoreFourLimbsCode` and `mstoreStackCode` at call
sites that transport individual framed quarter specs.

Distinctive token: evm_mstore_code_one_limb_q0_sub #53.
-/
theorem evm_mstore_code_one_limb_q0_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        32 24 25 26 27 28 29 30 31 (base + 8)) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mstore_code_stack_sub offReg valReg byteReg accReg addrReg memBaseReg base a i
    (mstoreStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mstoreFourLimbsCode_limb0_sub addrReg byteReg accReg base a i h))

/-- Public-code subsumption for the q1 MSTORE one-limb byte-window write block. -/
theorem evm_mstore_code_one_limb_q1_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        40 16 17 18 19 20 21 22 23 (base + 76)) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mstore_code_stack_sub offReg valReg byteReg accReg addrReg memBaseReg base a i
    (mstoreStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mstoreFourLimbsCode_limb1_sub addrReg byteReg accReg base a i h))

/-- Public-code subsumption for the q2 MSTORE one-limb byte-window write block. -/
theorem evm_mstore_code_one_limb_q2_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        48 8 9 10 11 12 13 14 15 (base + 144)) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mstore_code_stack_sub offReg valReg byteReg accReg addrReg memBaseReg base a i
    (mstoreStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mstoreFourLimbsCode_limb2_sub addrReg byteReg accReg base a i h))

/-- Public-code subsumption for the q3 MSTORE one-limb byte-window write block. -/
theorem evm_mstore_code_one_limb_q3_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreOneLimbCode addrReg byteReg accReg
        56 0 1 2 3 4 5 6 7 (base + 212)) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mstore_code_stack_sub offReg valReg byteReg accReg addrReg memBaseReg base a i
    (mstoreStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mstoreFourLimbsCode_limb3_sub addrReg byteReg accReg base a i h))

/-- Transport a q0 MSTORE one-limb triple to the public `evm_mstore_code`. -/
theorem cpsTripleWithin_evm_mstore_of_one_limb_q0
    {n : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 76)
        (mstoreOneLimbCode addrReg byteReg accReg
          32 24 25 26 27 28 29 30 31 (base + 8)) P Q) :
    cpsTripleWithin n (base + 8) (base + 76)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_one_limb_q0_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/-- Transport a q1 MSTORE one-limb triple to the public `evm_mstore_code`. -/
theorem cpsTripleWithin_evm_mstore_of_one_limb_q1
    {n : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 76) (base + 144)
        (mstoreOneLimbCode addrReg byteReg accReg
          40 16 17 18 19 20 21 22 23 (base + 76)) P Q) :
    cpsTripleWithin n (base + 76) (base + 144)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_one_limb_q1_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/-- Transport a q2 MSTORE one-limb triple to the public `evm_mstore_code`. -/
theorem cpsTripleWithin_evm_mstore_of_one_limb_q2
    {n : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 144) (base + 212)
        (mstoreOneLimbCode addrReg byteReg accReg
          48 8 9 10 11 12 13 14 15 (base + 144)) P Q) :
    cpsTripleWithin n (base + 144) (base + 212)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_one_limb_q2_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/-- Transport a q3 MSTORE one-limb triple to the public `evm_mstore_code`. -/
theorem cpsTripleWithin_evm_mstore_of_one_limb_q3
    {n : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 212) (base + 280)
        (mstoreOneLimbCode addrReg byteReg accReg
          56 0 1 2 3 4 5 6 7 (base + 212)) P Q) :
    cpsTripleWithin n (base + 212) (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_one_limb_q3_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/--
Compose four public-code MSTORE one-limb triples into a single q0..q3 body
triple over `evm_mstore_code`.

This is the public-code counterpart of `mstore_one_limb_sequence_spec_within`:
callers that already transported each quarter to `evm_mstore_code` can sequence
them without returning to the smaller `mstoreFourLimbsCode` surface.

Distinctive token: evm_mstore_public_one_limb_sequence_spec_within #53.
-/
theorem evm_mstore_public_one_limb_sequence_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P0 P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P3 P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P0 P4 := by
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr h0 h1)
      h2)
    h3

/--
Permutation-aware public-code MSTORE q0..q3 composition.

This variant lets callers stitch concrete quarter specs whose postconditions
match the next precondition only after rearranging or weakening separation
conjunction atoms.

Distinctive token: evm_mstore_public_one_limb_sequence_spec_within_perm #53.
-/
theorem evm_mstore_public_one_limb_sequence_spec_within_perm
    {n0 n1 n2 n3 : Nat}
    {P0 P1 P1' P2 P2' P3 P3' P4 : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P0 P1)
    (h01 : ∀ s, P1 s → P1' s)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P1' P2)
    (h12 : ∀ s, P2 s → P2' s)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P2' P3)
    (h23 : ∀ s, P3 s → P3' s)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P3' P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P0 P4 := by
  exact cpsTripleWithin_seq_perm_same_cr
    h23
    (cpsTripleWithin_seq_perm_same_cr
      h12
      (cpsTripleWithin_seq_perm_same_cr h01 h0 h1)
      h2)
    h3

/--
Compose the framed MSTORE prologue with four public-code one-limb quarter
triples.

This is useful once q0..q3 have already been transported to `evm_mstore_code`;
the theorem supplies the prologue step and sequences the public body in one
call.

Distinctive token:
evm_mstore_public_one_limb_sequence_with_prologue_framed #53.
-/
theorem evm_mstore_public_one_limb_sequence_with_prologue_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_seq_same_cr
    (evm_mstore_prologue_stack_spec_within_framed
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)
    (evm_mstore_public_one_limb_sequence_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg base h0 h1 h2 h3)

/--
Compose the framed MSTORE prologue with a permutation-aware public-code q0..q3
one-limb sequence.

This is the concrete-compose entry point for quarter specs whose intermediate
postconditions need `sep_perm`/weakening callbacks before the next quarter.

Distinctive token:
evm_mstore_public_one_limb_sequence_with_prologue_framed_perm #53.
-/
theorem evm_mstore_public_one_limb_sequence_with_prologue_framed_perm
    {n0 n1 n2 n3 : Nat}
    {P1 P1' P2 P2' P3 P3' Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 76)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        P1)
    (h01 : ∀ s, P1 s → P1' s)
    (h1 :
      cpsTripleWithin n1 (base + 76) (base + 144)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P1' P2)
    (h12 : ∀ s, P2 s → P2' s)
    (h2 :
      cpsTripleWithin n2 (base + 144) (base + 212)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P2' P3)
    (h23 : ∀ s, P3 s → P3' s)
    (h3 :
      cpsTripleWithin n3 (base + 212) (base + 280)
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P3' Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_seq_same_cr
    (evm_mstore_prologue_stack_spec_within_framed
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)
    (evm_mstore_public_one_limb_sequence_spec_within_perm
      offReg valReg byteReg accReg addrReg memBaseReg base
      h0 h01 h1 h12 h2 h23 h3)

/--
Generic public-code MSTORE prologue/body composition with a framed prologue.

This lets callers plug in any body triple over `evm_mstore_code` that starts
from the framed prologue postcondition, not just the q0..q3 one-limb sequence.

Distinctive token: evm_mstore_public_body_with_prologue_framed #53.
-/
theorem evm_mstore_public_body_with_prologue_framed
    {n : Nat} {Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base pcEnd : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (hbody :
      cpsTripleWithin n (base + 8) pcEnd
        (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        Q) :
    cpsTripleWithin (2 + n) base pcEnd
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_seq_same_cr
    (evm_mstore_prologue_stack_spec_within_framed
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)
    hbody

/--
Sibling-framed q0 stack spec: `evm_mstore_unaligned_one_limb_q0_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Used by the compose slice `evm_mstore_unaligned_full_stack_spec_within`
(evm-asm-f159q) to thread the not-yet-stored q1/q2/q3 byte-window cells
through q0's triple.

Distinctive token: evm_mstore_unaligned_one_limb_q0_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q0_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 17 (base + 8) (base + 76)
      (mstoreOneLimbCode addrReg byteReg accReg
        32 24 25 26 27 28 29 30 31 (base + 8))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q0_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q0 framed MSTORE spec: transports
`evm_mstore_unaligned_one_limb_q0_stack_spec_within_framed` from the q0
one-limb block to the full `evm_mstore_code` code requirement.

Distinctive token:
evm_mstore_unaligned_one_limb_q0_spec_within_framed_public_code #53.
-/
theorem evm_mstore_unaligned_one_limb_q0_spec_within_framed_public_code
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 17 (base + 8) (base + 76)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  exact cpsTripleWithin_evm_mstore_of_one_limb_q0
    offReg valReg byteReg accReg addrReg memBaseReg base
    (evm_mstore_unaligned_one_limb_q0_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld limbVal
      loAddr hiAddr loVal hiVal start base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Sibling-framed q1 stack spec: `evm_mstore_unaligned_one_limb_q1_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mstore_unaligned_one_limb_q1_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q1_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 17 (base + 76) (base + 144)
      (mstoreOneLimbCode addrReg byteReg accReg
        40 16 17 18 19 20 21 22 23 (base + 76))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q1_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q1 framed MSTORE spec: transports
`evm_mstore_unaligned_one_limb_q1_stack_spec_within_framed` from the q1
one-limb block to the full `evm_mstore_code` code requirement.

Distinctive token:
evm_mstore_unaligned_one_limb_q1_spec_within_framed_public_code #53.
-/
theorem evm_mstore_unaligned_one_limb_q1_spec_within_framed_public_code
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 17 (base + 76) (base + 144)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  exact cpsTripleWithin_evm_mstore_of_one_limb_q1
    offReg valReg byteReg accReg addrReg memBaseReg base
    (evm_mstore_unaligned_one_limb_q1_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld limbVal
      loAddr hiAddr loVal hiVal start base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Sibling-framed q2 stack spec: `evm_mstore_unaligned_one_limb_q2_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mstore_unaligned_one_limb_q2_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q2_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 17 (base + 144) (base + 212)
      (mstoreOneLimbCode addrReg byteReg accReg
        48 8 9 10 11 12 13 14 15 (base + 144))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q2_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q2 framed MSTORE spec: transports
`evm_mstore_unaligned_one_limb_q2_stack_spec_within_framed` from the q2
one-limb block to the full `evm_mstore_code` code requirement.

Distinctive token:
evm_mstore_unaligned_one_limb_q2_spec_within_framed_public_code #53.
-/
theorem evm_mstore_unaligned_one_limb_q2_spec_within_framed_public_code
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 17 (base + 144) (base + 212)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  exact cpsTripleWithin_evm_mstore_of_one_limb_q2
    offReg valReg byteReg accReg addrReg memBaseReg base
    (evm_mstore_unaligned_one_limb_q2_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld limbVal
      loAddr hiAddr loVal hiVal start base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Sibling-framed q3 stack spec: `evm_mstore_unaligned_one_limb_q3_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mstore_unaligned_one_limb_q3_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mstore_unaligned_one_limb_q3_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 17 (base + 212) (base + 280)
      (mstoreOneLimbCode addrReg byteReg accReg
        56 0 1 2 3 4 5 6 7 (base + 212))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  have core := evm_mstore_unaligned_one_limb_q3_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld limbVal
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q3 framed MSTORE spec: transports
`evm_mstore_unaligned_one_limb_q3_stack_spec_within_framed` from the q3
one-limb block to the full `evm_mstore_code` code requirement.

Distinctive token:
evm_mstore_unaligned_one_limb_q3_spec_within_framed_public_code #53.
-/
theorem evm_mstore_unaligned_one_limb_q3_spec_within_framed_public_code
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld limbVal : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mstoreLimbWindowOk (memBase + offset) loAddr hiAddr start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 17 (base + 212) (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        (let stored :=
          MStore.mstoreDwordPairStoreLimb loVal hiVal limbVal start
         (byteReg ↦ᵣ limbVal) ** (accReg ↦ᵣ limbVal) **
         (loAddr ↦ₘ stored.1) ** (hiAddr ↦ₘ stored.2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbVal))) ** F) := by
  exact cpsTripleWithin_evm_mstore_of_one_limb_q3
    offReg valReg byteReg accReg addrReg memBaseReg base
    (evm_mstore_unaligned_one_limb_q3_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld limbVal
      loAddr hiAddr loVal hiVal start base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Concrete public-code composition of the four unaligned MSTORE quarter specs.

The theorem instantiates q0..q3 with sibling frames that thread the remaining
source limbs and memory windows, then uses `sep_perm` at each midpoint.

Distinctive token: evm_mstore_unaligned_full_stack_spec_within_public #53.
-/
theorem evm_mstore_unaligned_full_stack_spec_within_public
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (loAddr0 hiAddr0 loVal0 hiVal0 : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word)
    (start : Nat) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window0 : mstoreLimbWindowOk (memBase + offset) loAddr0 hiAddr0 start
                  24 25 26 27 28 29 30 31)
    (h_window1 : mstoreLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23)
    (h_window2 : mstoreLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15)
    (h_window3 : mstoreLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
    let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
    let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
    let stored3 := MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
    cpsTripleWithin (2 + (17 + 17 + 17 + 17)) base (base + 280)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
         (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
         ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3))) **
       ((loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
        (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
        (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2))) := by
  let Fpre : Assertion :=
    (byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
    (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
    (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)
  let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
  let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
  let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
  let F0 : Assertion :=
    (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
    (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)
  let F1 : Assertion :=
    (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
    (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)
  let F2 : Assertion :=
    (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)
  let F3 : Assertion :=
    (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2)
  dsimp only
  exact cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      dsimp only [Fpre, F0] at hp ⊢
      sep_perm hp)
    (evm_mstore_prologue_stack_spec_within_framed
      offReg valReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base Fpre (by pcFree)
      h_off_ne_x0 h_addr_ne_x0)
    (evm_mstore_public_one_limb_sequence_spec_within_perm
      offReg valReg byteReg accReg addrReg memBaseReg base
      (evm_mstore_unaligned_one_limb_q0_spec_within_framed_public_code
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset memBase byteOld accOld limb0
        loAddr0 hiAddr0 loVal0 hiVal0 start base F0 (by pcFree)
        h_byte_ne_x0 h_acc_ne_x0 h_window0)
      (fun _ hp => by
        dsimp only [F0, F1, stored0] at hp ⊢
        sep_perm hp)
      (evm_mstore_unaligned_one_limb_q1_spec_within_framed_public_code
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset memBase limb0 limb0 limb1
        loAddr1 hiAddr1 loVal1 hiVal1 start base F1 (by pcFree)
        h_byte_ne_x0 h_acc_ne_x0 h_window1)
      (fun _ hp => by
        dsimp only [F1, F2, stored1] at hp ⊢
        sep_perm hp)
      (evm_mstore_unaligned_one_limb_q2_spec_within_framed_public_code
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset memBase limb1 limb1 limb2
        loAddr2 hiAddr2 loVal2 hiVal2 start base F2 (by pcFree)
        h_byte_ne_x0 h_acc_ne_x0 h_window2)
      (fun _ hp => by
        dsimp only [F2, F3, stored2] at hp ⊢
        sep_perm hp)
      (evm_mstore_unaligned_one_limb_q3_spec_within_framed_public_code
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset memBase limb2 limb2 limb3
        loAddr3 hiAddr3 loVal3 hiVal3 start base F3 (by pcFree)
        h_byte_ne_x0 h_acc_ne_x0 h_window3))

/--
Concrete public-code composition of unaligned MSTORE through the epilogue.

This wraps `evm_mstore_unaligned_full_stack_spec_within_public` with the
public-code epilogue so the final stack pointer is advanced to `sp + 64`.

Distinctive token:
evm_mstore_unaligned_full_stack_spec_within_public_epilogue #53.
-/
theorem evm_mstore_unaligned_full_stack_spec_within_public_epilogue
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (loAddr0 hiAddr0 loVal0 hiVal0 : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word)
    (start : Nat) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window0 : mstoreLimbWindowOk (memBase + offset) loAddr0 hiAddr0 start
                  24 25 26 27 28 29 30 31)
    (h_window1 : mstoreLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23)
    (h_window2 : mstoreLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15)
    (h_window3 : mstoreLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
    let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
    let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
    let stored3 := MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
    cpsTripleWithin (2 + (17 + 17 + 17 + 17) + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)))
      (((.x12 : Reg) ↦ᵣ (sp + 64)) **
       ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
        (addrReg ↦ᵣ (memBase + offset)) ** (sp ↦ₘ offset) **
        (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
        (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3) **
        (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
        (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
        (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2))) := by
  let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
  let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
  let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
  let stored3 := MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
  let FPost : Assertion :=
    (offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
    (addrReg ↦ᵣ (memBase + offset)) ** (sp ↦ₘ offset) **
    (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
    (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
    ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3) **
    (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
    ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
    (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
    ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
    (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2) **
    ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2)
  dsimp only
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_weaken
      (fun _ hp => by sep_perm hp)
      (fun _ hp => by
        dsimp only [FPost, stored0, stored1, stored2, stored3] at hp ⊢
        sep_perm hp)
      (evm_mstore_unaligned_full_stack_spec_within_public
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset offOld addrOld memBase byteOld accOld
        limb0 limb1 limb2 limb3
        loAddr0 hiAddr0 loVal0 hiVal0
        loAddr1 hiAddr1 loVal1 hiVal1
        loAddr2 hiAddr2 loVal2 hiVal2
        loAddr3 hiAddr3 loVal3 hiVal3
        start base
        h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
        h_window0 h_window1 h_window2 h_window3))
    (mstore_epilogue_evm_mstore_frame_spec_within
      offReg valReg byteReg accReg addrReg memBaseReg sp base
      FPost (by pcFree))

/--
Stack-tail variant of the public unaligned MSTORE epilogue composition.

This frames the remaining EVM stack tail at `sp + 64`, matching MSTORE's
two-word stack pop after the epilogue advances `.x12`.

Distinctive token:
evm_mstore_unaligned_full_stack_spec_within_public_stack_tail #53.
-/
theorem evm_mstore_unaligned_full_stack_spec_within_public_stack_tail
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (loAddr0 hiAddr0 loVal0 hiVal0 : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word)
    (start : Nat) (base : Word) (rest : List EvmWord)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window0 : mstoreLimbWindowOk (memBase + offset) loAddr0 hiAddr0 start
                  24 25 26 27 28 29 30 31)
    (h_window1 : mstoreLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23)
    (h_window2 : mstoreLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15)
    (h_window3 : mstoreLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
    let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
    let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
    let stored3 := MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
    cpsTripleWithin (2 + (17 + 17 + 17 + 17) + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3))) **
       evmStackIs (sp + 64) rest)
      (((.x12 : Reg) ↦ᵣ (sp + 64)) **
       evmStackIs (sp + 64) rest **
       ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
        (addrReg ↦ᵣ (memBase + offset)) ** (sp ↦ₘ offset) **
        (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
        (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
        ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3) **
        (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
        ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
        (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
        ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
        (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2) **
        ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2))) := by
  dsimp only
  have hCore :=
    cpsTripleWithin_frameR (evmStackIs (sp + 64) rest) (by pcFree)
      (evm_mstore_unaligned_full_stack_spec_within_public_epilogue
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset offOld addrOld memBase byteOld accOld
        limb0 limb1 limb2 limb3
        loAddr0 hiAddr0 loVal0 hiVal0
        loAddr1 hiAddr1 loVal1 hiVal1
        loAddr2 hiAddr2 loVal2 hiVal2
        loAddr3 hiAddr3 loVal3 hiVal3
        start base
        h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
        h_window0 h_window1 h_window2 h_window3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    hCore

/--
Stack-pre variant of the public unaligned MSTORE stack-tail composition.

This exposes the consumed offset and value words as an `evmStackIs`
precondition. The postcondition keeps those below-stack memory cells folded,
while `.x12` advances to `sp + 64`.

Distinctive token:
evm_mstore_unaligned_full_stack_spec_within_public_stack_pre #53.
-/
theorem evm_mstore_unaligned_full_stack_spec_within_public_stack_pre
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase byteOld accOld : Word)
    (offsetWord valueWord : EvmWord) (rest : List EvmWord)
    (offsetHigh1 offsetHigh2 offsetHigh3 : Word)
    (limb0 limb1 limb2 limb3 : Word)
    (loAddr0 hiAddr0 loVal0 hiVal0 : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word)
    (start : Nat) (base : Word)
    (h_offset0 : offsetWord.getLimbN 0 = offset)
    (h_offset1 : offsetWord.getLimbN 1 = offsetHigh1)
    (h_offset2 : offsetWord.getLimbN 2 = offsetHigh2)
    (h_offset3 : offsetWord.getLimbN 3 = offsetHigh3)
    (h_value0 : valueWord.getLimbN 0 = limb0)
    (h_value1 : valueWord.getLimbN 1 = limb1)
    (h_value2 : valueWord.getLimbN 2 = limb2)
    (h_value3 : valueWord.getLimbN 3 = limb3)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h_byte_ne_x0 : byteReg ≠ .x0)
    (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window0 : mstoreLimbWindowOk (memBase + offset) loAddr0 hiAddr0 start
                  24 25 26 27 28 29 30 31)
    (h_window1 : mstoreLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23)
    (h_window2 : mstoreLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15)
    (h_window3 : mstoreLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    let stored0 := MStore.mstoreDwordPairStoreLimb loVal0 hiVal0 limb0 start
    let stored1 := MStore.mstoreDwordPairStoreLimb loVal1 hiVal1 limb1 start
    let stored2 := MStore.mstoreDwordPairStoreLimb loVal2 hiVal2 limb2 start
    let stored3 := MStore.mstoreDwordPairStoreLimb loVal3 hiVal3 limb3 start
    cpsTripleWithin (2 + (17 + 17 + 17 + 17) + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        evmStackIs sp (offsetWord :: valueWord :: rest)) **
       ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
        (loAddr0 ↦ₘ loVal0) ** (hiAddr0 ↦ₘ hiVal0) **
        (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1) **
        (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2) **
        (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))))
      (((.x12 : Reg) ↦ᵣ (sp + 64)) **
       evmStackIs sp (offsetWord :: valueWord :: rest) **
       ((offReg ↦ᵣ offset) ** (memBaseReg ↦ᵣ memBase) **
        (addrReg ↦ᵣ (memBase + offset)) **
        (byteReg ↦ᵣ limb3) ** (accReg ↦ᵣ limb3) **
        (loAddr3 ↦ₘ stored3.1) ** (hiAddr3 ↦ₘ stored3.2) **
        (loAddr0 ↦ₘ stored0.1) ** (hiAddr0 ↦ₘ stored0.2) **
        (loAddr1 ↦ₘ stored1.1) ** (hiAddr1 ↦ₘ stored1.2) **
        (loAddr2 ↦ₘ stored2.1) ** (hiAddr2 ↦ₘ stored2.2))) := by
  dsimp only
  let offsetHighFrame : Assertion :=
    ((sp + 8) ↦ₘ offsetHigh1) **
    ((sp + 16) ↦ₘ offsetHigh2) **
    ((sp + 24) ↦ₘ offsetHigh3)
  have hCore :=
    cpsTripleWithin_frameR offsetHighFrame (by pcFree)
      (evm_mstore_unaligned_full_stack_spec_within_public_stack_tail
        offReg valReg byteReg accReg addrReg memBaseReg
        sp offset offOld addrOld memBase byteOld accOld
        limb0 limb1 limb2 limb3
        loAddr0 hiAddr0 loVal0 hiVal0
        loAddr1 hiAddr1 loVal1 hiVal1
        loAddr2 hiAddr2 loVal2 hiVal2
        loAddr3 hiAddr3 loVal3 hiVal3
        start base rest
        h_off_ne_x0 h_addr_ne_x0 h_byte_ne_x0 h_acc_ne_x0
        h_window0 h_window1 h_window2 h_window3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [evmStackIs_cons] at hp
      rw [evmWordIs_sp_limbs_eq sp offsetWord
        offset offsetHigh1 offsetHigh2 offsetHigh3
        h_offset0 h_offset1 h_offset2 h_offset3] at hp
      rw [evmStackIs_cons] at hp
      rw [evmWordIs_sp32_limbs_eq sp valueWord
        limb0 limb1 limb2 limb3
        h_value0 h_value1 h_value2 h_value3] at hp
      rw [show (sp + 32 + 32 : Word) = sp + 64 from by bv_addr] at hp
      simp only [signExtend12_32, signExtend12_40, signExtend12_48,
        signExtend12_56] at hp ⊢
      dsimp only [offsetHighFrame] at hp ⊢
      sep_perm hp)
    (fun _ hp => by
      rw [evmStackIs_cons]
      rw [evmWordIs_sp_limbs_eq sp offsetWord
        offset offsetHigh1 offsetHigh2 offsetHigh3
        h_offset0 h_offset1 h_offset2 h_offset3]
      rw [evmStackIs_cons]
      rw [evmWordIs_sp32_limbs_eq sp valueWord
        limb0 limb1 limb2 limb3
        h_value0 h_value1 h_value2 h_value3]
      rw [show (sp + 32 + 32 : Word) = sp + 64 from by bv_addr]
      simp only [signExtend12_32, signExtend12_40, signExtend12_48,
        signExtend12_56] at hp ⊢
      dsimp only [offsetHighFrame] at hp ⊢
      sep_perm hp)
    hCore

end EvmAsm.Evm64
