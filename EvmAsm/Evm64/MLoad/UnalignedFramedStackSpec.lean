/-
  EvmAsm.Evm64.MLoad.UnalignedFramedStackSpec

  Sibling-frame variants of the per-quarter stack specs in
  `EvmAsm/Evm64/MLoad/UnalignedStackSpec.lean`. Each wrapper takes an
  arbitrary `pcFree` assertion `F` and frames it on both pre and post.

  These are the prerequisite for the four-quarter compose slice toward
  the topmost `evm_mload_stack_spec_within` (evm-asm-75z1x / evm-asm-lrhou /
  GH #53 follow-up): the compose helper
  `evm_mload_combined_one_limb_sequence_stack_spec_within`
  (`EvmAsm/Evm64/MLoad/StackSpec.lean`) chains four quarter triples whose
  intermediate `Pi` are abstract. To plug the concrete q0..q3 specs from
  `UnalignedStackSpec.lean` into that helper, each quarter's pre/post must
  thread the *other three* quarters' byte-window cells (as future-frame
  for not-yet-loaded quarters; as already-loaded cells for past quarters).
  The generic `F` parameter lets the compose slice instantiate `F` with
  exactly the sibling-cell sep_conj it needs at each step.

  Direct MLOAD analog of `EvmAsm/Evm64/MStore/UnalignedFramedStackSpec.lean`
  (evm-asm-81sv2 / PR #3139).

  Distinctive token: evm_mload_unaligned_one_limb_q*_stack_spec_within_framed
  sibling-quarter cells #53.
-/

import EvmAsm.Evm64.MLoad.StackSpec
import EvmAsm.Evm64.MLoad.UnalignedStackSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
Sibling-framed MLOAD prologue stack spec: `mload_prologue_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

This is the prologue counterpart to the q0..q3 sibling-framed lemmas below.
The full unaligned MLOAD compose slice uses it to preserve the byte-window and
destination-cell frame while the initial stack offset is loaded and the
absolute memory address is computed.

Distinctive token: mload_prologue_stack_spec_within_framed sibling-quarter
cells #53.
-/
theorem mload_prologue_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (mloadStackCode offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  have core := mload_prologue_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base
    h_off_ne_x0 h_addr_ne_x0
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
EVM-code transport of `mload_prologue_stack_spec_within_framed`.

Later full-stack unaligned MLOAD composition can use this theorem directly at
the public `evm_mload_code` boundary instead of carrying an extra stack-code
transport step.

Distinctive token: evm_mload_prologue_stack_spec_within_framed #53.
-/
theorem evm_mload_prologue_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset)) ** F) := by
  exact cpsTripleWithin_evm_mload_of_stack
    offReg byteReg accReg addrReg memBaseReg base (base + 8)
    (mload_prologue_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)

/--
Framed version of `evm_mload_combined_one_limb_sequence_stack_spec_within`.

This wrapper preserves an arbitrary `pcFree` frame across the whole prologue
plus four-quarter byte-pack sequence, which is useful once the concrete q0..q3
lemmas have been composed into a single MLOAD sequence triple.

Distinctive token:
evm_mload_combined_one_limb_sequence_stack_spec_within_framed #53.
-/
theorem evm_mload_combined_one_limb_sequence_stack_spec_within_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
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
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mload_combined_one_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h0 h1 h2 h3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Framed version of `evm_mload_combined_stack_spec_within`.

This is the coarse-body counterpart of
`evm_mload_combined_one_limb_sequence_stack_spec_within_framed`: callers that
already produce one consolidated MLOAD body triple can preserve an arbitrary
`pcFree` frame across the public prologue/body composition.

Distinctive token: evm_mload_combined_stack_spec_within_framed #53.
-/
theorem evm_mload_combined_stack_spec_within_framed
    {n : Nat} {Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
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
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mload_combined_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h4)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Framed version of `evm_mload_combined_four_limb_sequence_stack_spec_within`.

This wrapper preserves an arbitrary `pcFree` frame around the public MLOAD
prologue plus four `mloadFourLimbsCode` quarter triples.

Distinctive token:
evm_mload_combined_four_limb_sequence_stack_spec_within_framed #53.
-/
theorem evm_mload_combined_four_limb_sequence_stack_spec_within_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
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
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      (Q ** F) := by
  have framed := cpsTripleWithin_frameL (F := F) hF
    (evm_mload_combined_four_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base
      h_off_ne_x0 h_addr_ne_x0 h0 h1 h2 h3)
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Threaded-frame variant of `evm_mload_combined_one_limb_sequence_stack_spec_within`.

Unlike the whole-sequence frame wrapper above, this theorem starts q0 from the
prologue postcondition already combined with `F`. That matches the concrete
q0..q3 sibling-framed MLOAD lemmas below, where the frame carries the other
window cells through each quarter.

Distinctive token:
evm_mload_combined_one_limb_sequence_stack_spec_within_threaded_frame #53.
-/
theorem evm_mload_combined_one_limb_sequence_stack_spec_within_threaded_frame
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8))
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
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
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_evm_mload_of_stack
    offReg byteReg accReg addrReg memBaseReg base (base + 376)
    (cpsTripleWithin_seq_same_cr
      (mload_prologue_stack_spec_within_framed
        offReg byteReg accReg addrReg memBaseReg
        sp offset offOld addrOld memBase base F hF
        h_off_ne_x0 h_addr_ne_x0)
      (mload_four_limbs_stack_spec_within
        offReg byteReg accReg addrReg memBaseReg base
        (mload_one_limb_sequence_spec_within
          addrReg byteReg accReg base h0 h1 h2 h3)))

/--
Public-code subsumption for the q0 MLOAD one-limb byte-pack block.

This bridges the concrete quarter block directly to `evm_mload_code`, avoiding
repeat composition through `mloadFourLimbsCode` and `mloadStackCode` at call
sites that transport individual framed quarter specs.

Distinctive token: evm_mload_code_one_limb_q0_sub #53.
-/
theorem evm_mload_code_one_limb_q0_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8)) a = some i →
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mload_code_stack_sub offReg byteReg accReg addrReg memBaseReg base a i
    (mloadStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mloadFourLimbsCode_one_limb_q0_sub addrReg byteReg accReg base a i h))

/-- Public-code subsumption for the q1 MLOAD one-limb byte-pack block. -/
theorem evm_mload_code_one_limb_q1_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100)) a = some i →
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mload_code_stack_sub offReg byteReg accReg addrReg memBaseReg base a i
    (mloadStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mloadFourLimbsCode_one_limb_q1_sub addrReg byteReg accReg base a i h))

/-- Public-code subsumption for the q2 MLOAD one-limb byte-pack block. -/
theorem evm_mload_code_one_limb_q2_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192)) a = some i →
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mload_code_stack_sub offReg byteReg accReg addrReg memBaseReg base a i
    (mloadStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mloadFourLimbsCode_one_limb_q2_sub addrReg byteReg accReg base a i h))

/-- Public-code subsumption for the q3 MLOAD one-limb byte-pack block. -/
theorem evm_mload_code_one_limb_q3_sub
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284)) a = some i →
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) a = some i := by
  intro a i h
  exact evm_mload_code_stack_sub offReg byteReg accReg addrReg memBaseReg base a i
    (mloadStackCode_four_limbs_sub offReg byteReg accReg addrReg memBaseReg base a i
      (mloadFourLimbsCode_one_limb_q3_sub addrReg byteReg accReg base a i h))

/-- Transport a q0 MLOAD one-limb triple to the public `evm_mload_code`. -/
theorem cpsTripleWithin_evm_mload_of_one_limb_q0
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8)) P Q) :
    cpsTripleWithin n (base + 8) (base + 100)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mload_code_one_limb_q0_sub
      offReg byteReg accReg addrReg memBaseReg base)

/-- Transport a q1 MLOAD one-limb triple to the public `evm_mload_code`. -/
theorem cpsTripleWithin_evm_mload_of_one_limb_q1
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 100) (base + 192)
        (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) P Q) :
    cpsTripleWithin n (base + 100) (base + 192)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mload_code_one_limb_q1_sub
      offReg byteReg accReg addrReg memBaseReg base)

/-- Transport a q2 MLOAD one-limb triple to the public `evm_mload_code`. -/
theorem cpsTripleWithin_evm_mload_of_one_limb_q2
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 192) (base + 284)
        (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) P Q) :
    cpsTripleWithin n (base + 192) (base + 284)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mload_code_one_limb_q2_sub
      offReg byteReg accReg addrReg memBaseReg base)

/-- Transport a q3 MLOAD one-limb triple to the public `evm_mload_code`. -/
theorem cpsTripleWithin_evm_mload_of_one_limb_q3
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 284) (base + 376)
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) P Q) :
    cpsTripleWithin n (base + 284) (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mload_code_one_limb_q3_sub
      offReg byteReg accReg addrReg memBaseReg base)

/--
Compose four public-code MLOAD one-limb triples into a single q0..q3 body
triple over `evm_mload_code`.

This is the public-code counterpart of `mload_one_limb_sequence_spec_within`:
callers that already transported each quarter to `evm_mload_code` can sequence
them without returning to the smaller `mloadFourLimbsCode` surface.

Distinctive token: evm_mload_public_one_limb_sequence_spec_within #53.
-/
theorem evm_mload_public_one_limb_sequence_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P0 P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P3 P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P0 P4 := by
  exact cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr h0 h1)
      h2)
    h3

/--
Permutation-aware public-code MLOAD q0..q3 composition.

This variant lets callers stitch concrete quarter specs whose postconditions
match the next precondition only after rearranging or weakening separation
conjunction atoms.

Distinctive token: evm_mload_public_one_limb_sequence_spec_within_perm #53.
-/
theorem evm_mload_public_one_limb_sequence_spec_within_perm
    {n0 n1 n2 n3 : Nat}
    {P0 P1 P1' P2 P2' P3 P3' P4 : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg) (base : Word)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P0 P1)
    (h01 : ∀ s, P1 s → P1' s)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P1' P2)
    (h12 : ∀ s, P2 s → P2' s)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P2' P3)
    (h23 : ∀ s, P3 s → P3' s)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P3' P4) :
    cpsTripleWithin (n0 + n1 + n2 + n3) (base + 8) (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P0 P4 := by
  exact cpsTripleWithin_seq_perm_same_cr
    h23
    (cpsTripleWithin_seq_perm_same_cr
      h12
      (cpsTripleWithin_seq_perm_same_cr h01 h0 h1)
      h2)
    h3

/--
Compose the framed MLOAD prologue with four public-code one-limb quarter
triples.

This is useful once q0..q3 have already been transported to `evm_mload_code`;
the theorem supplies the prologue step and sequences the public body in one
call.

Distinctive token: evm_mload_public_one_limb_sequence_with_prologue_framed #53.
-/
theorem evm_mload_public_one_limb_sequence_with_prologue_framed
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        P1)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P1 P2)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P2 P3)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P3 Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_seq_same_cr
    (evm_mload_prologue_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)
    (evm_mload_public_one_limb_sequence_spec_within
      offReg byteReg accReg addrReg memBaseReg base h0 h1 h2 h3)

/--
Compose the framed MLOAD prologue with a permutation-aware public-code q0..q3
one-limb sequence.

This is the concrete-compose entry point for quarter specs whose intermediate
postconditions need `sep_perm`/weakening callbacks before the next quarter.

Distinctive token:
evm_mload_public_one_limb_sequence_with_prologue_framed_perm #53.
-/
theorem evm_mload_public_one_limb_sequence_with_prologue_framed_perm
    {n0 n1 n2 n3 : Nat}
    {P1 P1' P2 P2' P3 P3' Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        P1)
    (h01 : ∀ s, P1 s → P1' s)
    (h1 :
      cpsTripleWithin n1 (base + 100) (base + 192)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P1' P2)
    (h12 : ∀ s, P2 s → P2' s)
    (h2 :
      cpsTripleWithin n2 (base + 192) (base + 284)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P2' P3)
    (h23 : ∀ s, P3 s → P3' s)
    (h3 :
      cpsTripleWithin n3 (base + 284) (base + 376)
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base) P3' Q) :
    cpsTripleWithin (2 + (n0 + n1 + n2 + n3)) base (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_seq_same_cr
    (evm_mload_prologue_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)
    (evm_mload_public_one_limb_sequence_spec_within_perm
      offReg byteReg accReg addrReg memBaseReg base
      h0 h01 h1 h12 h2 h23 h3)

/--
Generic public-code MLOAD prologue/body composition with a framed prologue.

This lets callers plug in any body triple over `evm_mload_code` that starts
from the framed prologue postcondition, not just the q0..q3 one-limb sequence.

Distinctive token: evm_mload_public_body_with_prologue_framed #53.
-/
theorem evm_mload_public_body_with_prologue_framed
    {n : Nat} {Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base pcEnd : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (hbody :
      cpsTripleWithin n (base + 8) pcEnd
        (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
        ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
          (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
          (sp ↦ₘ offset)) ** F)
        Q) :
    cpsTripleWithin (2 + n) base pcEnd
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
        (sp ↦ₘ offset)) ** F)
      Q := by
  exact cpsTripleWithin_seq_same_cr
    (evm_mload_prologue_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base F hF
      h_off_ne_x0 h_addr_ne_x0)
    hbody

/--
Sibling-framed q0 stack spec: `evm_mload_unaligned_one_limb_q0_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Used by the compose slice `evm_mload_unaligned_full_stack_spec_within`
(evm-asm-75z1x) to thread the not-yet-loaded q1/q2/q3 byte-window cells
through q0's triple.

Distinctive token: evm_mload_unaligned_one_limb_q0_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q0_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 23 (base + 8) (base + 100)
      (mloadOneLimbCode addrReg byteReg accReg
        24 25 26 27 28 29 30 31 0 (base + 8))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ mloadPackedLimbFromDwordPair loVal hiVal start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q0_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld
    loAddr hiAddr loVal hiVal start base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q0 framed MLOAD spec: transports
`evm_mload_unaligned_one_limb_q0_stack_spec_within_framed` from the q0
one-limb block to the full `evm_mload_code` code requirement.

Distinctive token:
evm_mload_unaligned_one_limb_q0_spec_within_framed_public_code #53.
-/
theorem evm_mload_unaligned_one_limb_q0_spec_within_framed_public_code
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (loAddr hiAddr loVal hiVal : Word) (start : Nat)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr hiAddr start
                  24 25 26 27 28 29 30 31) :
    cpsTripleWithin 23 (base + 8) (base + 100)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ offset) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ mloadPackedLimbFromDwordPair loVal hiVal start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal hiVal start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal hiVal start) **
         (loAddr ↦ₘ loVal) ** (hiAddr ↦ₘ hiVal))) ** F) := by
  exact cpsTripleWithin_evm_mload_of_one_limb_q0
    offReg byteReg accReg addrReg memBaseReg base
    (evm_mload_unaligned_one_limb_q0_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld
      loAddr hiAddr loVal hiVal start base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Sibling-framed q1 stack spec: `evm_mload_unaligned_one_limb_q1_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mload_unaligned_one_limb_q1_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q1_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 23 (base + 100) (base + 192)
      (mloadOneLimbCode addrReg byteReg accReg
        16 17 18 19 20 21 22 23 8 (base + 100))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal1 hiVal1 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
         (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q1_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld q0Old
    loAddr1 hiAddr1 loVal1 hiVal1 start dstOld base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q1 framed MLOAD spec: transports
`evm_mload_unaligned_one_limb_q1_stack_spec_within_framed` from the q1
one-limb block to the full `evm_mload_code` code requirement.

Distinctive token:
evm_mload_unaligned_one_limb_q1_spec_within_framed_public_code #53.
-/
theorem evm_mload_unaligned_one_limb_q1_spec_within_framed_public_code
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old : Word)
    (loAddr1 hiAddr1 loVal1 hiVal1 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr1 hiAddr1 start
                  16 17 18 19 20 21 22 23) :
    cpsTripleWithin 23 (base + 100) (base + 192)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal1 hiVal1 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal1 hiVal1 start) **
         (loAddr1 ↦ₘ loVal1) ** (hiAddr1 ↦ₘ hiVal1))) ** F) := by
  exact cpsTripleWithin_evm_mload_of_one_limb_q1
    offReg byteReg accReg addrReg memBaseReg base
    (evm_mload_unaligned_one_limb_q1_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld q0Old
      loAddr1 hiAddr1 loVal1 hiVal1 start dstOld base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Sibling-framed q2 stack spec: `evm_mload_unaligned_one_limb_q2_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mload_unaligned_one_limb_q2_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q2_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 23 (base + 192) (base + 284)
      (mloadOneLimbCode addrReg byteReg accReg
        8 9 10 11 12 13 14 15 16 (base + 192))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal2 hiVal2 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
         (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q2_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld q0Old q1Old
    loAddr2 hiAddr2 loVal2 hiVal2 start dstOld base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q2 framed MLOAD spec: transports
`evm_mload_unaligned_one_limb_q2_stack_spec_within_framed` from the q2
one-limb block to the full `evm_mload_code` code requirement.

Distinctive token:
evm_mload_unaligned_one_limb_q2_spec_within_framed_public_code #53.
-/
theorem evm_mload_unaligned_one_limb_q2_spec_within_framed_public_code
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old : Word)
    (loAddr2 hiAddr2 loVal2 hiVal2 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr2 hiAddr2 start
                  8 9 10 11 12 13 14 15) :
    cpsTripleWithin 23 (base + 192) (base + 284)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal2 hiVal2 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal2 hiVal2 start) **
         (loAddr2 ↦ₘ loVal2) ** (hiAddr2 ↦ₘ hiVal2))) ** F) := by
  exact cpsTripleWithin_evm_mload_of_one_limb_q2
    offReg byteReg accReg addrReg memBaseReg base
    (evm_mload_unaligned_one_limb_q2_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld q0Old q1Old
      loAddr2 hiAddr2 loVal2 hiVal2 start dstOld base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)

/--
Sibling-framed q3 stack spec: `evm_mload_unaligned_one_limb_q3_stack_spec_within`
with an arbitrary `pcFree` assertion `F` framed on both pre and post.

Distinctive token: evm_mload_unaligned_one_limb_q3_stack_spec_within_framed
sibling-quarter cells #53.
-/
theorem evm_mload_unaligned_one_limb_q3_stack_spec_within_framed
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old q2Old : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 23 (base + 284) (base + 376)
      (mloadOneLimbCode addrReg byteReg accReg
        0 1 2 3 4 5 6 7 24 (base + 284))
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ q2Old) **
        (sp + 24 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ q2Old) **
        (sp + 24 ↦ₘ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal3 hiVal3 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
         (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) ** F) := by
  have core := evm_mload_unaligned_one_limb_q3_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset memBase byteOld accOld q0Old q1Old q2Old
    loAddr3 hiAddr3 loVal3 hiVal3 start dstOld base
    h_byte_ne_x0 h_acc_ne_x0 h_window
  have framed := cpsTripleWithin_frameL (F := F) hF core
  exact cpsTripleWithin_weaken
    (fun _ hp => by sep_perm hp)
    (fun _ hp => by sep_perm hp)
    framed

/--
Public-code q3 framed MLOAD spec: transports
`evm_mload_unaligned_one_limb_q3_stack_spec_within_framed` from the q3
one-limb block to the full `evm_mload_code` code requirement.

Distinctive token:
evm_mload_unaligned_one_limb_q3_spec_within_framed_public_code #53.
-/
theorem evm_mload_unaligned_one_limb_q3_spec_within_framed_public_code
    (offReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset memBase byteOld accOld : Word)
    (q0Old q1Old q2Old : Word)
    (loAddr3 hiAddr3 loVal3 hiVal3 : Word) (start : Nat)
    (dstOld : Word)
    (base : Word)
    (F : Assertion) (hF : F.pcFree)
    (h_byte_ne_x0 : byteReg ≠ .x0) (h_acc_ne_x0 : accReg ≠ .x0)
    (h_window : mloadLimbWindowOk (memBase + offset) loAddr3 hiAddr3 start
                  0 1 2 3 4 5 6 7) :
    cpsTripleWithin 23 (base + 284) (base + 376)
      (evm_mload_code offReg byteReg accReg addrReg memBaseReg base)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ q2Old) **
        (sp + 24 ↦ₘ dstOld) **
        ((byteReg ↦ᵣ byteOld) ** (accReg ↦ᵣ accOld) **
         (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) ** F)
      ((((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
        (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
        (sp ↦ₘ q0Old) **
        (sp + 8 ↦ₘ q1Old) **
        (sp + 16 ↦ₘ q2Old) **
        (sp + 24 ↦ₘ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
        ((byteReg ↦ᵣ
           (mloadByteFromDwordPair loVal3 hiVal3 start 7).zeroExtend 64) **
         (accReg ↦ᵣ mloadPackedLimbFromDwordPair loVal3 hiVal3 start) **
         (loAddr3 ↦ₘ loVal3) ** (hiAddr3 ↦ₘ hiVal3))) ** F) := by
  exact cpsTripleWithin_evm_mload_of_one_limb_q3
    offReg byteReg accReg addrReg memBaseReg base
    (evm_mload_unaligned_one_limb_q3_stack_spec_within_framed
      offReg byteReg accReg addrReg memBaseReg
      sp offset memBase byteOld accOld q0Old q1Old q2Old
      loAddr3 hiAddr3 loVal3 hiVal3 start dstOld base F hF
      h_byte_ne_x0 h_acc_ne_x0 h_window)


end EvmAsm.Evm64
