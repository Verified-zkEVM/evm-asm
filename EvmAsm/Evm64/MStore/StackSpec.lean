/-
  EvmAsm.Evm64.MStore.StackSpec

  Stack-level bridge helpers for MSTORE.  Direct MSTORE analogs of the
  `MLoad/StackSpec.lean` lemmas: lift triples over `mstoreStackCode`
  to triples over `evm_mstore_code`.
-/

import EvmAsm.Evm64.MStore.Spec
import EvmAsm.Evm64.MStore.CombinedSequenceSpec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Sub-monotonicity: `mstoreStackCode` is contained in `evm_mstore_code` (they
    are in fact equal by `mstoreStackCode_eq_evm_mstore_code`).  Direct MSTORE
    analog of `evm_mload_code_stack_sub` (PR #3102, evm-asm-rw24y).

    Distinctive token: evm_mstore_code_stack_sub #53. -/
theorem evm_mstore_code_stack_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  rw [mstoreStackCode_eq_evm_mstore_code
    offReg valReg byteReg accReg addrReg memBaseReg base]
  intro _ _ h; exact h

/-- Transport a `cpsTripleWithin` over `mstoreStackCode` to one over
    `evm_mstore_code`.  Subsequent slices use this to land
    `evm_mstore_stack_spec_within_region` (evm-asm-ln8t5 / GH #53 follow-up) by
    composing the existing `mstore_combined_*_stack_spec_within` lemmas
    (over `mstoreStackCode`) with concrete byte-window write triples.

    Direct MSTORE analog of `cpsTripleWithin_evm_mload_of_stack`
    (PR #3102, evm-asm-rw24y).

    Distinctive token: cpsTripleWithin_evm_mstore_of_stack #53. -/
theorem cpsTripleWithin_evm_mstore_of_stack
    {n : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (base pcEnd : Word)
    (h :
      cpsTripleWithin n base pcEnd
        (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) P Q) :
    cpsTripleWithin n base pcEnd
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_stack_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

/--
MSTORE evm_mstore_code lift of `mstore_combined_one_limb_sequence_stack_spec_within`:
the same combined prologue + four byte-window write triples, transported from
`mstoreStackCode` to `evm_mstore_code` via `cpsTripleWithin_evm_mstore_of_stack`.

Subsequent slices toward `evm_mstore_stack_spec_within_region` (evm-asm-ln8t5 / GH #53
follow-up) instantiate each `hN` with a concrete byte-window write triple and
apply this helper to land a `cpsTripleWithin` over `evm_mstore_code` in one
step, without re-applying the stack-code → evm_mstore_code transport at every
call site. Direct MSTORE analog of
`evm_mload_combined_one_limb_sequence_stack_spec_within` (PR #3105,
evm-asm-g5l79).

Distinctive token: evm_mstore_combined_one_limb_sequence_stack_spec_within #53.
-/
theorem evm_mstore_combined_one_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
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
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 280)
    (mstore_combined_one_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
      h0 h1 h2 h3)

/--
MSTORE evm_mstore_code lift of `mstore_combined_stack_spec_within`: the same
combined prologue + single caller-supplied body triple, transported from
`mstoreStackCode` to `evm_mstore_code` via `cpsTripleWithin_evm_mstore_of_stack`.

This is the coarse-granularity counterpart of
`evm_mstore_combined_one_limb_sequence_stack_spec_within`: callers that already
assemble the whole four-limbs body as one triple can land the public-code
prologue/body composition without bundling it into quarter hypotheses.

Distinctive token: evm_mstore_combined_stack_spec_within #53.
-/
theorem evm_mstore_combined_stack_spec_within
    {n : Nat} {Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
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
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 280)
    (mstore_combined_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0 h4)

/--
MSTORE evm_mstore_code lift of `mstore_full_stack_spec_within`: the same
prologue + caller-supplied four-limbs core triple + framed epilogue
composition, transported from `mstoreStackCode` to `evm_mstore_code` via
`cpsTripleWithin_evm_mstore_of_stack`.

Subsequent slices toward `evm_mstore_stack_spec_within_region` (evm-asm-ln8t5 /
GH #53 follow-up) instantiate `h4` with a concrete four-limbs byte-window
write triple over `mstoreStackCode` and apply this helper to land the
full `base .. base + 284` triple over `evm_mstore_code` in one step,
without re-applying the stack-code → evm_mstore_code transport at every
call site.

Distinctive token: evm_mstore_full_stack_spec_within #53.
-/
theorem evm_mstore_full_stack_spec_within
    {n : Nat} {F : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
    (hF : F.pcFree)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h4 :
      cpsTripleWithin n (base + 8) (base + 280)
        (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ (memBase + offset)) **
         (sp ↦ₘ offset))
        (((.x12 : Reg) ↦ᵣ sp) ** F)) :
    cpsTripleWithin (2 + n + 1) base (base + 284)
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ (sp + 64)) ** F) :=
  cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 284)
    (mstore_full_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base hF h_off_ne_x0 h_addr_ne_x0 h4)

/--
MSTORE evm_mstore_code lift of `mstore_combined_four_limb_sequence_stack_spec_within`:
the same combined prologue + four `mstoreFourLimbsCode` quarter triples,
transported from `mstoreStackCode` to `evm_mstore_code` via
`cpsTripleWithin_evm_mstore_of_stack`.

Sister of `evm_mstore_combined_one_limb_sequence_stack_spec_within` but at the
coarser `mstoreFourLimbsCode` granularity: callers supply each quarter triple
over the four-limbs body program (not over the per-byte one-limb program),
useful when the concrete byte-window write triple is naturally produced at
that surface (e.g. via `mstore_four_limb_sequence_spec_within` composition
with byte-window subspecs). Direct MSTORE analog of
`evm_mload_combined_four_limb_sequence_stack_spec_within` (PR #3110,
evm-asm-7jxqa).

Distinctive token: evm_mstore_combined_four_limb_sequence_stack_spec_within #53.
-/
theorem evm_mstore_combined_four_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (sp offset offOld addrOld memBase : Word) (base : Word)
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
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_evm_mstore_of_stack
    offReg valReg byteReg accReg addrReg memBaseReg base (base + 280)
    (mstore_combined_four_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg memBaseReg
      sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
      h0 h1 h2 h3)

end EvmAsm.Evm64
