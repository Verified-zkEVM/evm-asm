/-
  EvmAsm.Evm64.MStore.CombinedSequenceSpec

  MSTORE combined one-limb sequence stack spec on `mstoreStackCode`.

  Split out of `EvmAsm.Evm64.MStore.Spec` to keep that file under the
  1500-line repo guardrail. Holds the per-quarter `mstoreOneLimbCode`
  variant of `mstore_combined_four_limb_sequence_stack_spec_within`.
-/

import EvmAsm.Evm64.MStore.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/--
MSTORE combined one-limb sequence stack spec: combine the prologue half
(`mstore_prologue_stack_spec_within`) with the four byte-window quarter
triples (composed via `mstore_one_limb_sequence_spec_within`) into a single
triple from `base` to `base + 280` over `mstoreStackCode`.

Direct analog of `calldataload_window_combined_one_limb_sequence_stack_spec_within`
(`EvmAsm/Evm64/Calldata/LoadStackCode.lean`) and the in-flight MLOAD analog
`mload_combined_one_limb_sequence_stack_spec_within`. This is a one-line
composition of `mstore_combined_stack_spec_within` (which takes a single
four-limbs core triple over `mstoreStackCode`) with
`mstore_one_limb_sequence_spec_within` (which produces that consolidated
four-limbs triple over `mstoreFourLimbsCode`), transported to
`mstoreStackCode` via `cpsTripleWithin_extend_code` /
`mstoreStackCode_four_limbs_sub`. Mirrors
`mstore_combined_four_limb_sequence_stack_spec_within` but takes per-quarter
`mstoreOneLimbCode` triples instead of `mstoreFourLimbsCode` wrappers,
eliminating an intermediate transport step in followup slices that wire
concrete byte-window write triples toward the full
`evm_mstore_stack_spec_within_region` (evm-asm-ln8t5 / GH #53 follow-up).

Distinctive token: mstore_combined_one_limb_sequence_stack_spec_within #53.
-/
theorem mstore_combined_one_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg memBaseReg : Reg)
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
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (memBaseReg ↦ᵣ memBase) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  mstore_combined_stack_spec_within
    offReg byteReg accReg addrReg memBaseReg
    sp offset offOld addrOld memBase base h_off_ne_x0 h_addr_ne_x0
    (cpsTripleWithin_extend_code
      (h := mstore_one_limb_sequence_spec_within
        addrReg byteReg accReg base h0 h1 h2 h3)
      (hmono := mstoreStackCode_four_limbs_sub
        offReg byteReg accReg addrReg memBaseReg base))

end EvmAsm.Evm64
