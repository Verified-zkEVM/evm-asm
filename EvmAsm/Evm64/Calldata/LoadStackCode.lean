/-
  EvmAsm.Evm64.Calldata.LoadStackCode

  CodeReq bridge from the CALLDATALOAD in-bounds byte-window core to the
  reusable MLOAD stack-code surface.
-/

module

public import EvmAsm.Evm64.Calldata.LoadProgram
public import EvmAsm.Evm64.Calldata.LoadArgs
public import EvmAsm.Evm64.MLoad.StackSpec

@[expose] public section

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/--
The in-bounds CALLDATALOAD byte-window core has the same CodeReq shape as
the reusable MLOAD stack-code bundle.

Distinctive token:
Calldata.LoadStackCode.evm_calldataload_window_code_eq_mloadStackCode #104 #99.
-/
theorem evm_calldataload_window_code_eq_mloadStackCode
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word) :
    evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base =
      mloadStackCode offReg byteReg accReg addrReg envPtrReg base := by
  rw [evm_calldataload_window_code_eq_evm_mload_code]
  unfold evm_mload_code mloadStackCode
  rw [mloadPrologueCode_eq_ofProg, mloadFourLimbsCode_eq_ofProg]
  rw [show base + 8 =
      base + BitVec.ofNat 64
        (4 * (LD offReg .x12 0 ;; ADD addrReg envPtrReg offReg).length) from by
    simp [LD, ADD, single, seq]]
  rw [← CodeReq.ofProg_append]
  unfold evm_mload mloadFourLimbsProg mloadTwoLimbsProg
  rfl

/--
Transport an MLOAD stack-code triple to the program-identical in-bounds
CALLDATALOAD window core.
-/
theorem evm_calldataload_window_of_mloadStackCode_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base endPc : Word)
    (h : cpsTripleWithin n base endPc
      (mloadStackCode offReg byteReg accReg addrReg envPtrReg base) P Q) :
    cpsTripleWithin n base endPc
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  exact h

/--
Transport an `evm_mload_code` triple to the program-identical in-bounds
CALLDATALOAD window core. This is the direct EVM-code sibling of
`evm_calldataload_window_of_mloadStackCode_spec_within`.

Distinctive token:
Calldata.LoadStackCode.evm_calldataload_window_of_evm_mload_spec_within #104.
-/
theorem evm_calldataload_window_of_evm_mload_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base endPc : Word)
    (h : cpsTripleWithin n base endPc
      (evm_mload_code offReg byteReg accReg addrReg envPtrReg base) P Q) :
    cpsTripleWithin n base endPc
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_evm_mload_code]
  exact h

/--
CALLDATALOAD prologue stack spec: pop the calldata offset from the EVM stack
slot at `x12` and resolve the source byte pointer
`addrReg ← envPtrReg + offReg` where `envPtrReg` holds `env.callDataPtr`.

This is the program-identical transport of `mload_prologue_stack_spec_within`
through `evm_calldataload_window_of_mloadStackCode_spec_within`. It splits
the upcoming `evm_calldataload_stack_spec` (evm-asm-pgeuo / GH #104) into a
prologue half plus a four-limb half so subsequent slices only need to wire
the four-limb byte-window read.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_prologue_stack_spec_within #104.
-/
theorem calldataload_window_prologue_stack_spec_within
    (offReg byteReg accReg addrReg envPtrReg : Reg)
    (sp offset offOld addrOld envPtr : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0) :
    cpsTripleWithin 2 base (base + 8)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ (envPtr + offset)) **
       (sp ↦ₘ offset)) :=
  evm_calldataload_window_of_mloadStackCode_spec_within
    offReg byteReg accReg addrReg envPtrReg base (base + 8)
    (mload_prologue_stack_spec_within offReg byteReg accReg addrReg envPtrReg
      sp offset offOld addrOld envPtr base h_off_ne_x0 h_addr_ne_x0)

/--
Transport the MLOAD four-limbs stack spec to the program-identical in-bounds
CALLDATALOAD window core. Mirrors `calldataload_window_prologue_stack_spec_within`
for the four-limbs side: combined, both pieces give the prologue + byte-window
ingredients for the upcoming `evm_calldataload_stack_spec`
(evm-asm-pgeuo / GH #104).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_four_limbs_stack_spec_within #104.
-/
theorem calldataload_window_four_limbs_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 376)
        (mloadFourLimbsCode addrReg byteReg accReg base) P Q) :
    cpsTripleWithin n (base + 8) (base + 376)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  exact mload_four_limbs_stack_spec_within
    offReg byteReg accReg addrReg envPtrReg base h

/--
CALLDATALOAD window four-limb sequence stack spec: compose four
program-identical `mloadFourLimbsCode` triples (one per byte-window quarter
spanning `base + 8 .. base + 100 .. 192 .. 284 .. 376`) into a single triple
on the in-bounds `evm_calldataload_window_code`. Mirrors
`mload_four_limb_sequence_spec_within` plus the
`calldataload_window_four_limbs_stack_spec_within` transport.

Subsequent slices can instantiate each `hN` with a concrete byte-load triple
to obtain a single four-limb byte-window read in the calldataload setting,
without re-doing the program-identity transport.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_four_limb_sequence_stack_spec_within #104.
-/
theorem calldataload_window_four_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
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
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P0 P4 :=
  calldataload_window_four_limbs_stack_spec_within
    offReg byteReg accReg addrReg envPtrReg base
    (mload_four_limb_sequence_spec_within
      addrReg byteReg accReg base h0 h1 h2 h3)

/--
CALLDATALOAD window combined stack spec: sequentially compose the prologue
half (`calldataload_window_prologue_stack_spec_within`) with a caller-supplied
four-limbs core triple via `cpsTripleWithin_seq_same_cr`.

Takes the four-limbs core triple as a hypothesis whose precondition matches
the prologue's postcondition (after the `addrReg ← envPtr + offset` resolve)
and whose postcondition is an arbitrary `Q`. The prologue threads
`(sp ↦ₘ offset)` and the resolved address registers through to the four-limbs
side, so the caller only needs to instantiate the four-limbs hypothesis with
a concrete byte-window read (e.g. via `mload_four_limbs_stack_spec_within`
together with a concrete byte-window core spec).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_combined_stack_spec_within #104.
-/
theorem calldataload_window_combined_stack_spec_within
    {n : Nat} {Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg)
    (sp offset offOld addrOld envPtr : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h4 :
      cpsTripleWithin n (base + 8) (base + 376)
        (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ (envPtr + offset)) **
         (sp ↦ₘ offset))
        Q) :
    cpsTripleWithin (2 + n) base (base + 376)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  cpsTripleWithin_seq_same_cr
    (calldataload_window_prologue_stack_spec_within
      offReg byteReg accReg addrReg envPtrReg
      sp offset offOld addrOld envPtr base h_off_ne_x0 h_addr_ne_x0)
    h4

/--
CALLDATALOAD window combined four-limb sequence stack spec: combine the
prologue half (`calldataload_window_prologue_stack_spec_within`) with the
four byte-window quarter triples (composed via
`calldataload_window_four_limb_sequence_stack_spec_within`) into a single
triple from `base` to `base + 376` over `evm_calldataload_window_code`.

This is a one-line composition of the existing combined spec
(`calldataload_window_combined_stack_spec_within`, which takes a single
four-limbs core triple) with the four-limb sequence spec
(`calldataload_window_four_limb_sequence_stack_spec_within`, which produces
that consolidated four-limbs triple from four byte-window quarter triples).
Subsequent slices instantiate each `hN` with a concrete byte-load triple to
land the full `evm_calldataload_stack_spec` (evm-asm-pgeuo / GH #104) without
re-doing the prologue/transport plumbing.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_combined_four_limb_sequence_stack_spec_within #104.
-/
theorem calldataload_window_combined_four_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg)
    (sp offset offOld addrOld envPtr : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadFourLimbsCode addrReg byteReg accReg base)
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ (envPtr + offset)) **
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
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  calldataload_window_combined_stack_spec_within
    offReg byteReg accReg addrReg envPtrReg
    sp offset offOld addrOld envPtr base h_off_ne_x0 h_addr_ne_x0
    (calldataload_window_four_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg envPtrReg base h0 h1 h2 h3)

/--
The byte-level semantic word produced by the CALLDATALOAD in-bounds window,
phrased through decoded stack arguments.

Distinctive token:
Calldata.LoadStackCode.calldataLoadWindowOutputWordFromArgs #104.
-/
def calldataLoadWindowOutputWordFromArgs
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) : EvmWord :=
  mloadLoadedWordFromBytes
    (CallDataLoadArgs.windowByteFromArgs data args 0)
    (CallDataLoadArgs.windowByteFromArgs data args 1)
    (CallDataLoadArgs.windowByteFromArgs data args 2)
    (CallDataLoadArgs.windowByteFromArgs data args 3)
    (CallDataLoadArgs.windowByteFromArgs data args 4)
    (CallDataLoadArgs.windowByteFromArgs data args 5)
    (CallDataLoadArgs.windowByteFromArgs data args 6)
    (CallDataLoadArgs.windowByteFromArgs data args 7)
    (CallDataLoadArgs.windowByteFromArgs data args 8)
    (CallDataLoadArgs.windowByteFromArgs data args 9)
    (CallDataLoadArgs.windowByteFromArgs data args 10)
    (CallDataLoadArgs.windowByteFromArgs data args 11)
    (CallDataLoadArgs.windowByteFromArgs data args 12)
    (CallDataLoadArgs.windowByteFromArgs data args 13)
    (CallDataLoadArgs.windowByteFromArgs data args 14)
    (CallDataLoadArgs.windowByteFromArgs data args 15)
    (CallDataLoadArgs.windowByteFromArgs data args 16)
    (CallDataLoadArgs.windowByteFromArgs data args 17)
    (CallDataLoadArgs.windowByteFromArgs data args 18)
    (CallDataLoadArgs.windowByteFromArgs data args 19)
    (CallDataLoadArgs.windowByteFromArgs data args 20)
    (CallDataLoadArgs.windowByteFromArgs data args 21)
    (CallDataLoadArgs.windowByteFromArgs data args 22)
    (CallDataLoadArgs.windowByteFromArgs data args 23)
    (CallDataLoadArgs.windowByteFromArgs data args 24)
    (CallDataLoadArgs.windowByteFromArgs data args 25)
    (CallDataLoadArgs.windowByteFromArgs data args 26)
    (CallDataLoadArgs.windowByteFromArgs data args 27)
    (CallDataLoadArgs.windowByteFromArgs data args 28)
    (CallDataLoadArgs.windowByteFromArgs data args 29)
    (CallDataLoadArgs.windowByteFromArgs data args 30)
    (CallDataLoadArgs.windowByteFromArgs data args 31)

/--
The low stack limb of the CALLDATALOAD byte-window word is the packed
least-significant byte block produced by the window core.
-/
theorem getLimbN_calldataLoadWindowOutputWordFromArgs_0
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 0 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 24)
        (CallDataLoadArgs.windowByteFromArgs data args 25)
        (CallDataLoadArgs.windowByteFromArgs data args 26)
        (CallDataLoadArgs.windowByteFromArgs data args 27)
        (CallDataLoadArgs.windowByteFromArgs data args 28)
        (CallDataLoadArgs.windowByteFromArgs data args 29)
        (CallDataLoadArgs.windowByteFromArgs data args 30)
        (CallDataLoadArgs.windowByteFromArgs data args 31) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_0]

theorem getLimbN_calldataLoadWindowOutputWordFromArgs_1
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 1 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 16)
        (CallDataLoadArgs.windowByteFromArgs data args 17)
        (CallDataLoadArgs.windowByteFromArgs data args 18)
        (CallDataLoadArgs.windowByteFromArgs data args 19)
        (CallDataLoadArgs.windowByteFromArgs data args 20)
        (CallDataLoadArgs.windowByteFromArgs data args 21)
        (CallDataLoadArgs.windowByteFromArgs data args 22)
        (CallDataLoadArgs.windowByteFromArgs data args 23) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_1]

theorem getLimbN_calldataLoadWindowOutputWordFromArgs_2
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 2 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 8)
        (CallDataLoadArgs.windowByteFromArgs data args 9)
        (CallDataLoadArgs.windowByteFromArgs data args 10)
        (CallDataLoadArgs.windowByteFromArgs data args 11)
        (CallDataLoadArgs.windowByteFromArgs data args 12)
        (CallDataLoadArgs.windowByteFromArgs data args 13)
        (CallDataLoadArgs.windowByteFromArgs data args 14)
        (CallDataLoadArgs.windowByteFromArgs data args 15) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_2]

/--
Distinctive token:
Calldata.LoadStackCode.getLimbN_calldataLoadWindowOutputWordFromArgs_3 #104 #107.
-/
theorem getLimbN_calldataLoadWindowOutputWordFromArgs_3
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (calldataLoadWindowOutputWordFromArgs data args).getLimbN 3 =
      mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 0)
        (CallDataLoadArgs.windowByteFromArgs data args 1)
        (CallDataLoadArgs.windowByteFromArgs data args 2)
        (CallDataLoadArgs.windowByteFromArgs data args 3)
        (CallDataLoadArgs.windowByteFromArgs data args 4)
        (CallDataLoadArgs.windowByteFromArgs data args 5)
        (CallDataLoadArgs.windowByteFromArgs data args 6)
        (CallDataLoadArgs.windowByteFromArgs data args 7) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [getLimbN_mloadLoadedWordFromBytes_3]

/--
Fold the four MLOAD-style packed output limbs produced by the CALLDATALOAD
window core into the EVM word selected by decoded calldata arguments.

Distinctive token:
Calldata.LoadStackCode.calldataLoadWindowOutputWordFromArgs_evmWordIs_fold #104.
-/
theorem calldataLoadWindowOutputWordFromArgs_evmWordIs_fold
    (sp : Word) (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    ((sp ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 24)
        (CallDataLoadArgs.windowByteFromArgs data args 25)
        (CallDataLoadArgs.windowByteFromArgs data args 26)
        (CallDataLoadArgs.windowByteFromArgs data args 27)
        (CallDataLoadArgs.windowByteFromArgs data args 28)
        (CallDataLoadArgs.windowByteFromArgs data args 29)
        (CallDataLoadArgs.windowByteFromArgs data args 30)
        (CallDataLoadArgs.windowByteFromArgs data args 31)) **
      ((sp + 8) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 16)
        (CallDataLoadArgs.windowByteFromArgs data args 17)
        (CallDataLoadArgs.windowByteFromArgs data args 18)
        (CallDataLoadArgs.windowByteFromArgs data args 19)
        (CallDataLoadArgs.windowByteFromArgs data args 20)
        (CallDataLoadArgs.windowByteFromArgs data args 21)
        (CallDataLoadArgs.windowByteFromArgs data args 22)
        (CallDataLoadArgs.windowByteFromArgs data args 23)) **
      ((sp + 16) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 8)
        (CallDataLoadArgs.windowByteFromArgs data args 9)
        (CallDataLoadArgs.windowByteFromArgs data args 10)
        (CallDataLoadArgs.windowByteFromArgs data args 11)
        (CallDataLoadArgs.windowByteFromArgs data args 12)
        (CallDataLoadArgs.windowByteFromArgs data args 13)
        (CallDataLoadArgs.windowByteFromArgs data args 14)
        (CallDataLoadArgs.windowByteFromArgs data args 15)) **
      ((sp + 24) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 0)
        (CallDataLoadArgs.windowByteFromArgs data args 1)
        (CallDataLoadArgs.windowByteFromArgs data args 2)
        (CallDataLoadArgs.windowByteFromArgs data args 3)
        (CallDataLoadArgs.windowByteFromArgs data args 4)
        (CallDataLoadArgs.windowByteFromArgs data args 5)
        (CallDataLoadArgs.windowByteFromArgs data args 6)
        (CallDataLoadArgs.windowByteFromArgs data args 7))) =
    evmWordIs sp (calldataLoadWindowOutputWordFromArgs data args) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [mloadLoadedWordFromBytes_evmWordIs_fold]

/--
Fold the four MLOAD-style packed output limbs produced by the CALLDATALOAD
window core into the EVM stack word selected by decoded calldata arguments.
-/
theorem calldataLoadWindowOutputWordFromArgs_evmStackIs_fold
    (sp : Word) (rest : List EvmWord)
    (data : List (BitVec 8)) (args : CallDataLoadArgs.Args) :
    (((sp ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 24)
        (CallDataLoadArgs.windowByteFromArgs data args 25)
        (CallDataLoadArgs.windowByteFromArgs data args 26)
        (CallDataLoadArgs.windowByteFromArgs data args 27)
        (CallDataLoadArgs.windowByteFromArgs data args 28)
        (CallDataLoadArgs.windowByteFromArgs data args 29)
        (CallDataLoadArgs.windowByteFromArgs data args 30)
        (CallDataLoadArgs.windowByteFromArgs data args 31)) **
      ((sp + 8) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 16)
        (CallDataLoadArgs.windowByteFromArgs data args 17)
        (CallDataLoadArgs.windowByteFromArgs data args 18)
        (CallDataLoadArgs.windowByteFromArgs data args 19)
        (CallDataLoadArgs.windowByteFromArgs data args 20)
        (CallDataLoadArgs.windowByteFromArgs data args 21)
        (CallDataLoadArgs.windowByteFromArgs data args 22)
        (CallDataLoadArgs.windowByteFromArgs data args 23)) **
      ((sp + 16) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 8)
        (CallDataLoadArgs.windowByteFromArgs data args 9)
        (CallDataLoadArgs.windowByteFromArgs data args 10)
        (CallDataLoadArgs.windowByteFromArgs data args 11)
        (CallDataLoadArgs.windowByteFromArgs data args 12)
        (CallDataLoadArgs.windowByteFromArgs data args 13)
        (CallDataLoadArgs.windowByteFromArgs data args 14)
        (CallDataLoadArgs.windowByteFromArgs data args 15)) **
      ((sp + 24) ↦ₘ mloadPackedLimb
        (CallDataLoadArgs.windowByteFromArgs data args 0)
        (CallDataLoadArgs.windowByteFromArgs data args 1)
        (CallDataLoadArgs.windowByteFromArgs data args 2)
        (CallDataLoadArgs.windowByteFromArgs data args 3)
        (CallDataLoadArgs.windowByteFromArgs data args 4)
        (CallDataLoadArgs.windowByteFromArgs data args 5)
        (CallDataLoadArgs.windowByteFromArgs data args 6)
        (CallDataLoadArgs.windowByteFromArgs data args 7))) **
      evmStackIs (sp + 32) rest) =
    evmStackIs sp (calldataLoadWindowOutputWordFromArgs data args :: rest) := by
  unfold calldataLoadWindowOutputWordFromArgs
  rw [mloadLoadedWordFromBytes_evmStackIs_fold]

/--
CALLDATALOAD window q0 one-limb stack spec: transport a concrete
`mloadOneLimbCode` byte-load triple at `base + 8 .. base + 100` (the
least-significant one-limb byte-pack block within `mloadFourLimbsCode`)
to the program-identical `evm_calldataload_window_code`.

Lets followup slices instantiate `h0` of
`calldataload_window_combined_four_limb_sequence_stack_spec_within`
directly with a concrete byte-load triple, without first wrapping in
`mloadFourLimbsCode`. q1/q2/q3 quarters land in followup sub-slices
(each needs its own subsumption witness).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_one_limb_q0_stack_spec_within #104.
-/
theorem calldataload_window_one_limb_q0_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8)) P Q) :
    cpsTripleWithin n (base + 8) (base + 100)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  refine cpsTripleWithin_extend_code (hmono := ?_) h
  intro a i hq
  exact mloadStackCode_four_limbs_sub
    offReg byteReg accReg addrReg envPtrReg base a i
    (mloadFourLimbsCode_one_limb_q0_sub addrReg byteReg accReg base a i hq)

/--
CALLDATALOAD window q1 one-limb stack spec: transport a concrete
`mloadOneLimbCode` byte-load triple at `base + 100 .. base + 192` (the
second one-limb byte-pack block within `mloadFourLimbsCode`) to the
program-identical `evm_calldataload_window_code`.

Sister to `calldataload_window_one_limb_q0_stack_spec_within`. Lets
followup slices instantiate `h1` of
`calldataload_window_combined_four_limb_sequence_stack_spec_within`
directly with a concrete byte-load triple. q2/q3 quarters land in
followup sub-slices.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_one_limb_q1_stack_spec_within #104.
-/
theorem calldataload_window_one_limb_q1_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 100) (base + 192)
        (mloadOneLimbCode addrReg byteReg accReg
          16 17 18 19 20 21 22 23 8 (base + 100)) P Q) :
    cpsTripleWithin n (base + 100) (base + 192)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  refine cpsTripleWithin_extend_code (hmono := ?_) h
  intro a i hq
  exact mloadStackCode_four_limbs_sub
    offReg byteReg accReg addrReg envPtrReg base a i
    (mloadFourLimbsCode_one_limb_q1_sub addrReg byteReg accReg base a i hq)

/--
CALLDATALOAD window q2 one-limb stack spec: transport a concrete
`mloadOneLimbCode` byte-load triple at `base + 192 .. base + 284` (the
third one-limb byte-pack block within `mloadFourLimbsCode`) to the
program-identical `evm_calldataload_window_code`.

Sister to `calldataload_window_one_limb_q0_stack_spec_within` and
`calldataload_window_one_limb_q1_stack_spec_within`. Lets followup slices
instantiate `h2` of
`calldataload_window_combined_four_limb_sequence_stack_spec_within`
directly with a concrete byte-load triple. q3 quarter lands in a
followup sub-slice.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_one_limb_q2_stack_spec_within #104.
-/
theorem calldataload_window_one_limb_q2_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 192) (base + 284)
        (mloadOneLimbCode addrReg byteReg accReg
          8 9 10 11 12 13 14 15 16 (base + 192)) P Q) :
    cpsTripleWithin n (base + 192) (base + 284)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  refine cpsTripleWithin_extend_code (hmono := ?_) h
  intro a i hq
  exact mloadStackCode_four_limbs_sub
    offReg byteReg accReg addrReg envPtrReg base a i
    (mloadFourLimbsCode_one_limb_q2_sub addrReg byteReg accReg base a i hq)

/--
CALLDATALOAD window q3 one-limb stack spec: transport a concrete
`mloadOneLimbCode` byte-load triple at `base + 284 .. base + 376` (the
fourth/rightmost one-limb byte-pack block within `mloadFourLimbsCode`)
to the program-identical `evm_calldataload_window_code`.

Sister to `calldataload_window_one_limb_q0_stack_spec_within`,
`_q1_stack_spec_within`, and `_q2_stack_spec_within`. Closes the four
quarter sub-slices toward `evm-asm-pgeuo` (#104) — lets followup slices
instantiate `h3` of
`calldataload_window_combined_four_limb_sequence_stack_spec_within`
directly with a concrete byte-load triple, without first wrapping in
`mloadFourLimbsCode`.

Distinctive token:
Calldata.LoadStackCode.calldataload_window_one_limb_q3_stack_spec_within #104.
-/
theorem calldataload_window_one_limb_q3_stack_spec_within
    {n : Nat} {P Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
    (h :
      cpsTripleWithin n (base + 284) (base + 376)
        (mloadOneLimbCode addrReg byteReg accReg
          0 1 2 3 4 5 6 7 24 (base + 284)) P Q) :
    cpsTripleWithin n (base + 284) (base + 376)
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P Q := by
  rw [evm_calldataload_window_code_eq_mloadStackCode]
  refine cpsTripleWithin_extend_code (hmono := ?_) h
  intro a i hq
  exact mloadStackCode_four_limbs_sub
    offReg byteReg accReg addrReg envPtrReg base a i
    (mloadFourLimbsCode_one_limb_q3_sub addrReg byteReg accReg base a i hq)

/--
CALLDATALOAD window one-limb sequence stack spec: compose the four merged
per-quarter wrappers (`calldataload_window_one_limb_q{0,1,2,3}_stack_spec_within`)
into a single triple from `base + 8` to `base + 376` over
`evm_calldataload_window_code`.

Takes one concrete `mloadOneLimbCode` byte-load triple per byte-window quarter
and chains them via three `cpsTripleWithin_seq_same_cr` applications. Lets
followup slices instantiate each quarter directly with a concrete byte-load
triple (without first wrapping in `mloadFourLimbsCode` and then
`mload_four_limb_sequence_spec_within`), and then combine with
`calldataload_window_prologue_stack_spec_within` to land the full
`evm_calldataload_stack_spec` (evm-asm-pgeuo / GH #104).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_one_limb_sequence_stack_spec_within #104.
-/
theorem calldataload_window_one_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P0 P1 P2 P3 P4 : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word)
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
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      P0 P4 :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_seq_same_cr
      (cpsTripleWithin_seq_same_cr
        (calldataload_window_one_limb_q0_stack_spec_within
          offReg byteReg accReg addrReg envPtrReg base h0)
        (calldataload_window_one_limb_q1_stack_spec_within
          offReg byteReg accReg addrReg envPtrReg base h1))
      (calldataload_window_one_limb_q2_stack_spec_within
        offReg byteReg accReg addrReg envPtrReg base h2))
    (calldataload_window_one_limb_q3_stack_spec_within
      offReg byteReg accReg addrReg envPtrReg base h3)

/--
CALLDATALOAD window combined one-limb sequence stack spec: combine the
prologue half (`calldataload_window_prologue_stack_spec_within`) with the
four byte-window quarter triples (composed via
`calldataload_window_one_limb_sequence_stack_spec_within`) into a single
triple from `base` to `base + 376` over `evm_calldataload_window_code`.

This is a one-line composition of the existing combined spec
(`calldataload_window_combined_stack_spec_within`, which takes a single
four-limbs core triple) with the one-limb sequence spec
(`calldataload_window_one_limb_sequence_stack_spec_within`, which produces
that consolidated four-limbs triple from four byte-window quarter
`mloadOneLimbCode` triples directly). Mirrors
`calldataload_window_combined_four_limb_sequence_stack_spec_within`, but
takes per-quarter `mloadOneLimbCode` triples instead of `mloadFourLimbsCode`
wrappers, eliminating an intermediate transport step in followup slices that
wire concrete byte-load triples toward the full `evm_calldataload_stack_spec`
(evm-asm-pgeuo / GH #104).

Distinctive token:
Calldata.LoadStackCode.calldataload_window_combined_one_limb_sequence_stack_spec_within #104.
-/
theorem calldataload_window_combined_one_limb_sequence_stack_spec_within
    {n0 n1 n2 n3 : Nat} {P1 P2 P3 Q : Assertion}
    (offReg byteReg accReg addrReg envPtrReg : Reg)
    (sp offset offOld addrOld envPtr : Word) (base : Word)
    (h_off_ne_x0 : offReg ≠ .x0)
    (h_addr_ne_x0 : addrReg ≠ .x0)
    (h0 :
      cpsTripleWithin n0 (base + 8) (base + 100)
        (mloadOneLimbCode addrReg byteReg accReg
          24 25 26 27 28 29 30 31 0 (base + 8))
        (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offset) **
         (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ (envPtr + offset)) **
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
      (evm_calldataload_window_code offReg byteReg accReg addrReg envPtrReg base)
      (((.x12 : Reg) ↦ᵣ sp) ** (offReg ↦ᵣ offOld) **
       (envPtrReg ↦ᵣ envPtr) ** (addrReg ↦ᵣ addrOld) **
       (sp ↦ₘ offset))
      Q :=
  calldataload_window_combined_stack_spec_within
    offReg byteReg accReg addrReg envPtrReg
    sp offset offOld addrOld envPtr base h_off_ne_x0 h_addr_ne_x0
    (calldataload_window_one_limb_sequence_stack_spec_within
      offReg byteReg accReg addrReg envPtrReg base h0 h1 h2 h3)

end Calldata
end EvmAsm.Evm64
