/-
  Composition scaffolding for unconditional `block_verdict_tx_state_gas_array`.

  Status (a4gbr track):
  * Array tops (#10432+#10437+#10442): conditional on
    IntrinsicAssumed / TeerAssumed / BgvOffsetAssumed (named hyps).
  * Intrinsic leaf (#10434): framed success under ExtractAssumed +
    TypeDispatchAssumed; ets proven.
  * Discharge (`TxIntrinsicStateGasDischarge`): framed → IntrinsicAssumed
    shape at **off = 0, len = bs.length** (slice-eq-ambient), still under
    TisCalleeAssumptions. **regOwn temp peel DONE**
    (`intrinsicAssumed_success_flat_off0_own`); multi-tx ambient residual.
  * Teer leaf (prover1): targets TeerAssumed.applied_flat verbatim; body
    modulo input callees; will ping when top lands.
  * prior_exact (#10433): success + mid-loop overflow complete (gate sum).
  * **BgvOffsetAssumed DISCHARGED** (`bgvOffsetAssumed_fullCode`): ambient
    LBU compose for unaligned loop-site `bgv_u32le` (classical-3).
  * **TypeDispatchAssumed DISCHARGED** (`typeDispatchAssumed_fullCode`):
    success-domain leaf + memOwn/regOwn peel under fullCode (classical-3).

  Residual set for "unconditional" a4gbr claim (honest):
  1. TeerAssumed ← prover1 teer top (modulo remaining input callees)
  2. IntrinsicAssumed ← multi-tx ambient (off ≠ 0) + CodeReq mono into
     array fullCode (off=0 regOwn peel DONE)
   3. TisCalleeAssumptions ← ExtractAssumed: **Program convert DONE** +
       **stack honesty DONE** (`ExtractAssumed` pins `x2`+`stackFree 10`;
       `nIntrinsicStackDwords` 8→18; discharge `stackFree18_split`).
       **toBuf/tea honesty DONE** (`extractToBufOwn` 3 dwords + `teaScratchOwn`;
       `tisScratchOwn` 8 cells). Packaging substrate + extractSuccess domain.
        **Frame save/restore DONE** + **pre-zero DONE** (`extractPreZero` E+56→E+72) +
        **type_dispatch call DONE** (`extractTypeSuccess` E+72→E+112, value-carrying
        tea post) + **load type/inner DONE** (`extractLoadTypeInner` E+112→E+144) +
        **walk_init DONE** (`extractWalkInitCall`+BNE E+144→E+152) +
        **save cursor + first walk_next skip DONE** (`extractSaveCursor` E+152→E+160;
        `extractWalkNext0Call`+BNE E+184→E+192 under extractLinkedCode).
        **type-branch DONE** (`extractTypeBranchLegacy/T1/Type234`).
        **all type walk chains DONE**; **HaveField both exits DONE**
        (`extractHaveFieldCreation` + `extractHaveFieldCopy` → EpiRestore
        classical-3). Residual: top compose prologue…epilogue under
        extractSuccess → extractAssumed; fullCode∪extract
        (150-instr ofProg mono heartbeat residual — use extractLinkedCode first);
        ~~TypeDispatchAssumed~~ DONE — use `typeDispatch_discharged`

  4. ~~BgvOffsetAssumed~~ DONE — use `bgvOffset_discharged`
  5. Full eip8037_tx_gas_gate composition (separate residual of a4gbr.1)

  This module holds the residual inventory and import hooks. Concrete
  compose theorems land when prover1 teer top is available.
-/

import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayTop
import EvmAsm.Codegen.Programs.TxIntrinsicStateGasDischarge
import EvmAsm.Codegen.Programs.BgvOffsetDischarge
import EvmAsm.Codegen.Programs.TxTypeDispatchTisDischarge
import EvmAsm.Codegen.Programs.TxExtractToAddressModel
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Rv64.SAsm.AbiFrameCall

namespace EvmAsm.Codegen.BlockVerdictTxStateGasArrayCompose

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
  (BgvOffsetAssumed nIntrinsicSteps nIntrinsicStackDwords tisScratchOwn fullCode
    bgvOffsetAssumed_fullCode)
open EvmAsm.Codegen.TxIntrinsicStateGasSpec
  (TisCalleeAssumptions ExtractAssumed ExtractEntry TypeEntry LinkEts T
    TypeDispatchAssumed intrinsicAssumed_success_flat_off0
    intrinsicAssumed_success_flat_off0_own)
open EvmAsm.Codegen.TxTypeDispatchSpec (typeDispatchAssumed_fullCode)
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
  (TeerApplied pureIntrinsicStateGasSuccess)

/-- Discharged loop-site bgv contract. Pass as `hbgv` to
    `blockVerdictTxStateGasArray_bal0/balNez_spec_within`. -/
def bgvOffset_discharged : BgvOffsetAssumed fullCode :=
  bgvOffsetAssumed_fullCode

/-- Discharged type_dispatch contract for intrinsic TisCalleeAssumptions. -/
def typeDispatch_discharged : TypeDispatchAssumed TxIntrinsicStateGasSpec.fullCode :=
  typeDispatchAssumed_fullCode

/-- Residual inventory for the unconditional a4gbr deliverable.
    BgvOffset + TypeDispatchAssumed removed — use `*_discharged`. -/
structure A4gbrResiduals where
  /-- Extract assumed still residual; type_dispatch discharged. -/
  extract : ExtractAssumed TxIntrinsicStateGasSpec.fullCode
  /-- Multi-tx ambient intrinsic (off ≠ 0 or len ≠ blob.length).
      off=0 regOwn peel: `intrinsicAssumed_success_flat_off0_own`.
      Blocker: leaf specs own `bytesRegion loadPtr slice`; array has ambient
      `bytesRegion regionBase blob`. Split needs `8 ∣ off` (`bytesRegion_split`);
      RLP tx starts are not dword-aligned → need ambient re-spec of extract/
      type_dispatch (BgvOffset style) or byte-granular region split. -/
  ambientMultiTx : True := trivial
  /-- Teer leaf modulo its remaining input callees (prover1 scope). -/
  teerInputCallees : True := trivial

/-- Slice-eq-ambient discharge is available (off=0, full blob).
    Packaging into `IntrinsicAssumed` for arbitrary off/len remains residual. -/
theorem intrinsic_discharge_off0_available
    (asm : TisCalleeAssumptions TxIntrinsicStateGasSpec.fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 : Word)
    (bs : List (BitVec 8))
    (old5 old6 old7 old13 old14 old15 old16 : Word)
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : EvmAsm.Codegen.TxExtractToAddressModel.extractSuccess bs)
    (hsuccess : (EvmAsm.Codegen.TxTypeDispatchSpec.teerTxTypeDispatch bs).1 =
      (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret TxIntrinsicStateGasSpec.fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (.x10 ↦ᵣ regionBase) **
        (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) ** (.x7 ↦ᵣ old7) **
        (.x13 ↦ᵣ old13) ** (.x14 ↦ᵣ old14) ** (.x15 ↦ᵣ old15) **
        (.x16 ↦ᵣ old16) **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) :=
  intrinsicAssumed_success_flat_off0 asm hextract htype
    ret spVal regionBase outPtr oldOut s0 s1 s2 s3 s4 s5 s6 bs
    old5 old6 old7 old13 old14 old15 old16 hret hlink hextractOk hsuccess halign hover hvalid0

/-- Same as `intrinsic_discharge_off0_available` with regOwn temps
    (IntrinsicAssumed footprint). Multi-tx off≠0 still residual. -/
theorem intrinsic_discharge_off0_own_available
    (asm : TisCalleeAssumptions TxIntrinsicStateGasSpec.fullCode)
    (hextract : asm.extract.entry = ExtractEntry)
    (htype : asm.typeDispatch.entry = TypeEntry)
    (ret spVal regionBase outPtr oldOut : Word)
    (s0 s1 s2 s3 s4 s5 s6 : Word)
    (bs : List (BitVec 8))
    (hret : (ret &&& ~~~(1 : Word)) = ret)
    (hlink : (LinkEts &&& ~~~(1 : Word)) = LinkEts)
    (hextractOk : EvmAsm.Codegen.TxExtractToAddressModel.extractSuccess bs)
    (hsuccess : (EvmAsm.Codegen.TxTypeDispatchSpec.teerTxTypeDispatch bs).1 =
      (0 : Word))
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hvalid0 : isValidByteAccess (regionBase + BitVec.ofNat 64 0) = true) :
    let lenW := BitVec.ofNat 64 bs.length
    cpsTripleWithin nIntrinsicSteps T ret TxIntrinsicStateGasSpec.fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (.x10 ↦ᵣ regionBase) **
        (.x11 ↦ᵣ lenW) **
        (.x12 ↦ᵣ outPtr) ** bytesRegion regionBase bs **
        (outPtr ↦ₘ oldOut) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x13 ** regOwn .x14 ** regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)))
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spVal) **
        stackFree spVal nIntrinsicStackDwords **
        (.x8 ↦ᵣ s0) ** (.x9 ↦ᵣ s1) **
        (.x18 ↦ᵣ s2) ** (.x19 ↦ᵣ s3) ** (.x20 ↦ᵣ s4) **
        (.x21 ↦ᵣ s5) ** (.x22 ↦ᵣ s6) **
        (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion regionBase bs **
        (outPtr ↦ₘ (BitVec.ofNat 64 pureIntrinsicStateGasSuccess)) **
        tisScratchOwn **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x11 ** regOwn .x12 ** regOwn .x13 ** regOwn .x14 **
        regOwn .x15 ** regOwn .x16 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word))) :=
  intrinsicAssumed_success_flat_off0_own asm hextract htype
    ret spVal regionBase outPtr oldOut s0 s1 s2 s3 s4 s5 s6 bs
    hret hlink hextractOk hsuccess halign hover hvalid0

#print axioms intrinsic_discharge_off0_available
#print axioms intrinsic_discharge_off0_own_available
#print axioms bgvOffsetAssumed_fullCode
#print axioms typeDispatchAssumed_fullCode

end EvmAsm.Codegen.BlockVerdictTxStateGasArrayCompose
