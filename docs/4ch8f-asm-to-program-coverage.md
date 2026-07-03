# 4ch8f.9 — asm-string → Program conversion coverage

_Regenerate with `python3 scripts/asm_to_program.py coverage` (requires `riscv64-unknown-elf-as`/`-objcopy`)._

**Multi-image constraint (wave .9.3).** A converted `*Function` string is emitted into N linked images — the monolithic `stateless_guest`, the `runtime_dispatcher`, and hundreds of `zisk_*` probe programs — each with a different `.text`/`.data` layout. `la`/cross-`jal` are therefore emitted **symbolically** (`emitProgramR` + a reloc side-table) so every image's linker relocates them itself; the per-function `Program` separately carries the **concrete** `stateless_guest`-linked immediates (`laHi`/`laLo`/`jalOff GuestAddrs.…`) as the verification view. Only the guest link pins that view; the emitted text stays byte-identical to the hand-written source in every image (checked per-function by assemble/link+`cmp` and by a probe-image execution check in CI).

Every `*Function : String` def under `EvmAsm/Codegen/Programs/` and `EvmAsm/Codegen/Dispatch.lean` is parsed to a `Program`, rendered back with `emitProgram`, and the render is assembled with `riscv64-unknown-elf-as` and byte-compared against the original hand-written text (`.text` of both). See `docs/4ch8f-asm-to-program.md` for the design and trust model.

## Summary

| Class | Count | Meaning |
|---|---:|---|
| BLOCKED_ON_.6 | 301 | References a `la <symbol>` or cross-function `jal <callee>` whose target symbol is NOT in the linker-facts address table (`scripts/asm-fixtures/symbol-addresses.tsv`) — typically a routine registered as a probe unit but not yet linked into the monolithic `stateless_guest`. Resolves once it is emitted into the guest and the table regenerated. |
| ALREADY-STRUCTURED | 248 | RHS is already `"label:\n" ++ emitProgram <prog>` — a landed conversion (this PR: 16) or a prior template splice (RlpWalk, *SAsm). |
| COMPOSITE | 139 | RHS is not a pure string literal (concatenates other defs / probe prologues / data sections) — not a standalone routine body. **No wave bead needed:** these resolve automatically as their component functions convert. |
| READY-WAVE3 | 90 | Parses to a `Program` using the wave-.9.3 `la`/cross-`jal` resolution. TWO views: the `Program` carries the CONCRETE guest-linked immediates (`laHi`/`laLo`/`jalOff GuestAddrs.…`) for verification, while the emitted string keeps `la`/`jal` SYMBOLIC via `emitProgramR` + a reloc side-table so EVERY linked image (guest, dispatcher, every `zisk_*` probe) relocates it for itself — byte-identical to the hand-written source in each image. Directly landable. |
| NEEDS-DOTWORD | 33 | Contains a raw pre-encoded `.4byte N` word — the ZisK accelerator `.CSRS`/`csrrs` pattern `emitInstr` renders as `.4byte`. Needs a word-literal `Instr` (or a `.4byte`→`.CSRS` decoder) to convert; deferred to a follow-up wave. |
| NEEDS-LI-EXPANSION | 28 | Contains an `li rd, C` with C outside 12-bit signed range; a faithful 4-byte-per-`Instr` Program must emit the explicit `lui`/`addiw`/… expansion as separate `Instr`s (follow-up wave). |
| CALLER-LOCAL-FRAGMENT | 8 | Branches/jumps to a `.L` label owned by the caller, or has no own entry label — no independent ABI; needs extraction into a status-returning callable first. |
| MULTI-ENTRY-BUNDLE | 4 | Defines secondary non-`.L` labels (e.g. `*_clear`/`*_append`/`*_record_nth`) that other files `jal` into as cross-function entry points; `emitProgram` keeps only the entry label, so converting would silently break the guest link (caught only by the whole-guest byte-identity gate). Needs a multi-entry ABI / the .6 layout. |
| **TOTAL** | **851** | |

## Landed in this PR (241)

| Function | File | Instrs |
|---|---|---:|
| `accessListCountFunction` | `EvmAsm/Codegen/Programs/TxExtract.lean` | 0 |
| `accountExtractBalanceFunction` | `EvmAsm/Codegen/Programs/AccountFieldExtract.lean` | 0 |
| `accountExtractNonceFunction` | `EvmAsm/Codegen/Programs/AccountFieldExtract.lean` | 0 |
| `b1SenderTableFindFunction` | `EvmAsm/Codegen/Programs/BlockVerdictSenderCounts.lean` | 0 |
| `bahU32leFunction` | `EvmAsm/Codegen/Programs/BlockAccessListHash.lean` | 0 |
| `bgvU32leFunction` | `EvmAsm/Codegen/Programs/BalGasValid.lean` | 0 |
| `bgvU64leFunction` | `EvmAsm/Codegen/Programs/BalGasValid.lean` | 0 |
| `bhrRevLeBeFunction` | `EvmAsm/Codegen/Programs/BlockHeaderSszToRlp.lean` | 0 |
| `blake2fLdLe64Function` | `EvmAsm/Codegen/Programs/Blake2f.lean` | 0 |
| `blake2fStLe64Function` | `EvmAsm/Codegen/Programs/Blake2f.lean` | 0 |
| `blockHashFromHeaderFunction` | `EvmAsm/Codegen/Programs/Header.lean` | 0 |
| `blockLogsBloomFromReceiptsListFunction` | `EvmAsm/Codegen/Programs/BloomBlock.lean` | 0 |
| `blockRlpRebuiltSizeFunction` | `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 0 |
| `blockValidateLogsBloomFunction` | `EvmAsm/Codegen/Programs/BloomBlock.lean` | 0 |
| `blockVerdictEip7702AuthNonstorageEffectsArrayFunction` | `EvmAsm/Codegen/Programs/TxIntrinsicStateGas.lean` | 0 |
| `blockVerdictTxStateGasArrayFunction` | `EvmAsm/Codegen/Programs/TxIntrinsicStateGas.lean` | 0 |
| `bloomAddValueFunction` | `EvmAsm/Codegen/Programs/BloomAddValue.lean` | 0 |
| `bloomEqFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `bloomOrIntoFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `bls12CopyQuadsFunction` | `EvmAsm/Codegen/Programs/Bls12Field.lean` | 0 |
| `bls12Fq12CopyFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12EqFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12IsZeroFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12PowFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12SetOneFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12ZeroFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12G1BeToLeFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1Copy96Function` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1Eq48Function` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1IsZeroFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1LeToBeFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1LtPFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1OnCurveFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1SubgroupFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1Zero96Function` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G2ChordTailFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2Copy192Function` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2EncodeFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2EqNFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2Fp2InvFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2FpInvFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2ScalarMulFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2SubgroupFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2Zero192Function` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12KzgFpPowQ14Function` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 0 |
| `bls12KzgG1WireFunction` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 0 |
| `bls12KzgG2WireFunction` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 0 |
| `bls12KzgLtBeFunction` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 0 |
| `bls12MapFp2PowFunction` | `EvmAsm/Codegen/Programs/Bls12Map.lean` | 0 |
| `bls12MapFpPowFunction` | `EvmAsm/Codegen/Programs/Bls12Map.lean` | 0 |
| `bls12PtCopyFunction` | `EvmAsm/Codegen/Programs/Bls12Pairing.lean` | 0 |
| `bn254CallAllotmentFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254FieldBeToLeFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldEq32Function` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldIsZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldLeToBeFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldLtPFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254Fp2CopyFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2EqFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2InvFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2IsZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2ZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254FpPowLeFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fq12CopyFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12EqFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12IsZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12PowFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12SetOneFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12ZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254OnCurveFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PointCopy64Function` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PointIsInfFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PointZero64Function` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PtCopyFunction` | `EvmAsm/Codegen/Programs/Bn254Pairing.lean` | 0 |
| `bn254ScalarMulFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254ValidateG1Function` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bytesToNibblesFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `calcExcessBlobGasFunction` | `EvmAsm/Codegen/Programs/Header.lean` | 0 |
| `callFrameSetCalldataFunction` | `EvmAsm/Codegen/Programs/CallFrameDescend.lean` | 0 |
| `calldataByteCountsFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `codesBlockhashRequiredHeadersFunction` | `EvmAsm/Codegen/Programs/BlockhashRequiredHeaders.lean` | 0 |
| `committedStorageChunkedSnapshotUpsertFunction` | `EvmAsm/Codegen/Programs/CommittedStorageSnapshot.lean` | 0 |
| `committedStorageSnapshotAppendFunction` | `EvmAsm/Codegen/Programs/CommittedStorageSnapshot.lean` | 0 |
| `committedStorageSnapshotUpsertFunction` | `EvmAsm/Codegen/Programs/CommittedStorageSnapshot.lean` | 0 |
| `copyWordGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `deriveChainIdFromVFunction` | `EvmAsm/Codegen/Programs/Tx.lean` | 0 |
| `deriveConsolidationRequestsFunction` | `EvmAsm/Codegen/Programs/SystemCallStaging.lean` | 0 |
| `deriveWithdrawalRequestsFunction` | `EvmAsm/Codegen/Programs/SystemCallStaging.lean` | 0 |
| `dispatcherCaptureExecStateGasFunction` | `EvmAsm/Codegen/Programs/DispatcherExecStateGas.lean` | 0 |
| `eip7702AuthorizationSigningHashFunction` | `EvmAsm/Codegen/Programs/TxSigningHash.lean` | 0 |
| `eip8037BlockGasUsedFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `enrgU32leFunction` | `EvmAsm/Codegen/Programs/Eip7702NonceReuseGuard.lean` | 0 |
| `ephU32leFunction` | `EvmAsm/Codegen/Programs/SszParentHeader.lean` | 0 |
| `execLogLatestValueFunction` | `EvmAsm/Codegen/Programs/ExecLogLatestValue.lean` | 0 |
| `expGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `extractParentHeaderAndStateRootFunction` | `EvmAsm/Codegen/Programs/SszParentHeader.lean` | 0 |
| `extractPayloadAndWithdrawalsFunction` | `EvmAsm/Codegen/Programs/SszPayloadWithdrawals.lean` | 0 |
| `extractWitnessStateSectionFunction` | `EvmAsm/Codegen/Programs/SszWitnessState.lean` | 0 |
| `findCodeEffectByAddressFunction` | `EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean` | 0 |
| `frameDepthPopFunction` | `EvmAsm/Codegen/Programs/CallFrameSwitch.lean` | 0 |
| `frameDepthPushFunction` | `EvmAsm/Codegen/Programs/CallFrameSwitch.lean` | 0 |
| `frameLoadRegsFunction` | `EvmAsm/Codegen/Programs/CallFrameSwitch.lean` | 0 |
| `frameSaveRegsFunction` | `EvmAsm/Codegen/Programs/CallFrameSwitch.lean` | 0 |
| `headerExtractLogsBloomFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `headerExtractNumberFunction` | `EvmAsm/Codegen/Programs/HeaderU64.lean` | 0 |
| `headersParentHashFunction` | `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 0 |
| `hpDecodeNibblesFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `hpEncodeNibblesFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `initCodeCostFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `intrinsicGasCalldataFloorEip7623Function` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `keccak256WordGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `logBloomAddFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `logDataGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `logsListBloomAddFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `memoryExpansionGasFunction` | `EvmAsm/Codegen/Programs/MemoryExpansionGas.lean` | 0 |
| `mptBranchChildFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `mptBranchPayloadTwoSlotsFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` | 0 |
| `mptCompactToNibblesFunction` | `EvmAsm/Codegen/Programs/MptNibbles.lean` | 0 |
| `mptDeleteAccFunction` | `EvmAsm/Codegen/Programs/MptDeleteAcc.lean` | 0 |
| `mptDeleteWalkDbFunction` | `EvmAsm/Codegen/Programs/MptDeleteWalkDb.lean` | 0 |
| `mptExtensionExtractFunction` | `EvmAsm/Codegen/Programs/MptInternal.lean` | 0 |
| `mptIndexedTrieRootLargeFunction` | `EvmAsm/Codegen/Programs/MptIndexedTrieRoot.lean` | 0 |
| `mptInsertAccFunction` | `EvmAsm/Codegen/Programs/MptInsertAcc.lean` | 0 |
| `mptInsertWalkDbFunction` | `EvmAsm/Codegen/Programs/MptInsertWalkDb.lean` | 0 |
| `mptLeafExtractFunction` | `EvmAsm/Codegen/Programs/MptInternal.lean` | 0 |
| `mptLookupByKeyFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `mptNibblesToCompactFunction` | `EvmAsm/Codegen/Programs/MptNibbles.lean` | 0 |
| `mptNodeKindFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `mptNodeSlotEncodeFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` | 0 |
| `mptOneLeafRootIndexedFunction` | `EvmAsm/Codegen/Programs/TxRoot.lean` | 0 |
| `mptSetAccFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 0 |
| `mptSetRecordWalkDbFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 0 |
| `mptSpliceSlotFunction` | `EvmAsm/Codegen/Programs/MptSet.lean` | 0 |
| `mptStateRootFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 0 |
| `mptStateRootInsFunction` | `EvmAsm/Codegen/Programs/MptStateRootIns.lean` | 0 |
| `mptWalkFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `msetMemcpyFunction` | `EvmAsm/Codegen/Programs/MptSet.lean` | 0 |
| `nibblesCommonPrefixLenFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` | 0 |
| `nodeDbAppendFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 0 |
| `nodeDbLookupFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 0 |
| `nonstorageEffectLatestBalanceFunction` | `EvmAsm/Codegen/Programs/NonstorageEffectLog.lean` | 0 |
| `p256BeToLeFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256ChordTailFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256CopyNFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256Eq32Function` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256IsZeroNFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256LeToBeFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256LtBeFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256PointAddFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256PointDblFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256PowFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256ScalarMulFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `parentHeaderMatchesWitnessFirstFunction` | `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 0 |
| `priorityFeePerGasEip1559Function` | `EvmAsm/Codegen/Programs/U256GasPricing.lean` | 0 |
| `receiptExtractLogsBloomFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `rlpBytesEncodedSizeFunction` | `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 0 |
| `rlpEncodeBytesFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpEncodeListPrefixFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpEncodeU64Function` | `EvmAsm/Codegen/Programs/Receipt.lean` | 0 |
| `rlpEncodeUintBeFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpFieldToU256BeFunction` | `EvmAsm/Codegen/Programs/Tx.lean` | 0 |
| `rlpFieldToU64Function` | `EvmAsm/Codegen/Programs/Tx.lean` | 0 |
| `rlpListCountItemsFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpListEncodedSizeFunction` | `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 0 |
| `rlpListNthItemFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpListTruncateToNFieldsFunction` | `EvmAsm/Codegen/Programs/TxSigningHash.lean` | 0 |
| `runningBloomCopyFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `runningBloomZeroFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `secp256k1FieldAddFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldBeToLeFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldCmpPFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldCopy32Function` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldEq32Function` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldGetBitFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldInvFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldIsZeroFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldLeToBeFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldPowFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldReduceOnceFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldSqrtFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldSquareFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldSubFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldZero32Function` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1PointCopy64Function` | `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 0 |
| `secp256k1PointZero64Function` | `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 0 |
| `secp256k1RecoverPubkeyStagedFunction` | `EvmAsm/Codegen/Programs/TxPubkey.lean` | 0 |
| `secp256k1RecoverRFunction` | `EvmAsm/Codegen/Programs/Secp256k1Recover.lean` | 0 |
| `secp256k1ScalarFieldAddFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1ScalarFieldInvFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1ScalarFieldPowFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1ScalarFieldReduceOnceFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1ScalarFieldSquareFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1ScalarMulFunction` | `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 0 |
| `senderPostNonceConsistentFunction` | `EvmAsm/Codegen/Programs/SenderPostNonceConsistent.lean` | 0 |
| `singleLeafTrieRootFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` | 0 |
| `slotDecodeU256Function` | `EvmAsm/Codegen/Programs/State.lean` | 0 |
| `slotTupleSequencesMatchFunction` | `EvmAsm/Codegen/Programs/SlotTupleSequencesMatch.lean` | 0 |
| `spwU32leFunction` | `EvmAsm/Codegen/Programs/SszPayloadWithdrawals.lean` | 0 |
| `sszHashTreeRootBytesFunction` | `EvmAsm/Codegen/Programs/Ssz.lean` | 0 |
| `sszMerkleizeFunction` | `EvmAsm/Codegen/Programs/Ssz.lean` | 0 |
| `sszMerkleizePow2Function` | `EvmAsm/Codegen/Programs/Ssz.lean` | 0 |
| `sszPackBytesFunction` | `EvmAsm/Codegen/Programs/Ssz.lean` | 0 |
| `sszTxListVersionedHashesMatchFunction` | `EvmAsm/Codegen/Programs/TxBlobGas.lean` | 0 |
| `sszWithdrawalToRlpFunction` | `EvmAsm/Codegen/Programs/SszWithdrawal.lean` | 0 |
| `swdMinimalCopyFunction` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swdReadU64leFunction` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swdWriteBe32U64Function` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swdWriteBe8Function` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swrRevLeBeFunction` | `EvmAsm/Codegen/Programs/SszWithdrawal.lean` | 0 |
| `swsU32leFunction` | `EvmAsm/Codegen/Programs/SszWitnessState.lean` | 0 |
| `txAccessListSpanFunction` | `EvmAsm/Codegen/Programs/SeedTxAccessList.lean` | 0 |
| `txEffectiveGasPricingFunction` | `EvmAsm/Codegen/Programs/TxExtract.lean` | 0 |
| `txEip1559DecodeFunction` | `EvmAsm/Codegen/Programs/TxDecode1559.lean` | 0 |
| `txEip2930DecodeFunction` | `EvmAsm/Codegen/Programs/TxDecode2930.lean` | 0 |
| `txEip4844DecodeFunction` | `EvmAsm/Codegen/Programs/TxDecode4844.lean` | 0 |
| `txEip4844ValidateBlobHashesFunction` | `EvmAsm/Codegen/Programs/TxBlobGas.lean` | 0 |
| `txEip7702DecodeFunction` | `EvmAsm/Codegen/Programs/TxDecode7702.lean` | 0 |
| `txGasResultIncrementsFunction` | `EvmAsm/Codegen/Programs/Account.lean` | 0 |
| `txGasSenderBalLookupFunction` | `EvmAsm/Codegen/Programs/TxGasSenderBalLookup.lean` | 0 |
| `txPubkeyEcrecoverStageMaterialFunction` | `EvmAsm/Codegen/Programs/TxPubkey.lean` | 0 |
| `txPubkeyPublicKeyMatchesFunction` | `EvmAsm/Codegen/Programs/TxPubkey.lean` | 0 |
| `txPubkeyRecoverRawFunction` | `EvmAsm/Codegen/Programs/TxPubkey.lean` | 0 |
| `txPubkeySignatureMaterialFunction` | `EvmAsm/Codegen/Programs/TxPubkey.lean` | 0 |
| `txRefundCapFunction` | `EvmAsm/Codegen/Programs/TxRefund.lean` | 0 |
| `txSigningHashFunction` | `EvmAsm/Codegen/Programs/TxSigningHash.lean` | 0 |
| `txSigningHashLegacyEip155Function` | `EvmAsm/Codegen/Programs/TxSigningHash.lean` | 0 |
| `txTypeDispatchFunction` | `EvmAsm/Codegen/Programs/TxExtract.lean` | 0 |
| `txValidateAgainstBlockFunction` | `EvmAsm/Codegen/Programs/Tx.lean` | 0 |
| `u256AddBeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256DivU64BeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256EqFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256FromU64BeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256IsZeroFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256LtBeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256MaxFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256MinFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256MulU64BeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256SubBeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256ToU64BeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `validateHeaderBasicFunction` | `EvmAsm/Codegen/Programs/Header.lean` | 0 |
| `witnessCodesValidateLengthsFunction` | `EvmAsm/Codegen/Programs/WitnessValidation.lean` | 0 |

## READY-WAVE3 (90)

| Function | File | Instrs | Note |
|---|---|---:|---|
| `createExecuteInitcodeFrameRuntimeFunction` | `EvmAsm/Codegen/Dispatch.lean` | 193 | 8 reloc sym(s) |
| `createStageInitcodeFrameRuntimeFunction` | `EvmAsm/Codegen/Dispatch.lean` | 70 | 13 reloc sym(s) |
| `accountChargeGasPreExecFunction` | `EvmAsm/Codegen/Programs/Account.lean` | 31 | 3 reloc sym(s) |
| `txUpfrontPrechargeFunction` | `EvmAsm/Codegen/Programs/Account.lean` | 77 | 7 reloc sym(s) |
| `accountApplyStorageSlotAccFunction` | `EvmAsm/Codegen/Programs/AccountApplyStorage.lean` | 203 | 23 reloc sym(s) |
| `accountApplyStorageSlotFunction` | `EvmAsm/Codegen/Programs/AccountApplyStorage.lean` | 74 | 7 reloc sym(s) |
| `accountAddBalanceFunction` | `EvmAsm/Codegen/Programs/AccountBalance.lean` | 108 | 8 reloc sym(s) |
| `accountSetUintFieldFunction` | `EvmAsm/Codegen/Programs/AccountBalance.lean` | 49 | 4 reloc sym(s) |
| `selfdestructBalanceTransferFunction` | `EvmAsm/Codegen/Programs/AccountBalance.lean` | 108 | 6 reloc sym(s) |
| `codeHashAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/AccountFieldGetters.lean` | 76 | 5 reloc sym(s) |
| `accountIsEip161EmptyFunction` | `EvmAsm/Codegen/Programs/AccountFields.lean` | 108 | 4 reloc sym(s) |
| `addressComputeCreate2Function` | `EvmAsm/Codegen/Programs/Address.lean` | 65 | 4 reloc sym(s) |
| `addressComputeCreateFunction` | `EvmAsm/Codegen/Programs/Address.lean` | 89 | 4 reloc sym(s) |
| `addressFromPubkeyFunction` | `EvmAsm/Codegen/Programs/Address.lean` | 21 | 2 reloc sym(s) |
| `requestsHashVerifyFunction` | `EvmAsm/Codegen/Programs/AssembleExecutionRequests.lean` | 36 | 3 reloc sym(s) |
| `balAccountAccessOutcomeDescriptorsFunction` | `EvmAsm/Codegen/Programs/BalAccountAccessDescriptors.lean` | 109 | 4 reloc sym(s) |
| `baapDeleteSingleLeafStorageFunction` | `EvmAsm/Codegen/Programs/BalAccountApplyPostFields.lean` | 137 | 20 reloc sym(s) |
| `balAccountChangeDescriptorFunction` | `EvmAsm/Codegen/Programs/BalAccountChangeDescriptor.lean` | 79 | 6 reloc sym(s) |
| `balAccountChangeValueFunction` | `EvmAsm/Codegen/Programs/BalAccountChangeValue.lean` | 54 | 3 reloc sym(s) |
| `balAccountCodeConsistentFunction` | `EvmAsm/Codegen/Programs/BalAccountCodeConsistent.lean` | 43 | 2 reloc sym(s) |
| `balAccountHasStateChangeFunction` | `EvmAsm/Codegen/Programs/BalAccountHasStateChange.lean` | 49 | 2 reloc sym(s) |
| `balAccountNonstorageConsistentFunction` | `EvmAsm/Codegen/Programs/BalAccountNonstorageConsistent.lean` | 63 | 2 reloc sym(s) |
| `balAccountNonstorageFinalsFunction` | `EvmAsm/Codegen/Programs/BalAccountNonstorageFinals.lean` | 192 | 4 reloc sym(s) |
| `balAccountPathFunction` | `EvmAsm/Codegen/Programs/BalAccountPath.lean` | 30 | 5 reloc sym(s) |
| `balAccountPostFieldsFunction` | `EvmAsm/Codegen/Programs/BalAccountPostFields.lean` | 157 | 2 reloc sym(s) |
| `balAccountRecordArrayFunction` | `EvmAsm/Codegen/Programs/BalAccountRecordArray.lean` | 156 | 14 reloc sym(s) |
| `balAllAccountsCodeConsistentFunction` | `EvmAsm/Codegen/Programs/BalAllAccountsCode.lean` | 81 | 3 reloc sym(s) |
| `balAllAccountsCodeCoversFunction` | `EvmAsm/Codegen/Programs/BalAllAccountsCodeCovers.lean` | 75 | 2 reloc sym(s) |
| `balAllAccountsNonstorageCoversFunction` | `EvmAsm/Codegen/Programs/BalAllAccountsNonstorageCovers.lean` | 144 | 3 reloc sym(s) |
| `balGasValidFunction` | `EvmAsm/Codegen/Programs/BalGasValid.lean` | 106 | 2 reloc sym(s) |
| `balSectionInfoFunction` | `EvmAsm/Codegen/Programs/BalGasValid.lean` | 53 | 3 reloc sym(s) |
| `balAccountIsModeledSystemFunction` | `EvmAsm/Codegen/Programs/BalModeledSystem.lean` | 50 | 5 reloc sym(s) |
| `balStorageAccessOutcomeDescriptorsFunction` | `EvmAsm/Codegen/Programs/BalStorageAccessDescriptors.lean` | 125 | 4 reloc sym(s) |
| `blockAccessListHashFunction` | `EvmAsm/Codegen/Programs/BlockAccessListHash.lean` | 33 | 3 reloc sym(s) |
| `eip7778RemainingBlockGasFromResultsFunction` | `EvmAsm/Codegen/Programs/BlockGasRemaining.lean` | 59 | 2 reloc sym(s) |
| `blockhashFromWitnessHeadersFunction` | `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 77 | 3 reloc sym(s) |
| `balFindAccountByAddressFunction` | `EvmAsm/Codegen/Programs/BlockVerdictBalFindAccount.lean` | 77 | 3 reloc sym(s) |
| `blockVerdictGasResultArenaPrepareFunction` | `EvmAsm/Codegen/Programs/BlockVerdictGasResults.lean` | 155 | 15 reloc sym(s) |
| `blockVerdictTxGasLimitsFunction` | `EvmAsm/Codegen/Programs/BlockVerdictGasResults.lean` | 160 | 10 reloc sym(s) |
| `bsrApplyModeledSystemPostFieldsFunction` | `EvmAsm/Codegen/Programs/BlockVerdictModeledSystem.lean` | 92 | 12 reloc sym(s) |
| `simpleTransferTxContextFunction` | `EvmAsm/Codegen/Programs/BlockVerdictSimpleTransfer.lean` | 168 | 16 reloc sym(s) |
| `bsrBeaconChangeFunction` | `EvmAsm/Codegen/Programs/BlockVerdictSysChange.lean` | 429 | 42 reloc sym(s) |
| `bsrSysChangeFunction` | `EvmAsm/Codegen/Programs/BlockVerdictSysChange.lean` | 109 | 17 reloc sym(s) |
| `btiScanStorageChangesFunction` | `EvmAsm/Codegen/Programs/BlockVerdictTxsIndependent.lean` | 48 | 4 reloc sym(s) |
| `chainValidateConsecutiveNumbersFunction` | `EvmAsm/Codegen/Programs/ChainValidate.lean` | 93 | 5 reloc sym(s) |
| `chainValidateExtraDataLengthFunction` | `EvmAsm/Codegen/Programs/ChainValidate.lean` | 69 | 5 reloc sym(s) |
| `chainValidateGasUsedUnderLimitFunction` | `EvmAsm/Codegen/Programs/ChainValidate.lean` | 83 | 5 reloc sym(s) |
| `chainValidateIncreasingTimestampsFunction` | `EvmAsm/Codegen/Programs/ChainValidate.lean` | 92 | 5 reloc sym(s) |
| `chainValidatePostMergeFullFunction` | `EvmAsm/Codegen/Programs/ChainValidatePostMerge.lean` | 149 | 8 reloc sym(s) |
| `committedStorageChunkedLatestValueFunction` | `EvmAsm/Codegen/Programs/CommittedStorageLookup.lean` | 48 | 1 reloc sym(s) |
| `committedStorageLatestValueFunction` | `EvmAsm/Codegen/Programs/CommittedStorageLookup.lean` | 48 | 1 reloc sym(s) |
| `eip7702AuthorizationRecoverAddressFunction` | `EvmAsm/Codegen/Programs/Eip7702Authority.lean` | 101 | 10 reloc sym(s) |
| `eip7702NonceReuseGuardFunction` | `EvmAsm/Codegen/Programs/Eip7702NonceReuseGuard.lean` | 296 | 30 reloc sym(s) |
| `hasCodeOrNonceAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/EvmCodes.lean` | 86 | 7 reloc sym(s) |
| `nonceAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/EvmNonce.lean` | 53 | 4 reloc sym(s) |
| `extcodehashAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/EvmOpcodes.lean` | 88 | 5 reloc sym(s) |
| `headerValidateExtraDataLengthFunction` | `EvmAsm/Codegen/Programs/Header.lean` | 22 | 3 reloc sym(s) |
| `headerValidatePostMergeFunction` | `EvmAsm/Codegen/Programs/Header.lean` | 85 | 4 reloc sym(s) |
| `eip1559CalcBaseFeePerGasFunction` | `EvmAsm/Codegen/Programs/HeaderBaseFee.lean` | 77 | 6 reloc sym(s) |
| `headerValidateBaseFeeFunction` | `EvmAsm/Codegen/Programs/HeaderBaseFee.lean` | 25 | 3 reloc sym(s) |
| `validateHeaderFullFunction` | `EvmAsm/Codegen/Programs/HeaderBaseFee.lean` | 62 | 6 reloc sym(s) |
| `validateParentHashLinkFunction` | `EvmAsm/Codegen/Programs/HeaderChain.lean` | 80 | 6 reloc sym(s) |
| `headerExtendedDecodeFunction` | `EvmAsm/Codegen/Programs/HeaderDecode.lean` | 174 | 4 reloc sym(s) |
| `headerExtractReceiptsRootFunction` | `EvmAsm/Codegen/Programs/HeaderFields.lean` | 45 | 3 reloc sym(s) |
| `headerExtractStateRootFunction` | `EvmAsm/Codegen/Programs/HeaderFields.lean` | 45 | 3 reloc sym(s) |
| `headerExtractWithdrawalsRootFunction` | `EvmAsm/Codegen/Programs/HeaderFields.lean` | 45 | 3 reloc sym(s) |
| `headerValidateParentHashFunction` | `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 43 | 4 reloc sym(s) |
| `headersKeccakArrayFunction` | `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 43 | 1 reloc sym(s) |
| `headersValidateChainFunction` | `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 75 | 4 reloc sym(s) |
| `blockVerdictEip8037TxStateGasNetArrayFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 54 | 1 reloc sym(s) |
| `receiptEncodeFunction` | `EvmAsm/Codegen/Programs/Receipt.lean` | 117 | 7 reloc sym(s) |
| `blockValidateReceiptsRootIndexedFunction` | `EvmAsm/Codegen/Programs/ReceiptsRootIndexed.lean` | 55 | 4 reloc sym(s) |
| `runtimeSameBlockDelegationCodeFunction` | `EvmAsm/Codegen/Programs/RuntimeSameBlockCode.lean` | 187 | 17 reloc sym(s) |
| `accountAtAddressFunction` | `EvmAsm/Codegen/Programs/State.lean` | 59 | 4 reloc sym(s) |
| `accountDecodeFunction` | `EvmAsm/Codegen/Programs/State.lean` | 136 | 3 reloc sym(s) |
| `slotAtIndexFunction` | `EvmAsm/Codegen/Programs/State.lean` | 38 | 4 reloc sym(s) |
| `accountAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/StateCompose.lean` | 57 | 3 reloc sym(s) |
| `codeAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/StateCompose.lean` | 59 | 7 reloc sym(s) |
| `extcodesizeAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/StateCompose.lean` | 84 | 8 reloc sym(s) |
| `slotAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/StateCompose.lean` | 64 | 6 reloc sym(s) |
| `accountExistsAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/StatePredicates.lean` | 54 | 5 reloc sym(s) |
| `accountIsEmptyAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/StatePredicates.lean` | 80 | 6 reloc sym(s) |
| `step2VerdictFunction` | `EvmAsm/Codegen/Programs/Step2Verdict.lean` | 59 | 6 reloc sym(s) |
| `accountSetStorageRootFunction` | `EvmAsm/Codegen/Programs/StorageWrite.lean` | 43 | 2 reloc sym(s) |
| `storageRootSingleSlotFunction` | `EvmAsm/Codegen/Programs/StorageWrite.lean` | 40 | 6 reloc sym(s) |
| `validateHeaderRlpPairFunction` | `EvmAsm/Codegen/Programs/ValidateHeaderPair.lean` | 46 | 5 reloc sym(s) |
| `verifyPublicKeysMatchSendersFunction` | `EvmAsm/Codegen/Programs/VerifyPublicKeysSenders.lean` | 77 | 8 reloc sym(s) |
| `withdrawalDecodeFunction` | `EvmAsm/Codegen/Programs/Withdrawal.lean` | 60 | 4 reloc sym(s) |
| `blockValidateWithdrawalsRootIndexedFunction` | `EvmAsm/Codegen/Programs/WithdrawalsRootIndexed.lean` | 55 | 4 reloc sym(s) |
| `withdrawalsStateRootFunction` | `EvmAsm/Codegen/Programs/WithdrawalsStateRoot.lean` | 102 | 11 reloc sym(s) |

## CONVERTED-CLEAN (0)

| Function | File | Instrs | Note |
|---|---|---:|---|

## NEEDS-LI-EXPANSION (28)

| Function | File | Instrs | Note |
|---|---|---:|---|
| `dispatcherTxGasSettleFunction` | `EvmAsm/Codegen/Dispatch.lean` |  | li 0xa0010000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `frameBaseFunction` | `EvmAsm/Codegen/Programs/CallFrameBase.lean` |  | li 0x29000: constant needs multi-instruction expansion (NEEDS-LI-EXPAN |
| `chainValidateBlobGasUsedMultipleFunction` | `EvmAsm/Codegen/Programs/ChainValidateBlob.lean` |  | li 0x1ffff: constant needs multi-instruction expansion (NEEDS-LI-EXPAN |
| `chainValidateBlobGasUsedUnderMaxFunction` | `EvmAsm/Codegen/Programs/ChainValidateBlob.lean` |  | li 2752512: constant needs multi-instruction expansion (NEEDS-LI-EXPAN |
| `eip2935BlockhashLookupFunction` | `EvmAsm/Codegen/Programs/Eip2935.lean` |  | li 8191: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `eip4788BeaconRootLookupFunction` | `EvmAsm/Codegen/Programs/Eip4788.lean` |  | li 8191: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `messageCallGasFunction` | `EvmAsm/Codegen/Programs/EvmMessageCallGas.lean` |  | li 2300: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `extcodecopyAtHeaderStateRootFunction` | `EvmAsm/Codegen/Programs/EvmOpcodesExtcodecopy.lean` |  | li 32768: constant needs multi-instruction expansion (NEEDS-LI-EXPANSI |
| `amsterdamBlobGasPriceFunction` | `EvmAsm/Codegen/Programs/Header.lean` |  | li 11684671: constant needs multi-instruction expansion (NEEDS-LI-EXPA |
| `amsterdamBlobGasPriceU256Function` | `EvmAsm/Codegen/Programs/Header.lean` |  | li 11684671: constant needs multi-instruction expansion (NEEDS-LI-EXPA |
| `checkGasLimitFunction` | `EvmAsm/Codegen/Programs/Header.lean` |  | li 5000: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `headerValidateExcessBlobGasFunction` | `EvmAsm/Codegen/Programs/HeaderBaseFee.lean` |  | li 1835008: constant needs multi-instruction expansion (NEEDS-LI-EXPAN |
| `eip8037ReservoirSplitFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` |  | li 16777216: constant needs multi-instruction expansion (NEEDS-LI-EXPA |
| `intrinsicGasAmsterdamCountsFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` |  | li 21000: constant needs multi-instruction expansion (NEEDS-LI-EXPANSI |
| `mptBranchNodeEncodeFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` |  | li 0xa0000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `mptExtensionNodeEncodeFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` |  | li 0xa0000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `mptLeafNodeEncodeFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` |  | li 0xa0000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `mptIndexedTrieRootSmallFunction` | `EvmAsm/Codegen/Programs/MptIndexedTrieRoot.lean` |  | li 2049: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `mptNodeResolveFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` |  | li 4095: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `mptResolveCacheResetFunction` | `EvmAsm/Codegen/Programs/MptSetAcc.lean` |  | li 4096: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `sszHashTreeRootListByteListFunction` | `EvmAsm/Codegen/Programs/Ssz.lean` |  | li 4096: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `bvSumWithdrawalsToAddressFunction` | `EvmAsm/Codegen/Programs/SszWithdrawal.lean` |  | li 1000000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `statelessVerdictFromSszFunction` | `EvmAsm/Codegen/Programs/StatelessVerdict.lean` |  | li 0x40000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `systemWriteDescriptorsFunction` | `EvmAsm/Codegen/Programs/SystemWrites.lean` |  | li 8191: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `intrinsicGasLegacyFunction` | `EvmAsm/Codegen/Programs/Tx.lean` |  | li 21000: constant needs multi-instruction expansion (NEEDS-LI-EXPANSI |
| `validateTransactionBasicFunction` | `EvmAsm/Codegen/Programs/Tx.lean` |  | li 0xffffffff: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `processWithdrawalFunction` | `EvmAsm/Codegen/Programs/Withdrawal.lean` |  | li 1000000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `withdrawalToPathDeltaFunction` | `EvmAsm/Codegen/Programs/WithdrawalPath.lean` |  | li 1000000000: constant needs multi-instruction expansion (NEEDS-LI-EX |

## NEEDS-CALL-EXPANSION (0)

| Function | File | Instrs | Note |
|---|---|---:|---|

## NEEDS-DOTWORD (33)

| Function | File | Instrs | Note |
|---|---|---:|---|
| `bls12FpAddFunction` | `EvmAsm/Codegen/Programs/Bls12Field.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12FpMulFunction` | `EvmAsm/Codegen/Programs/Bls12Field.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12Fq12SMulFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G1AddModPFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G1LeAddFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G1LeDblFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G1MulModPFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G1PointAddFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G1PointDblFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G2Fp2AddFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G2Fp2MulFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G2Fp2SubFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G2FpAddLeFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12G2FpMulLeFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bls12KzgNegScalarFunction` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254PointAddFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254PointDblFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254FieldAddFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254FieldMulFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254Fp2AddFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254Fp2MulFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254Fp2SubFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254FpAddLeFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254FpMulLeFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `bn254Fq12SMulFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `zkvmKeccak256Function` | `EvmAsm/Codegen/Programs/HashBridge.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `zkvmKeccak256SegmentsFunction` | `EvmAsm/Codegen/Programs/HashBridge.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `zkvmSha256Function` | `EvmAsm/Codegen/Programs/HashBridge.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `mptIndexedLargeLeafHashFunction` | `EvmAsm/Codegen/Programs/MptIndexedTrieRoot.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `p256OpWithFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `secp256k1PointDoubleFunction` | `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `secp256k1FieldMulFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |
| `secp256k1ScalarFieldMulFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` |  | .4byte: raw pre-encoded word (NEEDS-DOTWORD) |

## CALLER-LOCAL-FRAGMENT (8)

| Function | File | Instrs | Note |
|---|---|---:|---|
| `zkvmBls12G1AddRealFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | first line is not a label |
| `zkvmBls12G1MsmRealFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` |  | first line is not a label |
| `zkvmBls12G2AddRealFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | first line is not a label |
| `zkvmBls12G2MsmRealFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` |  | first line is not a label |
| `zkvmBls12MapFp2ToG2RealFunction` | `EvmAsm/Codegen/Programs/Bls12MapG2Real.lean` |  | first line is not a label |
| `zkvmBn254G1AddRealFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` |  | first line is not a label |
| `zkvmBn254G1MulRealFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` |  | first line is not a label |
| `runtimeAccessAccountSeedFunction` | `EvmAsm/Codegen/Programs/EvmAccessGas.lean` |  | unresolved branch/jump target '.exit_outofgas' |

## MULTI-ENTRY-BUNDLE (4)

| Function | File | Instrs | Note |
|---|---|---:|---|
| `blockValidateEmptyBlockFunction` | `EvmAsm/Codegen/Programs/BlockEmpty.lean` |  | secondary non-.L label 'beb_check_header_field_32B': multi-entry bundl |
| `mptIndexedTrieRootOneLeafFunction` | `EvmAsm/Codegen/Programs/MptIndexedTrieRoot.lean` |  | secondary non-.L label 'rlp_prefix_to_buffer': multi-entry bundle, cro |
| `receiptRecordsFunction` | `EvmAsm/Codegen/Programs/ReceiptRecords.lean` |  | secondary non-.L label 'receipt_records_clear': multi-entry bundle, cr |
| `storageEffectRecordsFunction` | `EvmAsm/Codegen/Programs/StorageEffectRecords.lean` |  | secondary non-.L label 'storage_effect_records_clear': multi-entry bun |

## BLOCKED_ON_.6 (301) — by file

| File | Count |
|---|---:|
| `EvmAsm/Codegen/Programs/Account.lean` | 7 |
| `EvmAsm/Codegen/Programs/AccountExistsAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountExistsAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountFields.lean` | 8 |
| `EvmAsm/Codegen/Programs/AccountIsEmptyAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountIsEmptyAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountStorageWalkable.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/B3CoinbaseFee.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountDescriptorArray.lean` | 2 |
| `EvmAsm/Codegen/Programs/BalAccountNthDescriptor.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountStateRoot.lean` | 2 |
| `EvmAsm/Codegen/Programs/BalanceAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalanceAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/BaseFeePerGasAtBlockHash.lean` | 2 |
| `EvmAsm/Codegen/Programs/BaseFeePerGasAtBlockNumber.lean` | 2 |
| `EvmAsm/Codegen/Programs/BeneficiaryAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BeneficiaryAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlobGasPairAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlobGasUsedAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlobGasUsedAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Block.lean` | 6 |
| `EvmAsm/Codegen/Programs/BlockBody.lean` | 6 |
| `EvmAsm/Codegen/Programs/BlockEmpty.lean` | 3 |
| `EvmAsm/Codegen/Programs/BlockHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashAtStateRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 5 |
| `EvmAsm/Codegen/Programs/BlockHashWindow.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockNumberAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockNumberAtStateRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockRoots.lean` | 4 |
| `EvmAsm/Codegen/Programs/BlockRootsAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockValidate.lean` | 5 |
| `EvmAsm/Codegen/Programs/BlockValidate1Tx.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bloom.lean` | 1 |
| `EvmAsm/Codegen/Programs/Chain.lean` | 11 |
| `EvmAsm/Codegen/Programs/ChainAggregator.lean` | 5 |
| `EvmAsm/Codegen/Programs/ChainBasefee.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainBlobCount.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainEndpoints.lean` | 9 |
| `EvmAsm/Codegen/Programs/ChainExcessBlobGas.lean` | 3 |
| `EvmAsm/Codegen/Programs/ChainLinkExtract.lean` | 1 |
| `EvmAsm/Codegen/Programs/ChainLinkParentKeccak.lean` | 1 |
| `EvmAsm/Codegen/Programs/ChainTimestamp.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainValidate.lean` | 6 |
| `EvmAsm/Codegen/Programs/ChainValidateBlob.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainValidatePostMerge.lean` | 3 |
| `EvmAsm/Codegen/Programs/ChainWalkNStepsBack.lean` | 1 |
| `EvmAsm/Codegen/Programs/ChainWalkOneStepBack.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeAtStateRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeHashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/DifficultyAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/DifficultyAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmOpcodes.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmOpcodesStorageRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExcessBlobGasAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExcessBlobGasAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtcodecopyAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtcodecopyAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtcodehashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtcodehashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtcodesizeAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtcodesizeAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtraDataAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtraDataAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/GasLimitAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/GasLimitAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/GasPairAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/GasUsedAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/GasUsedAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/HasCodeOrNonceAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/HasCodeOrNonceAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Header.lean` | 4 |
| `EvmAsm/Codegen/Programs/HeaderChain.lean` | 4 |
| `EvmAsm/Codegen/Programs/HeaderChainPostMerge.lean` | 3 |
| `EvmAsm/Codegen/Programs/HeaderDecode.lean` | 2 |
| `EvmAsm/Codegen/Programs/HeaderFields.lean` | 9 |
| `EvmAsm/Codegen/Programs/HeaderGasExtract.lean` | 2 |
| `EvmAsm/Codegen/Programs/HeaderGasLimits.lean` | 5 |
| `EvmAsm/Codegen/Programs/HeaderNonceAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeaderNonceAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeaderSummaryStruct.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeaderU64.lean` | 8 |
| `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 2 |
| `EvmAsm/Codegen/Programs/LogsBloomKeccakAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/LogsBloomKeccakAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Mpt.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptEncodeLeafBranch.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsert.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsertWalk.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInternal.lean` | 6 |
| `EvmAsm/Codegen/Programs/MptSet.lean` | 2 |
| `EvmAsm/Codegen/Programs/NonceAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/NonceAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/NumberTimestampPairAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/OmmersHashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/OmmersHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentBeaconBlockRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentBeaconBlockRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentHashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/PostMergeInvariantsAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/PrevRandaoAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/PrevRandaoAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Receipt.lean` | 1 |
| `EvmAsm/Codegen/Programs/ReceiptsRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ReceiptsRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/SelfdestructDescriptors.lean` | 2 |
| `EvmAsm/Codegen/Programs/SloadAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/SloadAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Ssz.lean` | 1 |
| `EvmAsm/Codegen/Programs/State.lean` | 2 |
| `EvmAsm/Codegen/Programs/StateAccountAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateAccountAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateAccountSpecDefault.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateBalanceProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateCodeHashProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateCompose.lean` | 2 |
| `EvmAsm/Codegen/Programs/StateExtractBalance.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateExtractCodeHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateExtractNonce.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateExtractStorageRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateNonceProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateRootChainWalkBack.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateRootInWitness.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateRootPresentInWitnessState.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateSlotAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateSlotAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateStorageProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateStorageRootProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateWalkExtractSlot.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageCompose.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRootInWitness.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/TimestampAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/TimestampAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/TransactionsRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/TransactionsRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Tx.lean` | 6 |
| `EvmAsm/Codegen/Programs/TxBlobGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxRoot.lean` | 3 |
| `EvmAsm/Codegen/Programs/TxTotalBlobGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/U256GasPricing.lean` | 1 |
| `EvmAsm/Codegen/Programs/Withdrawal.lean` | 5 |
| `EvmAsm/Codegen/Programs/WithdrawalBlockSummary.lean` | 2 |
| `EvmAsm/Codegen/Programs/WithdrawalsRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/WithdrawalsRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessCodesKeccakAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersAccountAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersAllChainLinksValidate.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersBlockHashAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersChainLink.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersFindIndexByBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersSlotAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessHeadersStateRootAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessNodeKindDistribution.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessStateKeccakAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessStorageKeccakAtIndex.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessStorageNodeKindDistribution.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessValidation.lean` | 2 |

## ALREADY-STRUCTURED (248) — by file

| File | Count |
|---|---:|
| `EvmAsm/Codegen/Programs/Account.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountFieldExtract.lean` | 2 |
| `EvmAsm/Codegen/Programs/BalGasValid.lean` | 2 |
| `EvmAsm/Codegen/Programs/Blake2f.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockAccessListHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHeaderSszToRlp.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 3 |
| `EvmAsm/Codegen/Programs/BlockVerdictSenderCounts.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockhashRequiredHeaders.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bloom.lean` | 8 |
| `EvmAsm/Codegen/Programs/BloomAddValue.lean` | 1 |
| `EvmAsm/Codegen/Programs/BloomBlock.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Field.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 6 |
| `EvmAsm/Codegen/Programs/Bls12G1.lean` | 9 |
| `EvmAsm/Codegen/Programs/Bls12G2.lean` | 9 |
| `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bls12Map.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Pairing.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 7 |
| `EvmAsm/Codegen/Programs/Bn254Field.lean` | 5 |
| `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 6 |
| `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 6 |
| `EvmAsm/Codegen/Programs/Bn254Pairing.lean` | 1 |
| `EvmAsm/Codegen/Programs/CallFrameDescend.lean` | 1 |
| `EvmAsm/Codegen/Programs/CallFrameSwitch.lean` | 4 |
| `EvmAsm/Codegen/Programs/CommittedStorageSnapshot.lean` | 3 |
| `EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateDeployedCodeValid.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateInitcodeSizeValid.lean` | 1 |
| `EvmAsm/Codegen/Programs/DispatcherExecStateGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 4 |
| `EvmAsm/Codegen/Programs/Eip7702NonceReuseGuard.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExecLogLatestValue.lean` | 1 |
| `EvmAsm/Codegen/Programs/Header.lean` | 3 |
| `EvmAsm/Codegen/Programs/HeaderU64.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 1 |
| `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 4 |
| `EvmAsm/Codegen/Programs/MemoryExpansionGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/Mpt.lean` | 7 |
| `EvmAsm/Codegen/Programs/MptDeleteAcc.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptDeleteWalkDb.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptEncode.lean` | 4 |
| `EvmAsm/Codegen/Programs/MptIndexedTrieRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsertAcc.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsertWalkDb.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInternal.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptNibbles.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptSet.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 5 |
| `EvmAsm/Codegen/Programs/MptStateRootIns.lean` | 1 |
| `EvmAsm/Codegen/Programs/NonstorageEffectLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/P256Verify.lean` | 11 |
| `EvmAsm/Codegen/Programs/Receipt.lean` | 1 |
| `EvmAsm/Codegen/Programs/RlpRead.lean` | 5 |
| `EvmAsm/Codegen/Programs/RlpWalk.lean` | 5 |
| `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 3 |
| `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 20 |
| `EvmAsm/Codegen/Programs/Secp256k1Recover.lean` | 1 |
| `EvmAsm/Codegen/Programs/SeedTxAccessList.lean` | 1 |
| `EvmAsm/Codegen/Programs/SenderPostNonceConsistent.lean` | 1 |
| `EvmAsm/Codegen/Programs/SlotTupleSequencesMatch.lean` | 1 |
| `EvmAsm/Codegen/Programs/Ssz.lean` | 4 |
| `EvmAsm/Codegen/Programs/SszParentHeader.lean` | 2 |
| `EvmAsm/Codegen/Programs/SszPayloadWithdrawals.lean` | 2 |
| `EvmAsm/Codegen/Programs/SszWithdrawal.lean` | 2 |
| `EvmAsm/Codegen/Programs/SszWitnessState.lean` | 2 |
| `EvmAsm/Codegen/Programs/State.lean` | 1 |
| `EvmAsm/Codegen/Programs/SystemCallStaging.lean` | 2 |
| `EvmAsm/Codegen/Programs/SystemWrites.lean` | 4 |
| `EvmAsm/Codegen/Programs/Tx.lean` | 4 |
| `EvmAsm/Codegen/Programs/TxBlobGas.lean` | 2 |
| `EvmAsm/Codegen/Programs/TxDecode1559.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode2930.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode4844.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode7702.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxExtract.lean` | 3 |
| `EvmAsm/Codegen/Programs/TxGasSenderBalLookup.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxIntrinsicStateGas.lean` | 2 |
| `EvmAsm/Codegen/Programs/TxPubkey.lean` | 5 |
| `EvmAsm/Codegen/Programs/TxRefund.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxSigningHash.lean` | 4 |
| `EvmAsm/Codegen/Programs/U256.lean` | 11 |
| `EvmAsm/Codegen/Programs/U256GasPricing.lean` | 1 |
| `EvmAsm/Codegen/Programs/WitnessValidation.lean` | 1 |

## COMPOSITE (139) — by file

| File | Count |
|---|---:|
| `EvmAsm/Codegen/Programs/AccountTupleSequencesConsistent.lean` | 1 |
| `EvmAsm/Codegen/Programs/AssembleExecutionRequests.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountApplyPostFields.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAddrExecLogKey.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAllAccountsNonstorage.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAllAccountsStorage.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAllAccountsTupleSequences.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalCodePreimages.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalSlotTupleSequence.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalStorageChangeValues.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalStorageCoversExecLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalStorageMatchesExecLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalStorageReadsExecLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/Blake2f.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockGasRemaining.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHeaderSszToRlp.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictChainConfig.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictContractStage.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictContractStorage.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictCreationStage.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictDispatchTx.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictFunction.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictGasGate.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictMultiTx.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictReceiptRecords.lean` | 3 |
| `EvmAsm/Codegen/Programs/BlockVerdictRecipientCredits.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictRuntimePayload.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictSelfContained.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictSenderCounts.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictSingleTxLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictStateRoot.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictSystemStorageCapture.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictTxsIndependent.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bls12G1.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12G2.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12MapG1Real.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bls12Pairing.lean` | 5 |
| `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bn254Fq12Point.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bn254Pairing.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bn254PairingCore.lean` | 3 |
| `EvmAsm/Codegen/Programs/CallFrameDescend.lean` | 4 |
| `EvmAsm/Codegen/Programs/CallFrameReturn.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateCreatorNonce.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateDescend.lean` | 2 |
| `EvmAsm/Codegen/Programs/CreateFrameDescend.lean` | 1 |
| `EvmAsm/Codegen/Programs/Eip7702Authority.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmAccessGas.lean` | 3 |
| `EvmAsm/Codegen/Programs/EvmMessageCallGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmOpcodes.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmStorageAccessGas.lean` | 2 |
| `EvmAsm/Codegen/Programs/ExecLogSlotTuples.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExecLogStorageSeed.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExtractDepositData.lean` | 1 |
| `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/LogRecordsRlp.lean` | 1 |
| `EvmAsm/Codegen/Programs/MaterializeLogRecords.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptEncodeLeafBranch.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptWitnessLookup.lean` | 1 |
| `EvmAsm/Codegen/Programs/MultiTxSenderDebit.lean` | 2 |
| `EvmAsm/Codegen/Programs/NonstorageEffectLog.lean` | 2 |
| `EvmAsm/Codegen/Programs/P256Verify.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParseDepositRequests.lean` | 1 |
| `EvmAsm/Codegen/Programs/ReceiptList.lean` | 1 |
| `EvmAsm/Codegen/Programs/ReceiptsConsensus.lean` | 1 |
| `EvmAsm/Codegen/Programs/RequestsHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/Ripemd160.lean` | 1 |
| `EvmAsm/Codegen/Programs/RlpRead.lean` | 2 |
| `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 1 |
| `EvmAsm/Codegen/Programs/SeedTxAccessList.lean` | 1 |
| `EvmAsm/Codegen/Programs/SenderBalanceDebit.lean` | 1 |
| `EvmAsm/Codegen/Programs/SimpleTransferFeeRecipient.lean` | 1 |
| `EvmAsm/Codegen/Programs/SimpleTransferRecipient.lean` | 1 |
| `EvmAsm/Codegen/Programs/SstoreGasRefund.lean` | 1 |
| `EvmAsm/Codegen/Programs/SstoreRegularGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/StageBlockhashM29.lean` | 1 |
| `EvmAsm/Codegen/Programs/SystemCallStaging.lean` | 3 |
| `EvmAsm/Codegen/Programs/SystemCallStoragePreload.lean` | 1 |
| `EvmAsm/Codegen/Programs/SystemStorageSlotTuples.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxExtract.lean` | 5 |
| `EvmAsm/Codegen/Programs/TxGasBalPostVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxGasBalPostVerifyRuntime.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxIntrinsicStateGas.lean` | 5 |
| `EvmAsm/Codegen/Programs/TxSignature.lean` | 6 |
| `EvmAsm/Codegen/Programs/WitnessCodeLookup.lean` | 1 |

