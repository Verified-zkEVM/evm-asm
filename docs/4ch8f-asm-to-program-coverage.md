# 4ch8f.9 — asm-string → Program conversion coverage

_Regenerate with `python3 scripts/asm_to_program.py coverage` (requires `riscv64-unknown-elf-as`/`-objcopy`)._

Every `*Function : String` def under `EvmAsm/Codegen/Programs/` and `EvmAsm/Codegen/Dispatch.lean` is parsed to a `Program`, rendered back with `emitProgram`, and the render is assembled with `riscv64-unknown-elf-as` and byte-compared against the original hand-written text (`.text` of both). See `docs/4ch8f-asm-to-program.md` for the design and trust model.

## Summary

| Class | Count | Meaning |
|---|---:|---|
| BLOCKED_ON_.6 | 548 | Contains `la <symbol>` scratch/global addressing or a cross-function `jal <callee>` — needs the authoritative linker-pinned address table (bead evm-asm-4ch8f.6). |
| COMPOSITE | 139 | RHS is not a pure string literal (concatenates other defs / probe prologues / data sections) — not a standalone routine body. **No wave bead needed:** these resolve automatically as their component functions convert. |
| ALREADY-STRUCTURED | 132 | RHS is already `"label:\n" ++ emitProgram <prog>` — a landed conversion (this PR: 16) or a prior template splice (RlpWalk, *SAsm). |
| NEEDS-LI-EXPANSION | 20 | Contains an `li rd, C` with C outside 12-bit signed range; a faithful 4-byte-per-`Instr` Program must emit the explicit `lui`/`addiw`/… expansion as separate `Instr`s (follow-up wave). |
| CALLER-LOCAL-FRAGMENT | 8 | Branches/jumps to a `.L` label owned by the caller, or has no own entry label — no independent ABI; needs extraction into a status-returning callable first. |
| MULTI-ENTRY-BUNDLE | 4 | Defines secondary non-`.L` labels (e.g. `*_clear`/`*_append`/`*_record_nth`) that other files `jal` into as cross-function entry points; `emitProgram` keeps only the entry label, so converting would silently break the guest link (caught only by the whole-guest byte-identity gate). Needs a multi-entry ABI / the .6 layout. |
| **TOTAL** | **851** | |

## Landed in this PR (125)

| Function | File | Instrs |
|---|---|---:|
| `b1SenderTableFindFunction` | `EvmAsm/Codegen/Programs/BlockVerdictSenderCounts.lean` | 0 |
| `bahU32leFunction` | `EvmAsm/Codegen/Programs/BlockAccessListHash.lean` | 0 |
| `bgvU32leFunction` | `EvmAsm/Codegen/Programs/BalGasValid.lean` | 0 |
| `bgvU64leFunction` | `EvmAsm/Codegen/Programs/BalGasValid.lean` | 0 |
| `bhrRevLeBeFunction` | `EvmAsm/Codegen/Programs/BlockHeaderSszToRlp.lean` | 0 |
| `blake2fLdLe64Function` | `EvmAsm/Codegen/Programs/Blake2f.lean` | 0 |
| `blake2fStLe64Function` | `EvmAsm/Codegen/Programs/Blake2f.lean` | 0 |
| `bloomEqFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `bloomOrIntoFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `bls12CopyQuadsFunction` | `EvmAsm/Codegen/Programs/Bls12Field.lean` | 0 |
| `bls12Fq12CopyFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12EqFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12IsZeroFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12Fq12ZeroFunction` | `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 0 |
| `bls12G1BeToLeFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1Copy96Function` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1Eq48Function` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1IsZeroFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1LeToBeFunction` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G1Zero96Function` | `EvmAsm/Codegen/Programs/Bls12G1.lean` | 0 |
| `bls12G2EqNFunction` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12G2Zero192Function` | `EvmAsm/Codegen/Programs/Bls12G2.lean` | 0 |
| `bls12KzgG1WireFunction` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 0 |
| `bls12KzgLtBeFunction` | `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 0 |
| `bls12PtCopyFunction` | `EvmAsm/Codegen/Programs/Bls12Pairing.lean` | 0 |
| `bn254CallAllotmentFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254FieldBeToLeFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldEq32Function` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldIsZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254FieldLeToBeFunction` | `EvmAsm/Codegen/Programs/Bn254Field.lean` | 0 |
| `bn254Fp2CopyFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2EqFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2IsZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fp2ZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 0 |
| `bn254Fq12CopyFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12EqFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12IsZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254Fq12ZeroFunction` | `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 0 |
| `bn254PointCopy64Function` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PointIsInfFunction` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PointZero64Function` | `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 0 |
| `bn254PtCopyFunction` | `EvmAsm/Codegen/Programs/Bn254Pairing.lean` | 0 |
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
| `eip8037BlockGasUsedFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `enrgU32leFunction` | `EvmAsm/Codegen/Programs/Eip7702NonceReuseGuard.lean` | 0 |
| `ephU32leFunction` | `EvmAsm/Codegen/Programs/SszParentHeader.lean` | 0 |
| `execLogLatestValueFunction` | `EvmAsm/Codegen/Programs/ExecLogLatestValue.lean` | 0 |
| `expGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `findCodeEffectByAddressFunction` | `EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean` | 0 |
| `headersParentHashFunction` | `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 0 |
| `hpDecodeNibblesFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `hpEncodeNibblesFunction` | `EvmAsm/Codegen/Programs/Mpt.lean` | 0 |
| `initCodeCostFunction` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `intrinsicGasCalldataFloorEip7623Function` | `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 0 |
| `keccak256WordGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `logDataGasFunction` | `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 0 |
| `memoryExpansionGasFunction` | `EvmAsm/Codegen/Programs/MemoryExpansionGas.lean` | 0 |
| `mptBranchPayloadTwoSlotsFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` | 0 |
| `mptCompactToNibblesFunction` | `EvmAsm/Codegen/Programs/MptNibbles.lean` | 0 |
| `mptNibblesToCompactFunction` | `EvmAsm/Codegen/Programs/MptNibbles.lean` | 0 |
| `msetMemcpyFunction` | `EvmAsm/Codegen/Programs/MptSet.lean` | 0 |
| `nibblesCommonPrefixLenFunction` | `EvmAsm/Codegen/Programs/MptEncode.lean` | 0 |
| `p256BeToLeFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256CopyNFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256Eq32Function` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256IsZeroNFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256LeToBeFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `p256LtBeFunction` | `EvmAsm/Codegen/Programs/P256Verify.lean` | 0 |
| `parentHeaderMatchesWitnessFirstFunction` | `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 0 |
| `rlpBytesEncodedSizeFunction` | `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 0 |
| `rlpEncodeBytesFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpEncodeListPrefixFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpEncodeU64Function` | `EvmAsm/Codegen/Programs/Receipt.lean` | 0 |
| `rlpEncodeUintBeFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpListCountItemsFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `rlpListEncodedSizeFunction` | `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 0 |
| `rlpListNthItemFunction` | `EvmAsm/Codegen/Programs/RlpRead.lean` | 0 |
| `runningBloomCopyFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `runningBloomZeroFunction` | `EvmAsm/Codegen/Programs/Bloom.lean` | 0 |
| `secp256k1FieldBeToLeFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldCopy32Function` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldEq32Function` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldGetBitFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldIsZeroFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldLeToBeFunction` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1FieldZero32Function` | `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 0 |
| `secp256k1PointCopy64Function` | `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 0 |
| `secp256k1PointZero64Function` | `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 0 |
| `senderPostNonceConsistentFunction` | `EvmAsm/Codegen/Programs/SenderPostNonceConsistent.lean` | 0 |
| `slotDecodeU256Function` | `EvmAsm/Codegen/Programs/State.lean` | 0 |
| `slotTupleSequencesMatchFunction` | `EvmAsm/Codegen/Programs/SlotTupleSequencesMatch.lean` | 0 |
| `spwU32leFunction` | `EvmAsm/Codegen/Programs/SszPayloadWithdrawals.lean` | 0 |
| `sszPackBytesFunction` | `EvmAsm/Codegen/Programs/Ssz.lean` | 0 |
| `swdMinimalCopyFunction` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swdReadU64leFunction` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swdWriteBe32U64Function` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swdWriteBe8Function` | `EvmAsm/Codegen/Programs/SystemWrites.lean` | 0 |
| `swrRevLeBeFunction` | `EvmAsm/Codegen/Programs/SszWithdrawal.lean` | 0 |
| `swsU32leFunction` | `EvmAsm/Codegen/Programs/SszWitnessState.lean` | 0 |
| `txGasResultIncrementsFunction` | `EvmAsm/Codegen/Programs/Account.lean` | 0 |
| `txPubkeyEcrecoverStageMaterialFunction` | `EvmAsm/Codegen/Programs/TxPubkey.lean` | 0 |
| `txRefundCapFunction` | `EvmAsm/Codegen/Programs/TxRefund.lean` | 0 |
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
| `u256SubBeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `u256ToU64BeFunction` | `EvmAsm/Codegen/Programs/U256.lean` | 0 |
| `validateHeaderBasicFunction` | `EvmAsm/Codegen/Programs/Header.lean` | 0 |
| `witnessCodesValidateLengthsFunction` | `EvmAsm/Codegen/Programs/WitnessValidation.lean` | 0 |

## CONVERTED-CLEAN (0)

| Function | File | Instrs | Note |
|---|---|---:|---|

## NEEDS-LI-EXPANSION (20)

| Function | File | Instrs | Note |
|---|---|---:|---|
| `dispatcherTxGasSettleFunction` | `EvmAsm/Codegen/Dispatch.lean` |  | li 0xa0010000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `frameBaseFunction` | `EvmAsm/Codegen/Programs/CallFrameBase.lean` |  | li 0x29000: constant needs multi-instruction expansion (NEEDS-LI-EXPAN |
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
| `sszHashTreeRootListByteListFunction` | `EvmAsm/Codegen/Programs/Ssz.lean` |  | li 4096: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `statelessVerdictFromSszFunction` | `EvmAsm/Codegen/Programs/StatelessVerdict.lean` |  | li 0x40000000: constant needs multi-instruction expansion (NEEDS-LI-EX |
| `systemWriteDescriptorsFunction` | `EvmAsm/Codegen/Programs/SystemWrites.lean` |  | li 8191: constant needs multi-instruction expansion (NEEDS-LI-EXPANSIO |
| `intrinsicGasLegacyFunction` | `EvmAsm/Codegen/Programs/Tx.lean` |  | li 21000: constant needs multi-instruction expansion (NEEDS-LI-EXPANSI |
| `validateTransactionBasicFunction` | `EvmAsm/Codegen/Programs/Tx.lean` |  | li 0xffffffff: constant needs multi-instruction expansion (NEEDS-LI-EX |

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

## BLOCKED_ON_.6 (548) — by file

| File | Count |
|---|---:|
| `EvmAsm/Codegen/Dispatch.lean` | 2 |
| `EvmAsm/Codegen/Programs/Account.lean` | 9 |
| `EvmAsm/Codegen/Programs/AccountApplyStorage.lean` | 2 |
| `EvmAsm/Codegen/Programs/AccountBalance.lean` | 3 |
| `EvmAsm/Codegen/Programs/AccountExistsAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountExistsAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountFieldExtract.lean` | 2 |
| `EvmAsm/Codegen/Programs/AccountFieldGetters.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountFields.lean` | 9 |
| `EvmAsm/Codegen/Programs/AccountIsEmptyAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountIsEmptyAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountStorageWalkable.lean` | 1 |
| `EvmAsm/Codegen/Programs/AccountVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/Address.lean` | 3 |
| `EvmAsm/Codegen/Programs/AssembleExecutionRequests.lean` | 1 |
| `EvmAsm/Codegen/Programs/B3CoinbaseFee.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountAccessDescriptors.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountApplyPostFields.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountChangeDescriptor.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountChangeValue.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountCodeConsistent.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountDescriptorArray.lean` | 2 |
| `EvmAsm/Codegen/Programs/BalAccountHasStateChange.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountNonstorageConsistent.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountNonstorageFinals.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountNthDescriptor.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountPath.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountPostFields.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountRecordArray.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAccountStateRoot.lean` | 2 |
| `EvmAsm/Codegen/Programs/BalAllAccountsCode.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAllAccountsCodeCovers.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalAllAccountsNonstorageCovers.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalGasValid.lean` | 2 |
| `EvmAsm/Codegen/Programs/BalModeledSystem.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalStorageAccessDescriptors.lean` | 1 |
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
| `EvmAsm/Codegen/Programs/BlockAccessListHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockBody.lean` | 6 |
| `EvmAsm/Codegen/Programs/BlockEmpty.lean` | 3 |
| `EvmAsm/Codegen/Programs/BlockGasRemaining.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashAtStateRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 6 |
| `EvmAsm/Codegen/Programs/BlockHashWindow.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockNumberAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockNumberAtStateRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockRoots.lean` | 4 |
| `EvmAsm/Codegen/Programs/BlockRootsAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockValidate.lean` | 5 |
| `EvmAsm/Codegen/Programs/BlockValidate1Tx.lean` | 3 |
| `EvmAsm/Codegen/Programs/BlockVerdictBalFindAccount.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictGasResults.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictModeledSystem.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictSimpleTransfer.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockVerdictSysChange.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictTxsIndependent.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bloom.lean` | 5 |
| `EvmAsm/Codegen/Programs/BloomAddValue.lean` | 1 |
| `EvmAsm/Codegen/Programs/BloomBlock.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Field.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bls12G1.lean` | 9 |
| `EvmAsm/Codegen/Programs/Bls12G2.lean` | 12 |
| `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bls12Map.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 5 |
| `EvmAsm/Codegen/Programs/Bn254Field.lean` | 3 |
| `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 7 |
| `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 3 |
| `EvmAsm/Codegen/Programs/CallFrameSwitch.lean` | 4 |
| `EvmAsm/Codegen/Programs/Chain.lean` | 11 |
| `EvmAsm/Codegen/Programs/ChainAggregator.lean` | 5 |
| `EvmAsm/Codegen/Programs/ChainBasefee.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainBlobCount.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainEndpoints.lean` | 9 |
| `EvmAsm/Codegen/Programs/ChainExcessBlobGas.lean` | 3 |
| `EvmAsm/Codegen/Programs/ChainLinkExtract.lean` | 1 |
| `EvmAsm/Codegen/Programs/ChainLinkParentKeccak.lean` | 1 |
| `EvmAsm/Codegen/Programs/ChainTimestamp.lean` | 2 |
| `EvmAsm/Codegen/Programs/ChainValidate.lean` | 10 |
| `EvmAsm/Codegen/Programs/ChainValidateBlob.lean` | 4 |
| `EvmAsm/Codegen/Programs/ChainValidatePostMerge.lean` | 4 |
| `EvmAsm/Codegen/Programs/ChainWalkNStepsBack.lean` | 1 |
| `EvmAsm/Codegen/Programs/ChainWalkOneStepBack.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeAtStateRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeHashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/CodeVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/CommittedStorageLookup.lean` | 2 |
| `EvmAsm/Codegen/Programs/DifficultyAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/DifficultyAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/DispatcherExecStateGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/Eip2935.lean` | 1 |
| `EvmAsm/Codegen/Programs/Eip4788.lean` | 1 |
| `EvmAsm/Codegen/Programs/Eip7702Authority.lean` | 1 |
| `EvmAsm/Codegen/Programs/Eip7702NonceReuseGuard.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmCodes.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmNonce.lean` | 1 |
| `EvmAsm/Codegen/Programs/EvmOpcodes.lean` | 2 |
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
| `EvmAsm/Codegen/Programs/HashBridge.lean` | 3 |
| `EvmAsm/Codegen/Programs/Header.lean` | 7 |
| `EvmAsm/Codegen/Programs/HeaderBaseFee.lean` | 3 |
| `EvmAsm/Codegen/Programs/HeaderChain.lean` | 5 |
| `EvmAsm/Codegen/Programs/HeaderChainPostMerge.lean` | 3 |
| `EvmAsm/Codegen/Programs/HeaderDecode.lean` | 3 |
| `EvmAsm/Codegen/Programs/HeaderFields.lean` | 12 |
| `EvmAsm/Codegen/Programs/HeaderGasExtract.lean` | 2 |
| `EvmAsm/Codegen/Programs/HeaderGasLimits.lean` | 5 |
| `EvmAsm/Codegen/Programs/HeaderNonceAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeaderNonceAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeaderSummaryStruct.lean` | 1 |
| `EvmAsm/Codegen/Programs/HeaderU64.lean` | 9 |
| `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 5 |
| `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/LogsBloomKeccakAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/LogsBloomKeccakAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Mpt.lean` | 5 |
| `EvmAsm/Codegen/Programs/MptDeleteAcc.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptDeleteWalkDb.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptEncode.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptEncodeLeafBranch.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptIndexedTrieRoot.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptInsert.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsertAcc.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsertWalk.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInsertWalkDb.lean` | 1 |
| `EvmAsm/Codegen/Programs/MptInternal.lean` | 8 |
| `EvmAsm/Codegen/Programs/MptSet.lean` | 3 |
| `EvmAsm/Codegen/Programs/MptSetAcc.lean` | 6 |
| `EvmAsm/Codegen/Programs/MptStateRootIns.lean` | 1 |
| `EvmAsm/Codegen/Programs/NonceAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/NonceAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/NonstorageEffectLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/NumberTimestampPairAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/OmmersHashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/OmmersHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/P256Verify.lean` | 6 |
| `EvmAsm/Codegen/Programs/ParentBeaconBlockRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentBeaconBlockRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentHashAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ParentHashAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/PostMergeInvariantsAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/PrevRandaoAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/PrevRandaoAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Receipt.lean` | 2 |
| `EvmAsm/Codegen/Programs/ReceiptsRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/ReceiptsRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/ReceiptsRootIndexed.lean` | 1 |
| `EvmAsm/Codegen/Programs/RuntimeSameBlockCode.lean` | 1 |
| `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 2 |
| `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 15 |
| `EvmAsm/Codegen/Programs/Secp256k1Recover.lean` | 1 |
| `EvmAsm/Codegen/Programs/SeedTxAccessList.lean` | 1 |
| `EvmAsm/Codegen/Programs/SelfdestructDescriptors.lean` | 2 |
| `EvmAsm/Codegen/Programs/SloadAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/SloadAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Ssz.lean` | 4 |
| `EvmAsm/Codegen/Programs/SszParentHeader.lean` | 1 |
| `EvmAsm/Codegen/Programs/SszPayloadWithdrawals.lean` | 1 |
| `EvmAsm/Codegen/Programs/SszWithdrawal.lean` | 2 |
| `EvmAsm/Codegen/Programs/SszWitnessState.lean` | 1 |
| `EvmAsm/Codegen/Programs/State.lean` | 5 |
| `EvmAsm/Codegen/Programs/StateAccountAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateAccountAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateAccountSpecDefault.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateBalanceProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateCodeHashProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateCompose.lean` | 6 |
| `EvmAsm/Codegen/Programs/StateExtractBalance.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateExtractCodeHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateExtractNonce.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateExtractStorageRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/StateNonceProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StatePredicates.lean` | 2 |
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
| `EvmAsm/Codegen/Programs/Step2Verdict.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageCompose.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageProof.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRoot.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageRootInWitness.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageVerify.lean` | 1 |
| `EvmAsm/Codegen/Programs/StorageWrite.lean` | 2 |
| `EvmAsm/Codegen/Programs/SystemCallStaging.lean` | 2 |
| `EvmAsm/Codegen/Programs/TimestampAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/TimestampAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/TransactionsRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/TransactionsRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/Tx.lean` | 8 |
| `EvmAsm/Codegen/Programs/TxBlobGas.lean` | 3 |
| `EvmAsm/Codegen/Programs/TxDecode.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode1559.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode2930.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode4844.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxDecode7702.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxExtract.lean` | 2 |
| `EvmAsm/Codegen/Programs/TxGasSenderBalLookup.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxIntrinsicStateGas.lean` | 2 |
| `EvmAsm/Codegen/Programs/TxPubkey.lean` | 4 |
| `EvmAsm/Codegen/Programs/TxRoot.lean` | 4 |
| `EvmAsm/Codegen/Programs/TxSigningHash.lean` | 4 |
| `EvmAsm/Codegen/Programs/TxTotalBlobGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/U256.lean` | 1 |
| `EvmAsm/Codegen/Programs/U256GasPricing.lean` | 2 |
| `EvmAsm/Codegen/Programs/ValidateHeaderPair.lean` | 1 |
| `EvmAsm/Codegen/Programs/VerifyPublicKeysSenders.lean` | 1 |
| `EvmAsm/Codegen/Programs/Withdrawal.lean` | 7 |
| `EvmAsm/Codegen/Programs/WithdrawalBlockSummary.lean` | 2 |
| `EvmAsm/Codegen/Programs/WithdrawalPath.lean` | 1 |
| `EvmAsm/Codegen/Programs/WithdrawalsRootAtBlockHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/WithdrawalsRootAtBlockNumber.lean` | 1 |
| `EvmAsm/Codegen/Programs/WithdrawalsRootIndexed.lean` | 1 |
| `EvmAsm/Codegen/Programs/WithdrawalsStateRoot.lean` | 1 |
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

## ALREADY-STRUCTURED (132) — by file

| File | Count |
|---|---:|
| `EvmAsm/Codegen/Programs/Account.lean` | 1 |
| `EvmAsm/Codegen/Programs/BalGasValid.lean` | 2 |
| `EvmAsm/Codegen/Programs/Blake2f.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockAccessListHash.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHashPredicates.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockHeaderSszToRlp.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockRlpSize.lean` | 2 |
| `EvmAsm/Codegen/Programs/BlockVerdictSenderCounts.lean` | 1 |
| `EvmAsm/Codegen/Programs/BlockhashRequiredHeaders.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bloom.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bls12Field.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bls12Fq12.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bls12G1.lean` | 6 |
| `EvmAsm/Codegen/Programs/Bls12G2.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Kzg.lean` | 2 |
| `EvmAsm/Codegen/Programs/Bls12Pairing.lean` | 1 |
| `EvmAsm/Codegen/Programs/Bn254Curve.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bn254Field.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bn254Fp2.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bn254Fq12.lean` | 4 |
| `EvmAsm/Codegen/Programs/Bn254Pairing.lean` | 1 |
| `EvmAsm/Codegen/Programs/CallFrameDescend.lean` | 1 |
| `EvmAsm/Codegen/Programs/CommittedStorageSnapshot.lean` | 3 |
| `EvmAsm/Codegen/Programs/CreateCodeEffectLog.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateDeployedCodeValid.lean` | 1 |
| `EvmAsm/Codegen/Programs/CreateInitcodeSizeValid.lean` | 1 |
| `EvmAsm/Codegen/Programs/DynamicOpcodeGas.lean` | 4 |
| `EvmAsm/Codegen/Programs/Eip7702NonceReuseGuard.lean` | 1 |
| `EvmAsm/Codegen/Programs/ExecLogLatestValue.lean` | 1 |
| `EvmAsm/Codegen/Programs/Header.lean` | 2 |
| `EvmAsm/Codegen/Programs/HeadersKeccak.lean` | 1 |
| `EvmAsm/Codegen/Programs/IntrinsicGas.lean` | 4 |
| `EvmAsm/Codegen/Programs/MemoryExpansionGas.lean` | 1 |
| `EvmAsm/Codegen/Programs/Mpt.lean` | 3 |
| `EvmAsm/Codegen/Programs/MptEncode.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptNibbles.lean` | 2 |
| `EvmAsm/Codegen/Programs/MptSet.lean` | 1 |
| `EvmAsm/Codegen/Programs/P256Verify.lean` | 6 |
| `EvmAsm/Codegen/Programs/Receipt.lean` | 1 |
| `EvmAsm/Codegen/Programs/RlpRead.lean` | 5 |
| `EvmAsm/Codegen/Programs/RlpWalk.lean` | 5 |
| `EvmAsm/Codegen/Programs/Secp256k1Curve.lean` | 2 |
| `EvmAsm/Codegen/Programs/Secp256k1Field.lean` | 7 |
| `EvmAsm/Codegen/Programs/SenderPostNonceConsistent.lean` | 1 |
| `EvmAsm/Codegen/Programs/SlotTupleSequencesMatch.lean` | 1 |
| `EvmAsm/Codegen/Programs/Ssz.lean` | 1 |
| `EvmAsm/Codegen/Programs/SszParentHeader.lean` | 1 |
| `EvmAsm/Codegen/Programs/SszPayloadWithdrawals.lean` | 1 |
| `EvmAsm/Codegen/Programs/SszWithdrawal.lean` | 1 |
| `EvmAsm/Codegen/Programs/SszWitnessState.lean` | 1 |
| `EvmAsm/Codegen/Programs/State.lean` | 1 |
| `EvmAsm/Codegen/Programs/SystemWrites.lean` | 4 |
| `EvmAsm/Codegen/Programs/Tx.lean` | 2 |
| `EvmAsm/Codegen/Programs/TxExtract.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxPubkey.lean` | 1 |
| `EvmAsm/Codegen/Programs/TxRefund.lean` | 1 |
| `EvmAsm/Codegen/Programs/U256.lean` | 10 |
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

