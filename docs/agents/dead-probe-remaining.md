# Remaining Dead Codegen Probe Programs (not yet removed)

<!-- Tracked as an issue for batching: https://github.com/Verified-zkEVM/evm-asm/issues/12866 -->
<!-- Latest scan count: 99 (regenerate with `python3 scripts/scan_deadprobes.py`). -->
<!-- Keep the count line in sync when a batch below is completed. -->

Registry of unverified `EvmAsm/Codegen/Programs/` modules that still define
RISC-V assembly-string probes but are linked into no `zisk*` BuildUnit, so they
are deadweight a future PR can `git rm`. The list is generated and reproducible
by **committed** `scripts/scan_deadprobes.py` (re-run it to refresh); entries are
cross-checked with the `git grep -l <Name>` method in the Reviewer playbook.

## Completed batches (do not re-list)

* **PR #12814** — 12 block-hash historical-state extractors
  (`BeneficiaryAtBlockHash ... CodeAtBlockHash`).
* **PR #12860** — 12 block-number historical-state extractors
  (`BalanceAtBlockNumber ... ExtcodesizeAtBlockNumber`, exactly the mirror of
  #12814).

In flight: a `State*` account/state-extractor batch (20 files, `StateBalanceProof` ... `StateWalkExtractSlot`) was filed as a dead-code PR. Move it into Completed batches once merged.

In flight: a `Bal*` non-storage field-comparator batch (7 files, `BalAccountAccessDescriptors` ... `BalAccountCodeConsistent`) filed as the equivalent of #12943. `BalAccountCodeConsistent` surfaces dead only once the 6 sibling files (one of them, `BalAllAccountsCode`, references its defs inline) are removed, so all seven go together. Move it into Completed batches once merged.

## Identification criteria (every entry meets all three)

1. **Probe family by stem.** For one module stem `S` the file defines, matching
   its own internal naming convention,

       `<stem-lc>Function`          # the emitted RISC-V assembly string
       `zisk<S>Prologue`            # the zisk build-unit prologue wrapper
       `zisk<S>DataSection`         # the probe data section

   (the `Function` def and the two `zisk` wrappers differ only in the case of the
   first letter of `S`, so the family is recognised by matching stems, not by
   stringifying a single stem twice).
2. **Every `def` in the file is unreferenced outside it** — a file is dead only
   when *all* of its definitions (including any local helper `def`) appear in
   exactly one `.lean` file. This is the proof step; mentions-equals-one is only
   a fast filter and never by itself the evidence.
3. **Not a build unit of record.** The probe runner that used to link them into
   a `zisk*` build unit is gone.

Because the deadness test is per-file on *every* definition, files that carry
several families (for example `ChainAggregator.lean` defines five) are caught,
and files that are still live anywhere (for example `TxTotalBlobGas.lean`, whose
`calculate_total_blob_gas` helper is referenced by the `Stateless/SpecRef` port)
are correctly excluded even though their probe strings are self-contained.

## Remaining 99 files

```text
  - AccountExistsAtBlockHash
  - AccountExistsAtBlockNumber
  - AccountIsEmptyAtBlockHash
  - AccountIsEmptyAtBlockNumber
  - AccountStorageWalkable
  - AccountVerify
  - B3CoinbaseFee
  - BaseFeePerGasAtBlockHash
  - BaseFeePerGasAtBlockNumber
  - BlobGasPairAtBlockHash
  - BlobGasUsedAtBlockHash
  - BlobGasUsedAtBlockNumber
  - Block
  - BlockEmpty
  - BlockHashAtBlockNumber
  - BlockHashAtStateRoot
  - BlockHashWindow
  - BlockNumberAtBlockHash
  - BlockNumberAtStateRoot
  - BlockRoots
  - BlockRootsAtBlockHash
  - BlockValidate
  - BlockValidate1Tx
  - BlockVerdictRecipientCredits
  - BlockVerdictTxsIndependent
  - ChainAggregator
  - ChainBasefee
  - ChainBlobCount
  - ChainEndpoints
  - ChainExcessBlobGas
  - ChainLinkExtract
  - ChainLinkParentKeccak
  - ChainTimestamp
  - ChainWalkNStepsBack
  - ChainWalkOneStepBack
  - CodeAtStateRoot
  - CodeVerify
  - CreateDescend
  - Eip2935
  - Eip4788
  - EvmOpcodesStorageRoot
  - ExcessBlobGasAtBlockHash
  - ExcessBlobGasAtBlockNumber
  - ExtcodecopyAtBlockHash
  - ExtcodecopyAtBlockNumber
  - ExtcodehashAtBlockHash
  - ExtcodehashAtBlockNumber
  - GasLimitAtBlockHash
  - GasLimitAtBlockNumber
  - GasPairAtBlockHash
  - GasUsedAtBlockHash
  - GasUsedAtBlockNumber
  - HeaderChainPostMerge
  - HeaderGasLimits
  - HeaderNonceAtBlockHash
  - HeaderNonceAtBlockNumber
  - HeaderSummaryStruct
  - LogsBloomKeccakAtBlockHash
  - LogsBloomKeccakAtBlockNumber
  - MptNibbles
  - NumberTimestampPairAtBlockHash
  - OmmersHashAtBlockHash
  - OmmersHashAtBlockNumber
  - ParentBeaconBlockRootAtBlockHash
  - ParentBeaconBlockRootAtBlockNumber
  - PostMergeInvariantsAtBlockHash
  - PrevRandaoAtBlockHash
  - PrevRandaoAtBlockNumber
  - ReceiptsRootAtBlockHash
  - ReceiptsRootAtBlockNumber
  - SelfdestructDescriptors
  - SimpleTransferFeeRecipient
  - SimpleTransferRecipient
  - SloadAtBlockHash
  - SloadAtBlockNumber
  - StorageCompose
  - StorageProof
  - StorageRoot
  - StorageRootInWitness
  - StorageVerify
  - TransactionsRootAtBlockHash
  - TransactionsRootAtBlockNumber
  - TxDecode
  - TxTail
  - WithdrawalsRootAtBlockHash
  - WithdrawalsRootAtBlockNumber
  - WitnessCodesKeccakAtIndex
  - WitnessHeadersAccountAtIndex
  - WitnessHeadersAllChainLinksValidate
  - WitnessHeadersBlockHashAtIndex
  - WitnessHeadersChainLink
  - WitnessHeadersFindIndexByBlockHash
  - WitnessHeadersSlotAtIndex
  - WitnessHeadersStateRootAtIndex
  - WitnessNodeKindDistribution
  - WitnessStateKeccakAtIndex
  - WitnessStorageKeccakAtIndex
  - WitnessStorageNodeKindDistribution
  - WitnessValidation
```
