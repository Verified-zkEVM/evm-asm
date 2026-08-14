/-
  EvmAsm.Codegen.Programs.RegistryTail

  Tail half of the CLI program lookup table. This is split from
  Programs.lean so the public registry module stays small and the
  generated match expression remains below backend nesting limits.
-/

import EvmAsm.Codegen.Programs.Imports
import EvmAsm.Codegen.Programs.EvmLogHandlers
import EvmAsm.Codegen.Programs.EvmMessageCallGas
import EvmAsm.Codegen.Programs.TxRefund
import EvmAsm.Codegen.Programs.StorageMultiContract
import EvmAsm.Codegen.Programs.BalStorageChangeValues
import EvmAsm.Codegen.Programs.ExecLogLatestValue
import EvmAsm.Codegen.Programs.SstoreRegularGas
import EvmAsm.Codegen.Programs.MemoryExpansionGas
import EvmAsm.Codegen.Programs.DynamicOpcodeGas
import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.ExecLogStorageSeed
import EvmAsm.Codegen.Programs.BalRecipientFieldEmpty
import EvmAsm.Codegen.Programs.SenderBalanceDebit
import EvmAsm.Codegen.Programs.BalStorageReadsExecLog
import EvmAsm.Codegen.Probes.BalSerializerMeasureProbe
import EvmAsm.Codegen.Probes.BalSelftestsProbe
import EvmAsm.Codegen.Probes.BalOrderDumpProbe
import EvmAsm.Codegen.Programs.CreateDescend
import EvmAsm.Codegen.Programs.BalAddrExecLogKey
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalAccountCodeConsistent
import EvmAsm.Codegen.Programs.BalAllAccountsCode
import EvmAsm.Codegen.Programs.BalAllAccountsCodeCovers
import EvmAsm.Codegen.Programs.ExtractDepositData
import EvmAsm.Codegen.Programs.TxGasBalPostVerifyRuntime
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Programs.CreateDeployedCodeValid
import EvmAsm.Codegen.Programs.CreateInitcodeSizeValid
import EvmAsm.Codegen.Programs.CreateCreatorNonce
import EvmAsm.Codegen.Programs.SenderPostNonceConsistent
import EvmAsm.Codegen.Programs.NonstorageEffectLog
import EvmAsm.Codegen.Programs.CreateRoundtrip
import EvmAsm.Codegen.Programs.CallBalanceGate
import EvmAsm.Codegen.Programs.CallValueEffect
import EvmAsm.Codegen.Programs.CallDepthLimit
import EvmAsm.Codegen.Programs.StageBlockhashM29
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.DepositDerivationE2E
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.LogRecordsRlp
import EvmAsm.Codegen.Programs.DispatcherExecStateGas
import EvmAsm.Codegen.Programs.DispatcherTxGasSettle
import EvmAsm.Codegen.Programs.MultiTxSenderDebit
import EvmAsm.Codegen.Programs.BlockVerdictSenderCounts
import EvmAsm.Codegen.Programs.B3CoinbaseFee
import EvmAsm.Codegen.Programs.BlockVerdictRecipientCredits
import EvmAsm.Codegen.Programs.CommittedStorageLookup
import EvmAsm.Codegen.Probes.SparseEpochProbe

namespace EvmAsm.Codegen

def lookupProgramTail : String → Option BuildUnit

  | "zisk_create_code_effect_log" => some ziskCreateCodeEffectLogProbeUnit
  | "zisk_nonstorage_effect_log" => some ziskNonstorageEffectLogProbeUnit
  | "zisk_bal_serializer_measure" => some ziskBalSerializerMeasureProbeUnit
  | "zisk_bal_selftests" => some ziskBalSelftestsProbeUnit

  -- Re-register probes whose dispatch arms were dropped in a registry refactor;
  -- each still has a codegen-zisk-*-check.sh. See bead evm-asm-8bt13.

  | name => lookupReceiptProgramTail name

end EvmAsm.Codegen
