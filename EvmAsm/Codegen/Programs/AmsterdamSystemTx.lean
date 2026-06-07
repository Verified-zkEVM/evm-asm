/-
  EvmAsm.Codegen.Programs.AmsterdamSystemTx

  Shared constants for Amsterdam system transactions.  These mirror
  execution-specs `src/ethereum/forks/amsterdam/fork.py` and `vm/gas.py`:
  `process_unchecked_system_transaction` constructs a SYSTEM-address call with
  a fixed 30M regular gas budget and a bounded state-gas reservoir sized for
  16 storage-set writes.  The concrete system-contract children (EIP-4788,
  EIP-2935, EIP-7002, EIP-7251) should import this module instead of
  open-coding these numbers.
-/

namespace EvmAsm.Codegen

/-- execution-specs Amsterdam `SYSTEM_TRANSACTION_GAS`. -/
def amsterdamSystemTransactionGas : Nat := 30000000

/-- execution-specs Amsterdam `COST_PER_STATE_BYTE`. -/
def amsterdamCostPerStateByte : Nat := 1530

/-- execution-specs Amsterdam `STATE_BYTES_PER_STORAGE_SET`. -/
def amsterdamStateBytesPerStorageSet : Nat := 64

/-- execution-specs Amsterdam `STATE_BYTES_PER_NEW_ACCOUNT`. -/
def amsterdamStateBytesPerNewAccount : Nat := 120

/-- execution-specs Amsterdam `STATE_BYTES_PER_AUTH_BASE`. -/
def amsterdamStateBytesPerAuthBase : Nat := 23

/-- execution-specs Amsterdam `SYSTEM_MAX_SSTORES_PER_CALL`. -/
def amsterdamSystemMaxSstoresPerCall : Nat := 16

/-- State gas charged for one zero-to-nonzero storage set. -/
def amsterdamStorageSetStateGas : Nat :=
  amsterdamStateBytesPerStorageSet * amsterdamCostPerStateByte

/-- State gas precharged for one new-account creation. -/
def amsterdamNewAccountStateGas : Nat :=
  amsterdamStateBytesPerNewAccount * amsterdamCostPerStateByte

/-- State gas precharged for one EIP-7702 authorization. -/
def amsterdamAuthStateGas : Nat :=
  (amsterdamStateBytesPerNewAccount + amsterdamStateBytesPerAuthBase) * amsterdamCostPerStateByte

/-- State-gas reservoir passed to each Amsterdam system transaction. -/
def amsterdamSystemStateGasReservoir : Nat :=
  amsterdamStorageSetStateGas * amsterdamSystemMaxSstoresPerCall

/-- Assembly `li` helper for the per-storage-set state gas constant. -/
def liAmsterdamStorageSetStateGas (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamStorageSetStateGas ++ "\n"

/-- Assembly `li` helper for the new-account intrinsic state gas constant. -/
def liAmsterdamNewAccountStateGas (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamNewAccountStateGas ++ "\n"

/-- Assembly `li` helper for the per-authorization intrinsic state gas constant. -/
def liAmsterdamAuthStateGas (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamAuthStateGas ++ "\n"

/-- Assembly `li` helper for the system transaction regular gas budget. -/
def liAmsterdamSystemTransactionGas (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamSystemTransactionGas ++ "\n"

/-- Assembly `li` helper for the system transaction state-gas reservoir. -/
def liAmsterdamSystemStateGasReservoir (reg : String) : String :=
  "  li " ++ reg ++ ", " ++ toString amsterdamSystemStateGasReservoir ++ "\n"

#guard amsterdamStorageSetStateGas = 97920
#guard amsterdamNewAccountStateGas = 183600
#guard amsterdamAuthStateGas = 218790
#guard amsterdamSystemStateGasReservoir = 1566720

end EvmAsm.Codegen
