/-
  EvmAsm.Codegen.Programs.ChainValidateOfflineAddrs

  Last-linked entry addresses for the three `chain_validate_*` routines
  retired from the guest image in #12351 (uncalled; Progress rows drained).
  Proof modules keep verifying the Program texts offline against these
  ghost bases — they are NOT `GuestAddrs` and must not be re-linked.
-/

namespace EvmAsm.Codegen.ChainValidateOfflineAddrs

/-- Last linked entry of `chain_validate_post_merge_full` before #12351. -/
def chain_validate_post_merge_full : Nat := 0x80002f38
/-- Last linked entry of `chain_validate_increasing_timestamps` before #12351. -/
def chain_validate_increasing_timestamps : Nat := 0x80003604
/-- Last linked entry of `chain_validate_consecutive_numbers` before #12351. -/
def chain_validate_consecutive_numbers : Nat := 0x80003774

end EvmAsm.Codegen.ChainValidateOfflineAddrs
