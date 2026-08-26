/- EvmAsm.Codegen.Programs.CryptoRegistry
  Crypto and precompile probe sub-registry for codegen programs.
-/

module

public import EvmAsm.Codegen.Layout
public import EvmAsm.Codegen.Probes.HashProbes

@[expose] public section

namespace EvmAsm.Codegen

/-- Look up standalone crypto/precompile probe programs by CLI name. -/
def lookupCryptoProgram : String → Option BuildUnit
  | "zisk_keccak_probe" => some ziskKeccakProbeUnit
  | _ => none

/-- CLI names hosted by `lookupCryptoProgram`. -/
def knownCryptoProgramNames : List String :=
  ["zisk_keccak_probe"]

end EvmAsm.Codegen
