/-
  EvmAsm.Codegen.Programs.RegistryNames

  CLI-visible program-name list split out of `EvmAsm.Codegen.Programs` so
  the lookup registry can keep shrinking without changing generated names.
-/

import EvmAsm.Codegen.Programs.CryptoRegistry

namespace EvmAsm.Codegen

def knownProgramNames : List String :=
  ["smoke", "evm_add", "evm_div_v5", "evm_mod_v5",
   "evm_sdiv_v5", "input_echo",
   "evm_exp_from_input",
   "evm_add_from_input", "evm_div_v5_from_input", "evm_mod_v5_from_input",
   "evm_sdiv_v5_from_input",
   "evm_smod_v5", "evm_smod_v5_from_input",
   "tiny_interp_add", "tiny_interp_add2",
   "tiny_interp_dispatch_add", "tiny_interp_dispatch_add2",
   "runtime_dispatcher",
   "runtime_dispatcher_call_probe",

   "zisk_runtime_access_list_seeded_sload",
  "stateless_guest"] ++
  knownCryptoProgramNames ++
  [

   "runtime_account_witness_extcodehash",
   "runtime_account_witness_extcodecopy",
   "runtime_create_initcode_frame",
   "runtime_create_initcode_execute",
   "runtime_selfdestruct_eip7708_logs",

   "zisk_step2_verdict",
   "zisk_stateless_verdict",
   "zisk_stateless_verdict_v2",

   ]

end EvmAsm.Codegen
