/- EvmAsm.Codegen.Programs.RegistryNamesTail
  Tail of CLI-visible codegen program names, split out of Programs.lean to
  keep the registry hub below the file-size pressure line.
-/
import EvmAsm.Codegen.Programs.RegistryReceipts

namespace EvmAsm.Codegen

/-- Tail of known codegen program names appended by `knownProgramNames`. -/
def knownProgramNamesTail : List String :=
  knownReceiptProgramNamesTail ++
  [

                                                    "zisk_create_code_effect_log",       "zisk_nonstorage_effect_log",  "zisk_mtx_committed_chunked_snapshot_upsert", "zisk_mtx_committed_chunked_latest_value", "zisk_mtx_committed_block_verdict_threading",                  "zisk_bal_serializer_measure", "zisk_bal_selftests",

   ]

end EvmAsm.Codegen
