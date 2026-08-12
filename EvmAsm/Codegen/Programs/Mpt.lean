/-
  EvmAsm.Codegen.Programs.Mpt

  Compatibility umbrella for the MPT program definitions.  The definitions
  are split between MptBase and MptTail so each source file stays below the
  Codegen/Programs file-size cap while existing imports keep working.
-/

import EvmAsm.Codegen.Programs.MptStatusVocab
import EvmAsm.Codegen.Programs.MptBase
import EvmAsm.Codegen.Programs.MptTail
