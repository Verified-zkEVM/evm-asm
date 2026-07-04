/-
  EvmAsm.Tests

  Umbrella for test/check executables' source modules. These are pure
  Lean defs used by `lake exe` binaries under `Main*.lean` shims; they
  live under `EvmAsm/Tests/` so the file-size / orphan checks see them,
  but they are not consumed by any proof.
-/

import EvmAsm.Tests.Div128V5RandomCheck
import EvmAsm.Tests.ArithDiffCheck
import EvmAsm.Tests.RlpDiffCheck
import EvmAsm.Tests.SpecRefEestCheck
