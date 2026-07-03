/-
  EvmAsm.Stateless.SpecRef

  Umbrella for the Lean functional *reference port* of the Amsterdam
  stateless-guest spec (`execution-specs @ tests-zkevm@v0.4.0`), feeder for
  bead `evm-asm-4ch8f.8`. This is a reference model only — no theorems about
  the RV64 guest live here. See `docs/4ch8f-specref-port.md` for the
  Python↔Lean mapping, the execution seam, and reuse notes.

  Module map (mirrors the Python modules):
  * `Crypto`       — full keccak256/sha256 on the ZisK accel permutations
  * `Types`        — the `@dataclass`/`StrEnum` mirrors + `SpecError`
  * `SszCodec`     — generic SSZ serialize / deserialize / hash_tree_root
  * `Ssz`          — `stateless_ssz.py` containers + 34 conversions
  * `WitnessState` — `witness_state.py` (4 module-level defs)
  * `Stateless`    — `stateless.py` (7 defs) + the execution seam
  * `Guest`        — `stateless_guest.py` (3 defs), the top-level shell
-/

import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.Stateless.SpecRef.SszCodec
import EvmAsm.Stateless.SpecRef.Ssz
import EvmAsm.Stateless.SpecRef.WitnessState
import EvmAsm.Stateless.SpecRef.Stateless
import EvmAsm.Stateless.SpecRef.Guest
