/-
  EvmAsm.Stateless.SpecRef

  Umbrella for the Lean functional *reference port* of the Amsterdam
  stateless-guest spec (`execution-specs @ tests-zkevm@v0.4.0`), feeder for
  bead `evm-asm-4ch8f.8`. This is a reference model only — no theorems about
  the RV64 guest live here. See `docs/4ch8f-specref-port.md` for the
  Python↔Lean mapping, the execution seam, and reuse notes.

  Module map (mirrors the Python modules):
  * `Crypto`       — full keccak256/sha256 on the ZisK accel permutations
  * `Secp256k1Recover` — the project-side ECDSA recovery reference
                     (execution-specs delegates to native coincurve; 4ch8f.38.1)
  * `Runtime`      — `vm/runtime.py` (`get_valid_jump_destinations`)
  * `Types`        — the `@dataclass`/`StrEnum` mirrors + `SpecError`
  * `SszCodec`     — generic SSZ serialize / deserialize / hash_tree_root
  * `Ssz`          — `stateless_ssz.py` containers + 34 conversions
  * `WitnessState` — `witness_state.py` (4 module-level defs)
  * `IncrementalMpt` — `incremental_mpt.py` read side (`decode_witness_to_mpt`
                     + helpers): MPT witness authentication (obligation #7)
  * `Stateless`    — `stateless.py` (7 defs) + the execution seam
  * `Guest`        — `stateless_guest.py` (3 defs), the top-level shell
-/

import EvmAsm.Stateless.SpecRef.Crypto
import EvmAsm.Stateless.SpecRef.Runtime
import EvmAsm.Stateless.SpecRef.Secp256k1Recover
import EvmAsm.Stateless.SpecRef.Types
import EvmAsm.Stateless.SpecRef.SszCodec
import EvmAsm.Stateless.SpecRef.Ssz
import EvmAsm.Stateless.SpecRef.WitnessState
import EvmAsm.Stateless.SpecRef.IncrementalMpt
import EvmAsm.Stateless.SpecRef.Stateless
import EvmAsm.Stateless.SpecRef.Guest
