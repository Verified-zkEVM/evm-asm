/-
  EvmAsm.Codegen.Programs.HashBridge

  Standalone Lean strings for the two host-hash bridge stubs:
  - `zkvm_sha256` — Merkle-Damgård wrapper around ziskemu's SHA-256
                    permutation accelerator
  - `zkvm_keccak256` — sponge wrapper around the Keccak-f[1600]
                    permutation accelerator

  Both are pure-text shims used by every higher-level BuildUnit
  that wants to inline a hash routine. Lifted out of
  `EvmAsm.Codegen.Programs` so SSZ/MPT/state-trie consumers can
  import them without pulling the whole registry hub.

  GH #10753 BRIDGE: the layout-abstract definitions live in the leaf
  `HashBridgeProg`; this module only applies `guestLayout` and re-exposes
  the original `_prog` names and types, so all consumers compile
  untouched.  All `*Function`/`_relocs`/`_eq_prog` declarations remain
  available here transitively via the leaf import.

  The bridge def names are REQUIRED, not just a consumer convenience:
  `check-asm-to-program`'s concrete-render gate looks up
  `emitProgram <camel(entry)>_prog` and ties its immediates to the linked
  image, so the `<name>_prog : Program` surface must exist in this module.
-/

import EvmAsm.Codegen.Programs.HashBridgeProg
import EvmAsm.Codegen.GuestLayoutInstance

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def zkvmSha256_prog : Program := zkvmSha256_prog_of guestLayout

def zkvmKeccak256_prog : Program := zkvmKeccak256_prog_of guestLayout

def zkvmKeccak256Segments_prog : Program := zkvmKeccak256Segments_prog_of guestLayout

end EvmAsm.Codegen
