/-
  EvmAsm.Codegen.GuestLayoutInstance

  GH #10753 — the concrete binding of `GuestLayout` to the generated
  `GuestAddrs` table.  This is the ONLY module on the layout-parameterised
  path that imports `EvmAsm.Codegen.GuestAddrs`: flipping an address in the
  table rebuilds this module and the bridge modules that apply
  `guestLayout`, and nothing else (the leaf `_prog_of` definitions are
  parameterised and their oleans are unchanged).

  Drift-proof by construction: every field is bound FROM `GuestAddrs`, so
  the instance can never disagree with the table; a missing field is a
  compile error in the referencing leaf.  Hand-written for now; the intent
  is for `scripts/asm_to_program.py` to emit this file from the same
  fixture scan that emits `GuestAddrs.lean` once the converted set is
  large enough to make hand-maintenance the drift risk.
-/

import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.GuestLayout

namespace EvmAsm.Codegen

def guestLayout : GuestLayout :=
  { sha256_w_state := GuestAddrs.sha256_w_state
    sha256_w_input := GuestAddrs.sha256_w_input
    sha256_w_iv := GuestAddrs.sha256_w_iv
    sha256_w_params := GuestAddrs.sha256_w_params
    zkvm_sha256 := GuestAddrs.zkvm_sha256
    zk3_state := GuestAddrs.zk3_state
    zkvm_keccak256 := GuestAddrs.zkvm_keccak256
    zkvm_keccak256_segments := GuestAddrs.zkvm_keccak256_segments
    bav_hash := GuestAddrs.bav_hash
    bloom_add_value := GuestAddrs.bloom_add_value }

end EvmAsm.Codegen
