/-
  EvmAsm.Codegen.GuestLayoutInstance

  Concrete `GuestLayout` built from the generated `GuestAddrs` table.
  Imported only by the top-level assembly / image layer — not by program
  modules (see GH #10753).
-/

import EvmAsm.Codegen.GuestLayout
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

def guestLayout : GuestLayout where
  bav_hash := GuestAddrs.bav_hash
  bloom_add_value := GuestAddrs.bloom_add_value
  zkvm_keccak256 := GuestAddrs.zkvm_keccak256

end EvmAsm.Codegen
