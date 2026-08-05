/-
  EvmAsm.Codegen.GuestLayout

  GH #10753 — the layout-parameterisation substrate.  `GuestLayout` is the
  abstract view of the guest's link-dependent symbol addresses: converted
  leaf modules (`Programs/<Name>Prog.lean`) define their `_prog_of`
  (L : GuestLayout) against this structure and import NOTHING concrete, so
  a layout change does not rebuild them.  The concrete binding lives in
  exactly one module (`EvmAsm.Codegen.GuestLayoutInstance`), and each
  converted program's application file (`Programs/<Name>.lean`, the bridge)
  re-exposes the original `<name>_prog : Program` as
  `<name>_prog_of guestLayout`, keeping every consumer compiling untouched.

  Field set: grows INCREMENTALLY, one group of fields per converted module
  (this file currently carries exactly the symbols referenced by
  `Programs/HashBridgeProg.lean`).  The measured record (see the issue's
  measurement comment) is that a FLAT structure works at this scale; the
  mega-flat end state (~1125+ fields) fails elaboration and will need
  grouping when we get there.  `GuestLayout` deliberately does NOT import
  `GuestAddrs`: the instance module does that, and is the only module that
  does for this path.

  `GuestLayout.zero` is the emission-time layout: the emitted strings and
  the `#guard` length facts are stated against the zero layout in the
  leaves.  That the emission really is layout-independent is CHECKED, not
  assumed, by two pre-existing gates bounding the claim from opposite
  sides: the emitted-reloc-count check rejects any `la`/`jal` whose target
  got baked from a layout instead of going through the reloc side-table,
  and `assemble_cmp` against the hand-written fixture catches any
  non-`la`/`jal` layout-dependent value (an `li` of an absolute address
  renders as 0 under `.zero` and diverges from the fixture).  The concrete
  immediates are tied to the real link by the bridge and by the
  `check-asm-to-program` concrete-render gate.
-/

namespace EvmAsm.Codegen

structure GuestLayout where
  -- HashBridge (zkvm_sha256 / zkvm_keccak256 / zkvm_keccak256_segments).
  sha256_w_state : Nat
  sha256_w_input : Nat
  sha256_w_iv : Nat
  sha256_w_params : Nat
  zkvm_sha256 : Nat
  zk3_state : Nat
  zkvm_keccak256 : Nat
  zkvm_keccak256_segments : Nat
  -- BloomAddValue (bloom_add_value); `zkvm_keccak256` already above.
  bav_hash : Nat
  bloom_add_value : Nat
  -- U256 (u256_mul_u64_be: accumulator window and entry).
  u256m_acc : Nat
  u256_mul_u64_be : Nat
  -- U256GasPricing (priority_fee_per_gas_eip1559: own entry and the two
  -- helpers it calls).
  priority_fee_per_gas_eip1559 : Nat
  u256_sub_be : Nat
  u256_min : Nat
  -- CallFrameBase (frame_base: arena base + own entry for la PC).
  call_frame_arena : Nat
  frame_base : Nat
  -- MptDeleteWalkDb (tail-call target + own entry for jal PC).
  mpt_set_record_walk_db : Nat
  mpt_delete_walk_db : Nat

/-- The all-zero layout: emission/guard view, never linked against. -/
def GuestLayout.zero : GuestLayout :=
  { sha256_w_state := 0
    sha256_w_input := 0
    sha256_w_iv := 0
    sha256_w_params := 0
    zkvm_sha256 := 0
    zk3_state := 0
    zkvm_keccak256 := 0
    zkvm_keccak256_segments := 0
    bav_hash := 0
    bloom_add_value := 0
    u256m_acc := 0
    u256_mul_u64_be := 0
    priority_fee_per_gas_eip1559 := 0
    u256_sub_be := 0
    u256_min := 0
    call_frame_arena := 0
    frame_base := 0
    mpt_set_record_walk_db := 0
    mpt_delete_walk_db := 0 }

end EvmAsm.Codegen
