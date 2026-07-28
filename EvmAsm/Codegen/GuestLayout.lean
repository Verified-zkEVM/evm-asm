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

  `GuestLayout.zero` is the emission-time layout: `emitProgramR` keeps
  `la`/`jal` symbolic via the reloc side-table, so the emitted strings and
  the `#guard` length facts are independent of the actual addresses and are
  stated against the zero layout in the leaves.  The concrete immediates
  are tied to the real link by the bridge and by the
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

/-- The all-zero layout: emission/guard view, never linked against. -/
def GuestLayout.zero : GuestLayout :=
  { sha256_w_state := 0
    sha256_w_input := 0
    sha256_w_iv := 0
    sha256_w_params := 0
    zkvm_sha256 := 0
    zk3_state := 0
    zkvm_keccak256 := 0
    zkvm_keccak256_segments := 0 }

end EvmAsm.Codegen
