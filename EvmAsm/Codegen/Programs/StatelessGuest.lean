/- EvmAsm.Codegen.Programs.StatelessGuest

  BuildUnit wrapper for the stateless guest entrypoint.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.StatelessVerdict
/-
  EvmAsm.Codegen.Programs.StatelessGuest

  BuildUnit wiring for the stateless guest body, epilogue, and data section.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.StatelessGuestData
import EvmAsm.Codegen.Programs.StatelessGuestEpilogue
import EvmAsm.Codegen.Programs.BlockVerdictV2
import EvmAsm.Stateless.Entry

namespace EvmAsm.Codegen

/-! ## stateless_guest body -- PR-K5 keccak hash field

    Replaces the zero-stub `new_payload_request_root` field in
    `Stateless.Entry.run_stateless_guest`'s SSZ output with the
    keccak256 of the entire SSZ-input byte string the host
    streamed in via `ziskemu -i`. Concretely:

    - Body: the unchanged `Stateless.Entry.run_stateless_guest`
      Program. It writes:
        bytes  0..32 : zero hash (placeholder)
        byte      32 : successful_validation (PR4/PR5 derived)
        bytes 33..41 : chain_id (PR3 from-decode)
        bytes 41..48 : zero gap
        bytes 48..56 : header_count diagnostic (PR6 from-decode)
    - Epilogue (raw asm): set up sp, load (data ptr, len) from
      INPUT_ADDR + (16, 8), set output = OUTPUT_ADDR + 0, and
      `jal ra, zkvm_keccak256`. The function overwrites
      OUTPUT[0..32] with keccak256(input bytes), clobbering the
      zero stub.

    The host-side `compute_new_payload_request_root` per the spec
    is SSZ `hash_tree_root` (SHA-256), not Keccak. PR-K5 stamps a
    *content-dependent* hash there so the test harness has a
    non-trivial value to verify and the keccak bridge is wired
    into the encoder pipeline end-to-end. Once PR-S series lands,
    the SHA-256 hash_tree_root replaces this keccak. -/

/-- Stateless guest program with the codegen epilogue and guest data section. -/
def statelessGuestUnit : BuildUnit := {
  body        := EvmAsm.Stateless.run_stateless_guest
  epilogueAsm := statelessGuestEpilogue
  -- guest scratch + the Step-2 verdict's data (zk3_state / rfu_* are dedup'd out
  -- of the guest section since the appended verdict section provides them).
  dataAsm     := statelessGuestDataSection ++ "\n" ++ statelessVerdictV2GuestData
}

end EvmAsm.Codegen
