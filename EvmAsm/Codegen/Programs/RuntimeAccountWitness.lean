/-
  EvmAsm.Codegen.Programs.RuntimeAccountWitness

  Probes for the runtime dispatcher's account-witness input context.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmOpcodes
import EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/--
Runtime-layout probe for the shared account-witness context.

Input is the normal `scripts/pack-bytecode.py` runtime bytecode payload. The
bytecode segment is interpreted as the 20-byte address to query. The probe runs
the same setup code as `runtime_dispatcher`, then calls
`extcodehash_at_header_state_root` with that address and the parent-header /
witness.state pointers that setup stored in `evm_env`. This validates the
reusable context without changing any opcode handler wiring.

Output:
  bytes  0.. 8 : helper status
  bytes  8..40 : EXTCODEHASH result
-/
def runtimeAccountWitnessExtcodehashPrologue : String :=
  emitRuntimeDispatcherSetup ++ "
" ++
  "  ld a0, 576(x20)
" ++       -- header ptr
  "  ld a1, 584(x20)
" ++       -- header len
  "  beqz a1, .Lraw_ech_no_context
" ++
  "  mv a2, x21
" ++       -- address ptr: bytecode segment payload
  "  ld a3, 592(x20)
" ++       -- witness.state ptr
  "  ld a4, 600(x20)
" ++       -- witness.state len
  "  li a5, 0xa0010008
" ++     -- output hash
  "  jal ra, extcodehash_at_header_state_root
" ++
  "  li t0, 0xa0010000
" ++
  "  sd a0, 0(t0)
" ++
  "  j .Lraw_ech_done
" ++
  ".Lraw_ech_no_context:
" ++
  "  li t0, 0xa0010000
" ++
  "  sd zero, 0(t0)
" ++
  "  sd zero, 8(t0)
" ++
  "  sd zero, 16(t0)
" ++
  "  sd zero, 24(t0)
" ++
  "  sd zero, 32(t0)
" ++
  "  j .Lraw_ech_done
" ++
  zkvmKeccak256Function ++ "
" ++
  witnessLookupByHashFunction ++ "
" ++
  rlpListNthItemFunction ++ "
" ++
  mptNodeKindFunction ++ "
" ++
  mptBranchChildFunction ++ "
" ++
  hpDecodeNibblesFunction ++ "
" ++
  bytesToNibblesFunction ++ "
" ++
  mptWalkFunction ++ "
" ++
  mptLookupByKeyFunction ++ "
" ++
  accountDecodeFunction ++ "
" ++
  accountAtAddressFunction ++ "
" ++
  headerExtractStateRootFunction ++ "
" ++
  extcodehashAtHeaderStateRootFunction ++ "
" ++
  runtimeAccessAccountSeedFunction ++ "
" ++
  runtimeAccessSeedInitialAccountsFunction ++ "
" ++
  ".exit_outofgas:
  j .Lraw_ech_done
" ++
  ".Lraw_ech_done:"


/-- Minimal `.data` section for runtime account-witness probes.

This mirrors the runtime dispatcher's context-carrying data without emitting a
jump table, so the probe can link without opcode handler labels. -/
def runtimeAccountWitnessProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 624\n" ++
  ".balign 8\n" ++
  "evm_blob_hashes:\n" ++
  "  .zero 512\n" ++
  ".balign 8\n" ++
  "evm_block_hashes:\n" ++
  "  .zero 8192\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 262144\n" ++   -- 6c7v9: 1024 × 256-byte LOG event descriptors (was 4096 = 16×256)
  emitPrecompileFrameData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  emitRuntimeAccountWitnessData ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  runtimeAccessSeedScratchLabel ++ ":\n" ++
  "  .zero 32\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++
  "lp64_sp_top:\n"

def runtimeAccountWitnessExtcodehashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeAccountWitnessExtcodehashPrologue
  dataAsm     := runtimeAccountWitnessProbeDataSection
}

/-- Runtime-layout probe for EXTCODECOPY over the shared account-witness
context.

The runtime bytecode segment is interpreted as:
  bytes  0.. 8 : code offset (u64 LE)
  bytes  8..16 : length (u64 LE, <= 256)
  bytes 16..36 : address (20 bytes, natural order)

Output:
  bytes  0.. 8 : helper status
  bytes  8..16 : effective length (= length on success, 0 otherwise)
  bytes 16..   : copied bytes, zero-padded by the helper
-/
def runtimeAccountWitnessExtcodecopyPrologue : String :=
  emitRuntimeDispatcherSetup ++ "
" ++
  "  ld a0, 576(x20)
" ++       -- header ptr
  "  ld a1, 584(x20)
" ++       -- header len
  "  beqz a1, .Lraw_ecc_no_context
" ++
  "  ld t0, 608(x20)
" ++       -- witness.codes ptr
  "  la t1, eccp_codes_ptr
" ++
  "  sd t0, 0(t1)
" ++
  "  ld t0, 616(x20)
" ++       -- witness.codes len
  "  la t1, eccp_codes_len
" ++
  "  sd t0, 0(t1)
" ++
  "  ld a3, 0(x21)
" ++         -- code offset
  "  ld a4, 8(x21)
" ++         -- length
  "  mv s1, a4
" ++             -- save length across helper call
  "  addi a2, x21, 16
" ++      -- address ptr
  "  li a5, 0xa0010010
" ++     -- output bytes
  "  ld a6, 592(x20)
" ++       -- witness.state ptr
  "  ld a7, 600(x20)
" ++       -- witness.state len
  "  jal ra, extcodecopy_at_header_state_root
" ++
  "  li t0, 0xa0010000
" ++
  "  sd a0, 0(t0)
" ++
  "  bnez a0, .Lraw_ecc_no_len
" ++
  "  sd s1, 8(t0)
" ++
  "  j .Lraw_ecc_done
" ++
  ".Lraw_ecc_no_len:
" ++
  "  sd zero, 8(t0)
" ++
  "  j .Lraw_ecc_done
" ++
  ".Lraw_ecc_no_context:
" ++
  "  li t0, 0xa0010000
" ++
  "  sd zero, 0(t0)
" ++
  "  sd zero, 8(t0)
" ++
  "  sd zero, 16(t0)
" ++
  "  sd zero, 24(t0)
" ++
  "  sd zero, 32(t0)
" ++
  "  j .Lraw_ecc_done
" ++
  zkvmKeccak256Function ++ "
" ++
  witnessLookupByHashFunction ++ "
" ++
  rlpListNthItemFunction ++ "
" ++
  mptNodeKindFunction ++ "
" ++
  mptBranchChildFunction ++ "
" ++
  hpDecodeNibblesFunction ++ "
" ++
  bytesToNibblesFunction ++ "
" ++
  mptWalkFunction ++ "
" ++
  mptLookupByKeyFunction ++ "
" ++
  accountDecodeFunction ++ "
" ++
  accountAtAddressFunction ++ "
" ++
  headerExtractStateRootFunction ++ "
" ++
  extcodecopyAtHeaderStateRootFunction ++ "
" ++
  runtimeAccessAccountSeedFunction ++ "
" ++
  runtimeAccessSeedInitialAccountsFunction ++ "
" ++
  ".exit_outofgas:
  j .Lraw_ecc_done
" ++
  ".Lraw_ecc_done:"

def runtimeAccountWitnessExtcodecopyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeAccountWitnessExtcodecopyPrologue
  dataAsm     := runtimeAccountWitnessProbeDataSection
}

end EvmAsm.Codegen
