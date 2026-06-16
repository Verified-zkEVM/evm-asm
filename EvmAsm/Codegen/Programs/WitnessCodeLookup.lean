/-
  EvmAsm.Codegen.Programs.WitnessCodeLookup

  Independent indexed lookup for witness.codes preimages. This deliberately
  uses code-specific globals so building a code index does not overwrite the
  witness.state index used by MPT/account lookups.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.MptWitnessLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Code-specific variant of `witness_lookup_by_hash`.

    The generated assembler is the existing K19 indexed/linear implementation
    with every state-index global and local label renamed from `widx`/`wlh` to
    `wcidx`/`wclh`, and with public entry points renamed to
    `witness_codes_index_build`, `witness_codes_lookup_by_hash_indexed`, and
    `witness_codes_lookup_by_hash`.

    This keeps state and code indexes live at the same time: a caller can build
    the regular `witness_index_build` for `witness.state`, build
    `witness_codes_index_build` for `witness.codes`, and then route code-hash
    preimage probes through this helper without invalidating state lookups. -/
def witnessCodesLookupByHashFunction : String :=
  (((witnessLookupByHashFunction.replace
      "witness_lookup_by_hash_indexed"
      "witness_codes_lookup_by_hash_indexed").replace
      "witness_lookup_by_hash"
      "witness_codes_lookup_by_hash").replace
      "witness_index_build"
      "witness_codes_index_build").replace
      "widx" "wcidx" |>.replace
      "wlh" "wclh"

/-- `zisk_witness_codes_lookup_by_hash_indexed`: focused probe for the
    independent witness.codes index.

    Input layout matches `zisk_witness_lookup_by_hash_indexed`:
      bytes  0.. 8 : ziskemu metadata
      bytes  8..16 : section_len (u64)
      bytes 16..48 : target_hash (32 bytes)
      bytes 48..56 : lookup mode (0 = matching section, 1 = pointer mismatch)
      bytes 56..   : SSZ `witness.codes` list section

    Output:
      +0  lookup status (0 hit, 1 miss)
      +8  matched element offset within the section
      +16 matched element length
      +24 code-index build status
      +32 state-index enabled flag after code-index build (must remain 1)
      +40 code-index enabled flag
      +48 code-indexed lookup call count
      +56 code-linear lookup call count -/
def ziskWitnessCodesLookupByHashIndexedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld s0, 8(a5)                # section_len\n" ++
  "  addi s1, a5, 16             # target_hash ptr\n" ++
  "  ld s3, 48(a5)               # lookup mode\n" ++
  "  addi s2, a5, 56             # section ptr\n" ++
  "  # Build a tiny ordinary witness.state index first. The code-index build\n" ++
  "  # must not clear or overwrite this state-index enabled flag.\n" ++
  "  la a0, z_wclh_state_section\n" ++
  "  li a1, 5\n" ++
  "  jal ra, witness_index_build\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, witness_codes_index_build\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 24(t0)               # code-index build status\n" ++
  "  la t1, widx_enabled; ld t2, 0(t1); sd t2, 32(t0)\n" ++
  "  la t1, wcidx_enabled; ld t2, 0(t1); sd t2, 40(t0)\n" ++
  "  bnez a0, .Lwclh_probe_done\n" ++
  "  mv a0, s2\n" ++
  "  beqz s3, .Lwclh_probe_lookup_ptr_ready\n" ++
  "  addi a0, s2, 1              # deliberate section mismatch -> linear path\n" ++
  ".Lwclh_probe_lookup_ptr_ready:\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  li a3, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a4, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  sd zero, 0(a4)\n" ++
  "  jal ra, witness_codes_lookup_by_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # lookup status\n" ++
  "  la t1, wclh_indexed_calls; ld t2, 0(t1); sd t2, 48(t0)\n" ++
  "  la t1, wclh_linear_calls; ld t2, 0(t1); sd t2, 56(t0)\n" ++
  ".Lwclh_probe_done:\n" ++
  "  j .Lwclh_probe_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
  ".Lwclh_probe_pdone:"

def ziskWitnessCodesLookupByHashIndexedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  -- One SSZ list entry with a one-byte payload, enough to enable the regular
  -- state index before the code index is built.
  "z_wclh_state_section:\n" ++
  "  .byte 4,0,0,0,0xaa\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  "wclh_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessCodesLookupByHashIndexedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessCodesLookupByHashIndexedPrologue
  dataAsm     := ziskWitnessCodesLookupByHashIndexedDataSection
}

end EvmAsm.Codegen
