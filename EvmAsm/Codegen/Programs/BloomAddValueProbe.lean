/-
  EvmAsm.Codegen.Programs.BloomAddValueProbe

  Probe BuildUnit for `bloom_add_value`. Split from `BloomAddValue` so the
  program module can stay free of `GuestAddrs` (via `HashBridge`) under the
  GH #10753 layout-parameterisation prototype.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BloomAddValue
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `zisk_bloom_add_value`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : value_len
      bytes  8..   : value bytes
    Output layout:
      bytes  0..256 : zero-initialised bloom, then bloom_add_value
                      run once on the supplied value. -/
def ziskBloomAddValuePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a2, 8(a3)                # value_len\n" ++
  "  addi a1, a3, 16             # value ptr\n" ++
  "  li a0, 0xa0010000           # output bloom ptr\n" ++
  "  jal ra, bloom_add_value\n" ++
  "  j .Lbav_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bloomAddValueFunction ++ "\n" ++
  ".Lbav_pdone:"

def ziskBloomAddValueDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bav_hash:\n" ++
  "  .zero 32"

def ziskBloomAddValueProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBloomAddValuePrologue
  dataAsm     := ziskBloomAddValueDataSection
}

end EvmAsm.Codegen
