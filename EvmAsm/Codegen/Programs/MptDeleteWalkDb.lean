/-
  EvmAsm.Codegen.Programs.MptDeleteWalkDb

  DB-aware descent for deleting an existing key from a witness-backed MPT.
  This is the delete-side foundation paired with `mpt_set_record_walk_db`:
  it records the resolved ancestor stack and terminal node using absolute
  pointers, so a later delete accumulator can remove the terminal and bubble
  branch/extension collapse through the shared node DB.

  GH #10753 bridge module: the program itself lives in the leaf
  `MptDeleteWalkDbProg.lean` parameterised over the abstract `GuestLayout`;
  this module applies the concrete `guestLayout` and re-exposes
  `mptDeleteWalkDb_prog` with its original name and type, so every consumer
  (and the concrete-render drift gate, whose key is `emitProgram`
  `mptDeleteWalkDb_prog`) compiles unchanged.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.MptDeleteWalkDbProg
import EvmAsm.Codegen.GuestLayoutInstance
import EvmAsm.Codegen.Programs.MptSetAcc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_delete_walk_db -- DB-aware walk to an existing key.

    ABI:
      a0 = root_hash ptr
      a1 = witness section ptr
      a2 = witness section length
      a3 = path_nibbles ptr
      a4 = path_nibbles length
      a5 = stack_out ptr (32 bytes per ancestor)
      a6 = meta_out ptr
      a0 output = 0 found / 1 not found / 2 parse fail

    `stack_out` and `meta_out` match `mpt_set_record_walk_db`; node pointers
    are absolute, not witness-relative:
      stack[i] = node_ptr_ABS, node_len, kind(0 branch / 1 extension), nibble
      meta     = depth, consumed, terminal_ptr_ABS, terminal_len

    The next primitive (`mpt_delete_acc`) consumes this walk and implements the
    Ethereum delete collapse rules from execution-specs incremental_mpt.py. -/
def mptDeleteWalkDb_prog : Program := mptDeleteWalkDb_prog_of guestLayout

/-- Probe with the same input layout as `zisk_mpt_set_record_walk`.
    Output: status@0, meta@8, stack@128. -/
def ziskMptDeleteWalkDbPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # init node DB empty; later delete-acc tests will exercise DB-resident roots.\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  ld t4, 24(a7)               # value_len (ignored; input layout shared)\n" ++
  "  addi a0, a7, 32             # root_hash ptr\n" ++
  "  addi a3, a7, 64             # path ptr\n" ++
  "  add t3, t5, t4\n" ++
  "  addi t3, t3, 7\n" ++
  "  andi t3, t3, -8\n" ++
  "  add a1, a3, t3              # witness ptr\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010080           # stack_out at OUTPUT+128\n" ++
  "  li a6, 0xa0010008           # meta_out at OUTPUT+8\n" ++
  "  jal ra, mpt_delete_walk_db\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lmdwdb_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptDeleteWalkDbFunction ++ "\n" ++
  ".Lmdwdb_pdone:"

def ziskMptDeleteWalkDbDataSection : String :=
  ziskMptSetAccDataSection

def ziskMptDeleteWalkDbProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptDeleteWalkDbPrologue
  dataAsm     := ziskMptDeleteWalkDbDataSection
}

end EvmAsm.Codegen
