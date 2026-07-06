/-
  EvmAsm.Codegen.Programs.StateCompose

  Composite state-proof programs carved out of `State.lean` to
  keep that file under the hard-cap line limit. Imports `State`
  so it can reference the string-constant helpers defined there.
-/
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.WitnessCodeLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program
/-! ## validate_witness_state_contains_root

    Compose `header_extract_state_root` (K201) and
    `witness_lookup_by_hash` (K19) into a single composite:
    given a parent header RLP and an SSZ `witness.state` list
    section, find the node in the section whose `keccak256`
    matches the header's `state_root` field.

    Second step in the storage-proof top-down walk: a previous
    composite verified a caller-supplied root node directly;
    THIS one searches the whole witness for it. On the spec
    side this is what `run_stateless_guest` does between the
    header walk and `apply_body` -- it can only descend the
    trie once the root node has been located in
    `witness.state`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : SSZ list section ptr (witness.state shape)
      a3 (input)  : section_len
      a4 (input)  : u64 out ptr (matched entry offset within
                    section; meaningful only on hit)
      a5 (input)  : u64 out ptr (matched entry length;
                    meaningful only on hit)
      ra (input)  : return
      a0 (output) : 0 on hit, 1 on miss,
                    2 on header parse/size fail
-/
def validateWitnessStateContainsRootFunction : String :=
  "validate_witness_state_contains_root:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_rlp_len\n" ++
  "  mv s2, a2                  # section ptr\n" ++
  "  mv s3, a3                  # section_len\n" ++
  "  mv s4, a4                  # out_offset ptr\n" ++
  "  mv s5, a5                  # out_length ptr\n" ++
  "  # Step 1: header.state_root -> vwsc_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vwsc_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lvwsc_step2\n" ++
  "  li a0, 2\n" ++
  "  j .Lvwsc_ret\n" ++
  ".Lvwsc_step2:\n" ++
  "  # Step 2: witness_lookup_by_hash(section, target=state_root).\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, vwsc_state_root\n" ++
  "  mv a3, s4\n" ++
  "  mv a4, s5\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  # a0 already holds 0 (hit) or 1 (miss).\n" ++
  ".Lvwsc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_validate_witness_state_contains_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len (u64)
      bytes 16..24 : state_section_len (u64)
      bytes 24..24+H            : header_rlp
      bytes 24+H..24+H+S        : witness.state SSZ list bytes
    Output layout:
      bytes  0.. 8 : status (0 hit / 1 miss / 2 parse_fail)
      bytes  8..16 : matched entry offset (u64; on hit)
      bytes 16..24 : matched entry length (u64; on hit) -/
def ziskValidateWitnessStateContainsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)               # state_section_len\n" ++
  "  addi a0, a7, 24             # header_rlp ptr\n" ++
  "  add a2, a0, a1              # section ptr = header_end\n" ++
  "  li a4, 0xa0010008           # out_offset (OUTPUT + 8)\n" ++
  "  li a5, 0xa0010010           # out_length (OUTPUT + 16)\n" ++
  "  # Pre-zero so non-hits surface as zeros.\n" ++
  "  sd zero, 0(a4)\n" ++
  "  sd zero, 0(a5)\n" ++
  "  jal ra, validate_witness_state_contains_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lvwsc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  validateWitnessStateContainsRootFunction ++ "\n" ++
  ".Lvwsc_pdone:"

def ziskValidateWitnessStateContainsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "vwsc_state_root:\n" ++
  "  .zero 32"

def ziskValidateWitnessStateContainsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateWitnessStateContainsRootPrologue
  dataAsm     := ziskValidateWitnessStateContainsRootDataSection
}

/-! ## validate_state_root_against_witness_node

    First-step storage-proof verification: confirm that the
    keccak256 of a witness state-trie root node matches the
    `state_root` field of a parent header.

    Composes two existing primitives:
      - `header_extract_state_root` (K201): pulls `state_root`
        (field 3, Bytes32) from an RLP-encoded amsterdam Header.
      - `zkvm_keccak256`: computes the keccak256 of the witness
        state-trie root node bytes.

    Then byte-compares the two 32-byte digests.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : state_node_ptr (raw witness MPT-node bytes)
      a3 (input)  : state_node byte length
      ra (input)  : return
      a0 (output) :
        0 : match -- keccak256(state_node) == header.state_root
        1 : mismatch
        2 : header parse failure / wrong state_root field length

    Scratch: `vsraw_state_root` (32 B), `vsraw_keccak` (32 B). -/
def validateStateRootAgainstWitnessNodeFunction : String :=
  "validate_state_root_against_witness_node:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                  # s0 = header_rlp ptr\n" ++
  "  mv s1, a1                  # s1 = header_rlp len\n" ++
  "  mv s2, a2                  # s2 = state_node ptr\n" ++
  "  mv s3, a3                  # s3 = state_node len\n" ++
  "  # Step 1: extract header.state_root -> vsraw_state_root.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, vsraw_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  beqz a0, .Lvsraw_step2\n" ++
  "  li a0, 2\n" ++
  "  j .Lvsraw_ret\n" ++
  ".Lvsraw_step2:\n" ++
  "  # Step 2: keccak256(state_node) -> vsraw_keccak.\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, vsraw_keccak\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  # Step 3: byte-compare the two 32-byte digests.\n" ++
  "  la t0, vsraw_state_root\n" ++
  "  la t1, vsraw_keccak\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvsraw_mismatch\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvsraw_mismatch\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvsraw_mismatch\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvsraw_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Lvsraw_ret\n" ++
  ".Lvsraw_mismatch:\n" ++
  "  li a0, 1\n" ++
  ".Lvsraw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_validate_state_root_against_witness_node`: probe
    BuildUnit. Input layout:
      INPUT[0..8)        : ziskemu metadata (zero)
      INPUT[8..16)       : header_len (u64 LE)
      INPUT[16..24)      : state_node_len (u64 LE)
      INPUT[24..24+H)    : header_rlp bytes (H = header_len)
      INPUT[24+H..)      : state_node bytes (length state_node_len)
    Output:
      OUTPUT[0..8)       : status (0=match, 1=mismatch, 2=parse fail). -/
def ziskValidateStateRootAgainstWitnessNodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_len\n" ++
  "  ld a3, 16(a7)               # state_node_len\n" ++
  "  addi a0, a7, 24             # header_ptr = INPUT + 24\n" ++
  "  add a2, a0, a1              # state_node_ptr = header_ptr + header_len\n" ++
  "  jal ra, validate_state_root_against_witness_node\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvsraw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  validateStateRootAgainstWitnessNodeFunction ++ "\n" ++
  ".Lvsraw_pdone:"

def ziskValidateStateRootAgainstWitnessNodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "vsraw_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "vsraw_keccak:\n" ++
  "  .zero 32"

def ziskValidateStateRootAgainstWitnessNodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateStateRootAgainstWitnessNodePrologue
  dataAsm     := ziskValidateStateRootAgainstWitnessNodeDataSection
}


/-! ## account_at_header_state_root

    Compose `header_extract_state_root` (K201) and
    `account_at_address` (K28) into a single composite: given
    a parent header RLP, an address, and an SSZ `witness.state`
    section, extract the header's `state_root`, then look up
    and decode the account at the given address.

    Third top-down storage-proof step: the prior probes
    handled "verify root node by hash" and "locate root node
    in witness"; this one walks the trie all the way down to
    the account record, the natural unit of state being
    queried in `apply_body`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address bytes ptr
      a3 (input)  : address byte length (typically 20)
      a4 (input)  : witness section ptr
      a5 (input)  : witness section_len
      a6 (input)  : output struct ptr (104 bytes)
      ra (input)  : return
      a0 (output) :
        0 = found and decoded
        1 = not found in trie     (output zeroed)
        2 = mpt_walk parse error  (output zeroed)
        3 = account_decode failure (output zeroed)
        4 = header parse / state_root size fail (output zeroed)

    The 104-byte output struct layout is identical to
    `account_at_address`:
      offset  0..  8 : nonce (u64 LE)
      offset  8.. 40 : balance (u256 BE, left-zero-padded)
      offset 40.. 72 : storage_root (32 B)
      offset 72..104 : code_hash (32 B)
-/
def accountAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.aahsr_state_root (GuestAddrs.account_at_header_state_root + 76)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aahsr_state_root (GuestAddrs.account_at_header_state_root + 76)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.account_at_header_state_root + 84)),
    .BEQ .x10 .x0 (64 : BitVec 13),
    .SD .x22 .x0 (0 : BitVec 12),
    .SD .x22 .x0 (8 : BitVec 12),
    .SD .x22 .x0 (16 : BitVec 12),
    .SD .x22 .x0 (24 : BitVec 12),
    .SD .x22 .x0 (32 : BitVec 12),
    .SD .x22 .x0 (40 : BitVec 12),
    .SD .x22 .x0 (48 : BitVec 12),
    .SD .x22 .x0 (56 : BitVec 12),
    .SD .x22 .x0 (64 : BitVec 12),
    .SD .x22 .x0 (72 : BitVec 12),
    .SD .x22 .x0 (80 : BitVec 12),
    .SD .x22 .x0 (88 : BitVec 12),
    .SD .x22 .x0 (96 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (36 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .AUIPC .x12 (laHi GuestAddrs.aahsr_state_root (GuestAddrs.account_at_header_state_root + 160)),
    .ADDI .x12 .x12 (laLo GuestAddrs.aahsr_state_root (GuestAddrs.account_at_header_state_root + 160)),
    .MV .x13 .x20,
    .MV .x14 .x21,
    .MV .x15 .x22,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.account_at_header_state_root + 180)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accountAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accountAtHeaderStateRoot_relocs : RelocTable :=
  [ (19, .la .x12 "aahsr_state_root"),
    (21, .jal .x1 "header_extract_state_root"),
    (40, .la .x12 "aahsr_state_root"),
    (45, .jal .x1 "account_at_address") ]

def accountAtHeaderStateRootFunction : String :=
  "account_at_header_state_root:\n" ++ emitProgramR accountAtHeaderStateRoot_prog accountAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accountAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accountAtHeaderStateRootFunction_eq_prog :
    accountAtHeaderStateRootFunction = "account_at_header_state_root:\n" ++ emitProgramR accountAtHeaderStateRoot_prog accountAtHeaderStateRoot_relocs := rfl

#guard accountAtHeaderStateRootFunction.startsWith "account_at_header_state_root:\n"
#guard accountAtHeaderStateRoot_prog.length = 57
/-- `zisk_account_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len (u64)
      bytes 16..24 : witness_len (u64)
      bytes 24..32 : addr_len (u64)
      bytes 32..32+H              : header_rlp
      bytes 32+H..32+H+addr_len   : address bytes
      bytes 32+H+addr_len..       : witness section
    Output layout:
      bytes  0.. 8 : status (0/1/2/3/4)
      bytes  8.. 16: nonce
      bytes 16..48 : balance
      bytes 48..80 : storage_root
      bytes 80..112: code_hash -/
def ziskAccountAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # header_rlp_len\n" ++
  "  ld t5, 16(a7)               # witness_len\n" ++
  "  ld t4, 24(a7)               # addr_len\n" ++
  "  addi a0, a7, 32             # header_rlp ptr\n" ++
  "  mv a1, t6                   # header_rlp_len\n" ++
  "  add a2, a0, t6              # address ptr = header_end\n" ++
  "  mv a3, t4                   # addr_len\n" ++
  "  add a4, a2, t4              # witness ptr = addr_end\n" ++
  "  mv a5, t5                   # witness_len\n" ++
  "  li a6, 0xa0010008           # output struct at OUTPUT + 8\n" ++
  "  # Pre-zero 104 bytes so a failure surfaces as zeros.\n" ++
  "  sd zero, 0(a6); sd zero, 8(a6); sd zero, 16(a6); sd zero, 24(a6)\n" ++
  "  sd zero, 32(a6); sd zero, 40(a6); sd zero, 48(a6); sd zero, 56(a6)\n" ++
  "  sd zero, 64(a6); sd zero, 72(a6); sd zero, 80(a6); sd zero, 88(a6)\n" ++
  "  sd zero, 96(a6)\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Laahsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  accountAtHeaderStateRootFunction ++ "\n" ++
  ".Laahsr_pdone:"

def ziskAccountAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aahsr_state_root:\n" ++
  "  .zero 32"

def ziskAccountAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountAtHeaderStateRootPrologue
  dataAsm     := ziskAccountAtHeaderStateRootDataSection
}




/-! ## slot_at_header_state_root

    End-to-end storage-slot lookup from a parent header:
    given `(header_rlp, address, slot_idx, witness.state,
    witness.storage)`, extract `state_root` from the header,
    walk down to the account leaf in `witness.state`, then walk
    the per-account storage trie in `witness.storage` down to
    the requested slot and decode it as a u256.

    Fourth top-down storage-proof step. Each prior PR moved one
    level deeper:
      1. verify a caller-supplied root node directly against
         `header.state_root`
      2. locate the root node in `witness.state` by hash
      3. walk down to the account leaf
      4. (this PR) walk down again to a storage slot value

    Calling convention (8 args, fits in a0..a7):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : slot_idx ptr (32-byte BE u256)
      a4 (input)  : witness.state ptr
      a5 (input)  : witness.state len
      a6 (input)  : witness.storage ptr
      a7 (input)  : witness.storage len
      ra (input)  : return

      a0 (output) : unified status
        0 = found + decoded
        1 = account not in state trie
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = slot not in storage trie
        6 = storage-trie mpt parse error
        7 = slot RLP decode failure

    The 32-byte slot value (u256, big-endian) is written to
    `sahsr_u256` -- the probe BuildUnit copies it to OUTPUT.
-/
def slotAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .SD .x2 .x24 (72 : BitVec 12),
    .SD .x2 .x25 (80 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x23 .x17,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.sahsr_state_root (GuestAddrs.slot_at_header_state_root + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sahsr_state_root (GuestAddrs.slot_at_header_state_root + 88)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.slot_at_header_state_root + 96)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (96 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.sahsr_state_root (GuestAddrs.slot_at_header_state_root + 120)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sahsr_state_root (GuestAddrs.slot_at_header_state_root + 120)),
    .MV .x13 .x20,
    .MV .x14 .x21,
    .AUIPC .x15 (laHi GuestAddrs.sahsr_acct_struct (GuestAddrs.slot_at_header_state_root + 136)),
    .ADDI .x15 .x15 (laLo GuestAddrs.sahsr_acct_struct (GuestAddrs.slot_at_header_state_root + 136)),
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.slot_at_header_state_root + 144)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .JAL .x0 (52 : BitVec 21),
    .MV .x10 .x19,
    .LI .x11 (32 : Word),
    .AUIPC .x12 (laHi GuestAddrs.sahsr_acct_struct (GuestAddrs.slot_at_header_state_root + 164)),
    .ADDI .x12 .x12 (laLo GuestAddrs.sahsr_acct_struct (GuestAddrs.slot_at_header_state_root + 164)),
    .ADDI .x12 .x12 (40 : BitVec 12),
    .MV .x13 .x22,
    .MV .x14 .x23,
    .AUIPC .x15 (laHi GuestAddrs.sahsr_u256 (GuestAddrs.slot_at_header_state_root + 184)),
    .ADDI .x15 .x15 (laLo GuestAddrs.sahsr_u256 (GuestAddrs.slot_at_header_state_root + 184)),
    .JAL .x1 (jalOff GuestAddrs.slot_at_index (GuestAddrs.slot_at_header_state_root + 192)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .ADDI .x10 .x10 (4 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .LD .x25 .x2 (80 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `slotAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def slotAtHeaderStateRoot_relocs : RelocTable :=
  [ (22, .la .x12 "sahsr_state_root"),
    (24, .jal .x1 "header_extract_state_root"),
    (30, .la .x12 "sahsr_state_root"),
    (34, .la .x15 "sahsr_acct_struct"),
    (36, .jal .x1 "account_at_address"),
    (41, .la .x12 "sahsr_acct_struct"),
    (46, .la .x15 "sahsr_u256"),
    (48, .jal .x1 "slot_at_index") ]

def slotAtHeaderStateRootFunction : String :=
  "slot_at_header_state_root:\n" ++ emitProgramR slotAtHeaderStateRoot_prog slotAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `slotAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem slotAtHeaderStateRootFunction_eq_prog :
    slotAtHeaderStateRootFunction = "slot_at_header_state_root:\n" ++ emitProgramR slotAtHeaderStateRoot_prog slotAtHeaderStateRoot_relocs := rfl

#guard slotAtHeaderStateRootFunction.startsWith "slot_at_header_state_root:\n"
#guard slotAtHeaderStateRoot_prog.length = 64
/-- `zisk_slot_at_header_state_root`: probe BuildUnit.

    Input layout at INPUT_ADDR:
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_storage_len (u64 LE)
      bytes 32..64 : slot_idx (32-byte BE u256)
      bytes 64..84 : address (20 bytes)
      bytes 84..84+H              : header_rlp
      bytes 84+H..84+H+WS         : witness.state
      bytes 84+H+WS..84+H+WS+WTG  : witness.storage

    Output layout at OUTPUT_ADDR:
      bytes  0.. 8 : status (0..7, see function comment)
      bytes  8..40 : slot value (u256 big-endian; zero on failure) -/
def ziskSlotAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t1, 0x40000000           # input base\n" ++
  "  ld t2, 8(t1)                # header_rlp_len\n" ++
  "  ld t3, 16(t1)               # witness_state_len\n" ++
  "  ld t4, 24(t1)               # witness_storage_len\n" ++
  "  addi a3, t1, 32             # slot_idx ptr (32 B)\n" ++
  "  addi a2, t1, 64             # address ptr (20 B)\n" ++
  "  addi a0, t1, 84             # header_rlp ptr\n" ++
  "  mv a1, t2                   # header_rlp_len\n" ++
  "  add a4, a0, t2              # witness.state ptr = header_end\n" ++
  "  mv a5, t3                   # witness_state_len\n" ++
  "  add a6, a4, t3              # witness.storage ptr = state_end\n" ++
  "  mv a7, t4                   # witness_storage_len\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  # Copy sahsr_u256 (32 B) to OUTPUT + 8.\n" ++
  "  la t1, sahsr_u256\n" ++
  "  ld t2,  0(t1); sd t2,  8(t0)\n" ++
  "  ld t2,  8(t1); sd t2, 16(t0)\n" ++
  "  ld t2, 16(t1); sd t2, 24(t0)\n" ++
  "  ld t2, 24(t1); sd t2, 32(t0)\n" ++
  "  j .Lsahsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  slotAtHeaderStateRootFunction ++ "\n" ++
  ".Lsahsr_pdone:"

def ziskSlotAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "si_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "sahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "sahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 32\n" ++
  "sahsr_u256:\n" ++
  "  .zero 32"

def ziskSlotAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSlotAtHeaderStateRootPrologue
  dataAsm     := ziskSlotAtHeaderStateRootDataSection
}



/-! ## code_at_header_state_root

    Sibling of `slot_at_header_state_root`, but on the code-hash
    side of the account record.

    Given `(header_rlp, address, witness.state, witness.codes)`,
    extract `state_root` from the header, walk the state trie to
    the account leaf, decode the four account fields, then look
    up the account's `code_hash` in the `witness.codes` SSZ list
    via `witness_codes_lookup_by_hash`.

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, and the code-specific K19 `witness_codes_lookup_by_hash`.

    Calling convention (7 args, fits in a0..a6):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : witness.codes ptr
      a6 (input)  : witness.codes len
      ra (input)  : return

      a0 (output) : unified status
        0 = found in both state-trie and codes-section
        1 = account not in state trie
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = code_hash not found in witness.codes

    On a hit, the matched code entry's offset/length within the
    codes section are written to `cahsr_code_offset` /
    `cahsr_code_length`; the probe BuildUnit copies them to
    OUTPUT.
-/
def codeAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.cahsr_state_root (GuestAddrs.code_at_header_state_root + 76)),
    .ADDI .x12 .x12 (laLo GuestAddrs.cahsr_state_root (GuestAddrs.code_at_header_state_root + 76)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.code_at_header_state_root + 84)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (96 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.cahsr_state_root (GuestAddrs.code_at_header_state_root + 108)),
    .ADDI .x12 .x12 (laLo GuestAddrs.cahsr_state_root (GuestAddrs.code_at_header_state_root + 108)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x15 (laHi GuestAddrs.cahsr_acct_struct (GuestAddrs.code_at_header_state_root + 124)),
    .ADDI .x15 .x15 (laLo GuestAddrs.cahsr_acct_struct (GuestAddrs.code_at_header_state_root + 124)),
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.code_at_header_state_root + 132)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .JAL .x0 (52 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .AUIPC .x12 (laHi GuestAddrs.cahsr_acct_struct (GuestAddrs.code_at_header_state_root + 152)),
    .ADDI .x12 .x12 (laLo GuestAddrs.cahsr_acct_struct (GuestAddrs.code_at_header_state_root + 152)),
    .ADDI .x12 .x12 (72 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.cahsr_code_offset (GuestAddrs.code_at_header_state_root + 164)),
    .ADDI .x13 .x13 (laLo GuestAddrs.cahsr_code_offset (GuestAddrs.code_at_header_state_root + 164)),
    .AUIPC .x14 (laHi GuestAddrs.cahsr_code_length (GuestAddrs.code_at_header_state_root + 172)),
    .ADDI .x14 .x14 (laLo GuestAddrs.cahsr_code_length (GuestAddrs.code_at_header_state_root + 172)),
    .JAL .x1 (jalOff GuestAddrs.witness_codes_lookup_by_hash (GuestAddrs.code_at_header_state_root + 180)),
    .BEQ .x10 .x0 (8 : BitVec 13),
    .LI .x10 (5 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `codeAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def codeAtHeaderStateRoot_relocs : RelocTable :=
  [ (19, .la .x12 "cahsr_state_root"),
    (21, .jal .x1 "header_extract_state_root"),
    (27, .la .x12 "cahsr_state_root"),
    (31, .la .x15 "cahsr_acct_struct"),
    (33, .jal .x1 "account_at_address"),
    (38, .la .x12 "cahsr_acct_struct"),
    (41, .la .x13 "cahsr_code_offset"),
    (43, .la .x14 "cahsr_code_length"),
    (45, .jal .x1 "witness_codes_lookup_by_hash") ]

def codeAtHeaderStateRootFunction : String :=
  "code_at_header_state_root:\n" ++ emitProgramR codeAtHeaderStateRoot_prog codeAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `codeAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem codeAtHeaderStateRootFunction_eq_prog :
    codeAtHeaderStateRootFunction = "code_at_header_state_root:\n" ++ emitProgramR codeAtHeaderStateRoot_prog codeAtHeaderStateRoot_relocs := rfl

#guard codeAtHeaderStateRootFunction.startsWith "code_at_header_state_root:\n"
#guard codeAtHeaderStateRoot_prog.length = 59
/-- `zisk_code_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len     (u64 LE)
      bytes 16..24 : witness_state_len  (u64 LE)
      bytes 24..32 : witness_codes_len  (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..52+H              : header_rlp
      bytes 52+H..52+H+WS         : witness.state
      bytes 52+H+WS..             : witness.codes
    Output layout:
      bytes  0.. 8 : status (0..5)
      bytes  8..16 : matched code offset within codes section (on hit)
      bytes 16..24 : matched code length (on hit) -/
def ziskCodeAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # header_rlp_len\n" ++
  "  ld s2, 16(s0)               # witness_state_len\n" ++
  "  ld s3, 24(s0)               # witness_codes_len\n" ++
  "  addi s4, s0, 52             # header_rlp ptr\n" ++
  "  add s5, s4, s1              # witness.state ptr\n" ++
  "  add s6, s5, s2              # witness.codes ptr\n" ++
  "  mv a0, s6; mv a1, s3; jal ra, witness_codes_index_build\n" ++
  "  mv a0, s4                   # header_rlp ptr\n" ++
  "  mv a1, s1                   # header_rlp_len\n" ++
  "  addi a2, s0, 32             # address ptr (20 B)\n" ++
  "  mv a3, s5                   # witness.state ptr\n" ++
  "  mv a4, s2                   # witness_state_len\n" ++
  "  mv a5, s6                   # witness.codes ptr\n" ++
  "  mv a6, s3                   # witness_codes_len\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  # Copy cahsr_code_offset / cahsr_code_length to OUTPUT + 8/+16.\n" ++
  "  la t1, cahsr_code_offset; ld t2, 0(t1); sd t2,  8(t0)\n" ++
  "  la t1, cahsr_code_length; ld t2, 0(t1); sd t2, 16(t0)\n" ++
  "  j .Lcahsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  codeAtHeaderStateRootFunction ++ "\n" ++
  ".Lcahsr_pdone:"

def ziskCodeAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  "wclh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "cahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "cahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "cahsr_code_offset:\n" ++
  "  .zero 8\n" ++
  "cahsr_code_length:\n" ++
  "  .zero 8"

def ziskCodeAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCodeAtHeaderStateRootPrologue
  dataAsm     := ziskCodeAtHeaderStateRootDataSection
}

/-! ## extcodesize_at_header_state_root  (EVM EXTCODESIZE opcode)

    Witness-side implementation of the EVM `EXTCODESIZE` opcode.
    Given a parent header RLP, an address, and the SSZ
    `witness.state` and `witness.codes` sections, return the
    u64 byte length an `EXTCODESIZE(addr)` frame would push.

    EXTCODESIZE semantics (per the execution spec):
      * 0 if the account doesn't exist
      * 0 if the account has `code_hash == EMPTY_CODE_HASH`
        (no code; no codes-section lookup needed)
      * `len(witness.codes[i])` where node `i` is the entry whose
        `keccak256` matches `account.code_hash`

    Distinct from PR-K? `code_at_header_state_root` (which
    returns the code's offset/length without applying the
    empty-code rule) and PR-K? `extcodehash_at_header_state_root`
    (which returns the hash, with EIP-1052's empty-account zero
    rule).

    Composes K201 `header_extract_state_root`, K28
    `account_at_address`, code-specific K19 `witness_codes_lookup_by_hash`, and an
    inline 4 x u64 compare against the pre-baked
    `EMPTY_CODE_HASH` constant.

    Calling convention (7 args, fits in a0..a6):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : witness.state ptr
      a4 (input)  : witness.state len
      a5 (input)  : witness.codes ptr
      a6 (input)  : witness.codes len
      ra (input)  : return

      a0 (output) :
        0 = success (`ecsahsr_code_len` holds the code length;
            may be 0 for missing/empty)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = code_hash != EMPTY but not found in witness.codes
            (witness integrity violation)

    The probe BuildUnit copies `ecsahsr_code_len` to OUTPUT + 8.
-/
def extcodesizeAtHeaderStateRoot_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .MV .x22 .x16,
    .AUIPC .x5 (laHi GuestAddrs.ecsahsr_code_len (GuestAddrs.extcodesize_at_header_state_root + 68)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecsahsr_code_len (GuestAddrs.extcodesize_at_header_state_root + 68)),
    .SD .x5 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.ecsahsr_state_root (GuestAddrs.extcodesize_at_header_state_root + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ecsahsr_state_root (GuestAddrs.extcodesize_at_header_state_root + 88)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.extcodesize_at_header_state_root + 96)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (184 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.ecsahsr_state_root (GuestAddrs.extcodesize_at_header_state_root + 120)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ecsahsr_state_root (GuestAddrs.extcodesize_at_header_state_root + 120)),
    .MV .x13 .x19,
    .MV .x14 .x20,
    .AUIPC .x23 (laHi GuestAddrs.ecsahsr_acct_struct (GuestAddrs.extcodesize_at_header_state_root + 136)),
    .ADDI .x23 .x23 (laLo GuestAddrs.ecsahsr_acct_struct (GuestAddrs.extcodesize_at_header_state_root + 136)),
    .MV .x15 .x23,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.extcodesize_at_header_state_root + 148)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (128 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (120 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.ecsahsr_empty_code_hash (GuestAddrs.extcodesize_at_header_state_root + 176)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecsahsr_empty_code_hash (GuestAddrs.extcodesize_at_header_state_root + 176)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x23 (72 : BitVec 12),
    .BNE .x6 .x7 (48 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x23 (80 : BitVec 12),
    .BNE .x6 .x7 (36 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x23 (88 : BitVec 12),
    .BNE .x6 .x7 (24 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x23 (96 : BitVec 12),
    .BNE .x6 .x7 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (56 : BitVec 21),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .ADDI .x12 .x23 (72 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.ecsahsr_dummy_offset (GuestAddrs.extcodesize_at_header_state_root + 252)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ecsahsr_dummy_offset (GuestAddrs.extcodesize_at_header_state_root + 252)),
    .AUIPC .x14 (laHi GuestAddrs.ecsahsr_code_len (GuestAddrs.extcodesize_at_header_state_root + 260)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ecsahsr_code_len (GuestAddrs.extcodesize_at_header_state_root + 260)),
    .JAL .x1 (jalOff GuestAddrs.witness_codes_lookup_by_hash (GuestAddrs.extcodesize_at_header_state_root + 268)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.ecsahsr_code_len (GuestAddrs.extcodesize_at_header_state_root + 276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecsahsr_code_len (GuestAddrs.extcodesize_at_header_state_root + 276)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LI .x10 (5 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `extcodesizeAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def extcodesizeAtHeaderStateRoot_relocs : RelocTable :=
  [ (17, .la .x5 "ecsahsr_code_len"),
    (22, .la .x12 "ecsahsr_state_root"),
    (24, .jal .x1 "header_extract_state_root"),
    (30, .la .x12 "ecsahsr_state_root"),
    (34, .la .x23 "ecsahsr_acct_struct"),
    (37, .jal .x1 "account_at_address"),
    (44, .la .x5 "ecsahsr_empty_code_hash"),
    (63, .la .x13 "ecsahsr_dummy_offset"),
    (65, .la .x14 "ecsahsr_code_len"),
    (67, .jal .x1 "witness_codes_lookup_by_hash"),
    (69, .la .x5 "ecsahsr_code_len") ]

def extcodesizeAtHeaderStateRootFunction : String :=
  "extcodesize_at_header_state_root:\n" ++ emitProgramR extcodesizeAtHeaderStateRoot_prog extcodesizeAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `extcodesizeAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem extcodesizeAtHeaderStateRootFunction_eq_prog :
    extcodesizeAtHeaderStateRootFunction = "extcodesize_at_header_state_root:\n" ++ emitProgramR extcodesizeAtHeaderStateRoot_prog extcodesizeAtHeaderStateRoot_relocs := rfl

#guard extcodesizeAtHeaderStateRootFunction.startsWith "extcodesize_at_header_state_root:\n"
#guard extcodesizeAtHeaderStateRoot_prog.length = 84
/-- `zisk_extcodesize_at_header_state_root`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_codes_len (u64 LE)
      bytes 32..52 : address (20 bytes)
      bytes 52..52+H              : header_rlp
      bytes 52+H..52+H+WS         : witness.state
      bytes 52+H+WS..             : witness.codes
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4 / 5)
      bytes  8..16 : code length (u64; 0 for missing/empty) -/
def ziskExtcodesizeAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # header_rlp_len\n" ++
  "  ld s2, 16(s0)               # witness_state_len\n" ++
  "  ld s3, 24(s0)               # witness_codes_len\n" ++
  "  addi s4, s0, 52             # header_rlp ptr\n" ++
  "  add s5, s4, s1              # witness.state ptr\n" ++
  "  add s6, s5, s2              # witness.codes ptr\n" ++
  "  mv a0, s6; mv a1, s3; jal ra, witness_codes_index_build\n" ++
  "  mv a0, s4                   # header_rlp ptr\n" ++
  "  mv a1, s1                   # header_rlp_len\n" ++
  "  addi a2, s0, 32             # address ptr\n" ++
  "  mv a3, s5                   # witness.state ptr\n" ++
  "  mv a4, s2                   # witness_state_len\n" ++
  "  mv a5, s6                   # witness.codes ptr\n" ++
  "  mv a6, s3                   # witness_codes_len\n" ++
  "  jal ra, extcodesize_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  # Copy ecsahsr_code_len to OUTPUT + 8.\n" ++
  "  la t1, ecsahsr_code_len; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  j .Lecsahsr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  extcodesizeAtHeaderStateRootFunction ++ "\n" ++
  ".Lecsahsr_pdone:"

def ziskExtcodesizeAtHeaderStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "wlh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  "wclh_scratch_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8\n" ++
  "mbc_offset:\n" ++
  "  .zero 8\n" ++
  "mbc_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_lookup_hash:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_lookup_offset:\n" ++
  "  .zero 8\n" ++
  "mw_lookup_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_child_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "mw_path_offset:\n" ++
  "  .zero 8\n" ++
  "mw_path_length:\n" ++
  "  .zero 8\n" ++
  "mw_child_offset:\n" ++
  "  .zero 8\n" ++
  "mw_child_length:\n" ++
  "  .zero 8\n" ++
  "mw_value_offset:\n" ++
  "  .zero 8\n" ++
  "mw_value_length:\n" ++
  "  .zero 8\n" ++
  "mw_nibble_count:\n" ++
  "  .zero 8\n" ++
  "mw_is_leaf:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "mw_nibble_buf:\n" ++
  "  .zero 128\n" ++
  ".balign 32\n" ++
  "mlk_keccak_buf:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "mlk_nibble_buf:\n" ++
  "  .zero 64\n" ++
  ".balign 8\n" ++
  "ad_offset:\n" ++
  "  .zero 8\n" ++
  "ad_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "aa_value_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n" ++
  "  .zero 256\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecsahsr_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecsahsr_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "ecsahsr_dummy_offset:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ecsahsr_code_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecsahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskExtcodesizeAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtcodesizeAtHeaderStateRootPrologue
  dataAsm     := ziskExtcodesizeAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
