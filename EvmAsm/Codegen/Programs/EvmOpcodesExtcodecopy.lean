/-
  EvmAsm.Codegen.Programs.EvmOpcodesExtcodecopy

  EXTCODECOPY opcode probe — carved out of EvmOpcodes.lean to
  stay under the file-size hard cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.State
import EvmAsm.Codegen.Programs.WitnessCodeLookup

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## extcodecopy_at_header_state_root  (EVM EXTCODECOPY opcode)

    Witness-side implementation of the EVM EXTCODECOPY opcode.
    Given a parent header RLP, an address, a code offset, a
    length, an SSZ `witness.state` list, and an SSZ
    `witness.codes` list, write `length` bytes into a
    caller-supplied output buffer:

        for i in 0..length:
          output[i] = code[code_offset + i] if code_offset + i < len(code) else 0

    i.e., reads past the end of the code are zero-padded
    (NOT truncated, NOT errored). This zero-pad rule is the
    EXTCODECOPY-specific spec divergence from a naive byte-copy.

    Distinct from PR `code_at_header_state_root` (which returns
    the full code's offset/length in witness.codes without
    range-extraction) and from PR `extcodesize_at_header_state_root`
    (which returns just the length). EXTCODECOPY is the only
    opcode that actually emits code bytes into EVM memory.

    Composes K201 `header_extract_state_root` + K28
    `account_at_address` + code-specific K19 `witness_codes_lookup_by_hash` + an
    inline byte-by-byte zero-padded copy loop.

    Calling convention (8 args, fits in a0..a7):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp_len
      a2 (input)  : address ptr (20 bytes)
      a3 (input)  : code_offset (u64)
      a4 (input)  : length (u64; must be <= MAX_CODE_SIZE = 65536 / EIP-7907)
      a5 (input)  : output buffer ptr (`length` bytes)
      a6 (input)  : witness.state ptr
      a7 (input)  : witness.state len
      (precondition: caller pre-set `eccp_codes_ptr` and
       `eccp_codes_len` in .data scratch.)
      ra (input)  : return

      a0 (output) :
        0 = success (output filled, zero-padded as needed)
        2 = state-trie mpt parse error
        3 = account_decode failure
        4 = header parse / state_root size fail
        5 = code_hash != EMPTY but not in witness.codes
            (witness integrity violation)
        6 = length > 65536 (EIP-7907 deployed-code cap)

      (Code 1 "account not in trie" is intentionally absent:
      missing accounts map to `status=0, output=all zeros` per
      the EXTCODECOPY spec.)
-/
def extcodecopyAtHeaderStateRoot_prog : Program :=
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
    .LUI .x5 (16 : BitVec 20),
    .BLTU .x5 .x20 (344 : BitVec 13),
    .MV .x5 .x21,
    .MV .x6 .x20,
    .BEQ .x6 .x0 (20 : BitVec 13),
    .SB .x5 .x0 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.ecc_state_root (GuestAddrs.extcodecopy_at_header_state_root + 124)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ecc_state_root (GuestAddrs.extcodecopy_at_header_state_root + 124)),
    .JAL .x1 (jalOff GuestAddrs.header_extract_state_root (GuestAddrs.extcodecopy_at_header_state_root + 132)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (4 : Word),
    .JAL .x0 (288 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (20 : Word),
    .AUIPC .x12 (laHi GuestAddrs.ecc_state_root (GuestAddrs.extcodecopy_at_header_state_root + 156)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ecc_state_root (GuestAddrs.extcodecopy_at_header_state_root + 156)),
    .MV .x13 .x22,
    .MV .x14 .x23,
    .AUIPC .x24 (laHi GuestAddrs.ecc_acct_struct (GuestAddrs.extcodecopy_at_header_state_root + 172)),
    .ADDI .x24 .x24 (laLo GuestAddrs.ecc_acct_struct (GuestAddrs.extcodecopy_at_header_state_root + 172)),
    .MV .x15 .x24,
    .JAL .x1 (jalOff GuestAddrs.account_at_address (GuestAddrs.extcodecopy_at_header_state_root + 184)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x10 .x5 (8 : BitVec 13),
    .JAL .x0 (232 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (224 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.ecc_empty_code_hash (GuestAddrs.extcodecopy_at_header_state_root + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecc_empty_code_hash (GuestAddrs.extcodecopy_at_header_state_root + 212)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x24 (72 : BitVec 12),
    .BNE .x6 .x7 (48 : BitVec 13),
    .LD .x6 .x5 (8 : BitVec 12),
    .LD .x7 .x24 (80 : BitVec 12),
    .BNE .x6 .x7 (36 : BitVec 13),
    .LD .x6 .x5 (16 : BitVec 12),
    .LD .x7 .x24 (88 : BitVec 12),
    .BNE .x6 .x7 (24 : BitVec 13),
    .LD .x6 .x5 (24 : BitVec 12),
    .LD .x7 .x24 (96 : BitVec 12),
    .BNE .x6 .x7 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (160 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.eccp_codes_ptr (GuestAddrs.extcodecopy_at_header_state_root + 276)),
    .ADDI .x5 .x5 (laLo GuestAddrs.eccp_codes_ptr (GuestAddrs.extcodecopy_at_header_state_root + 276)),
    .LD .x10 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.eccp_codes_len (GuestAddrs.extcodecopy_at_header_state_root + 288)),
    .ADDI .x5 .x5 (laLo GuestAddrs.eccp_codes_len (GuestAddrs.extcodecopy_at_header_state_root + 288)),
    .LD .x11 .x5 (0 : BitVec 12),
    .ADDI .x12 .x24 (72 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.ecc_match_offset (GuestAddrs.extcodecopy_at_header_state_root + 304)),
    .ADDI .x13 .x13 (laLo GuestAddrs.ecc_match_offset (GuestAddrs.extcodecopy_at_header_state_root + 304)),
    .AUIPC .x14 (laHi GuestAddrs.ecc_match_len (GuestAddrs.extcodecopy_at_header_state_root + 312)),
    .ADDI .x14 .x14 (laLo GuestAddrs.ecc_match_len (GuestAddrs.extcodecopy_at_header_state_root + 312)),
    .MV .x15 .x18,
    .JAL .x1 (jalOff GuestAddrs.code_read_fetch (GuestAddrs.extcodecopy_at_header_state_root + 324)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (5 : Word),
    .JAL .x0 (96 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.eccp_codes_ptr (GuestAddrs.extcodecopy_at_header_state_root + 340)),
    .ADDI .x5 .x5 (laLo GuestAddrs.eccp_codes_ptr (GuestAddrs.extcodecopy_at_header_state_root + 340)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.ecc_match_offset (GuestAddrs.extcodecopy_at_header_state_root + 352)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecc_match_offset (GuestAddrs.extcodecopy_at_header_state_root + 352)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x25 .x6 .x7,
    .AUIPC .x5 (laHi GuestAddrs.ecc_match_len (GuestAddrs.extcodecopy_at_header_state_root + 368)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ecc_match_len (GuestAddrs.extcodecopy_at_header_state_root + 368)),
    .LD .x28 .x5 (0 : BitVec 12),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x20 (36 : BitVec 13),
    .ADD .x6 .x19 .x5,
    .BGEU .x6 .x28 (20 : BitVec 13),
    .ADD .x7 .x25 .x6,
    .LBU .x29 .x7 (0 : BitVec 12),
    .ADD .x30 .x21 .x5,
    .SB .x30 .x29 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (6 : Word),
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

/-- Reloc side-table for `extcodecopyAtHeaderStateRoot_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def extcodecopyAtHeaderStateRoot_relocs : RelocTable :=
  [ (31, .la .x12 "ecc_state_root"),
    (33, .jal .x1 "header_extract_state_root"),
    (39, .la .x12 "ecc_state_root"),
    (43, .la .x24 "ecc_acct_struct"),
    (46, .jal .x1 "account_at_address"),
    (53, .la .x5 "ecc_empty_code_hash"),
    (69, .la .x5 "eccp_codes_ptr"),
    (72, .la .x5 "eccp_codes_len"),
    (76, .la .x13 "ecc_match_offset"),
    (78, .la .x14 "ecc_match_len"),
    (81, .jal .x1 "code_read_fetch"),
    (85, .la .x5 "eccp_codes_ptr"),
    (88, .la .x5 "ecc_match_offset"),
    (92, .la .x5 "ecc_match_len") ]

def extcodecopyAtHeaderStateRootFunction : String :=
  "extcodecopy_at_header_state_root:\n" ++ emitProgramR extcodecopyAtHeaderStateRoot_prog extcodecopyAtHeaderStateRoot_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `extcodecopyAtHeaderStateRoot_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem extcodecopyAtHeaderStateRootFunction_eq_prog :
    extcodecopyAtHeaderStateRootFunction = "extcodecopy_at_header_state_root:\n" ++ emitProgramR extcodecopyAtHeaderStateRoot_prog extcodecopyAtHeaderStateRoot_relocs := rfl

#guard extcodecopyAtHeaderStateRootFunction.startsWith "extcodecopy_at_header_state_root:\n"
#guard extcodecopyAtHeaderStateRoot_prog.length = 121
/-- `zisk_extcodecopy_at_header_state_root`: probe BuildUnit.

    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : header_rlp_len    (u64 LE)
      bytes 16..24 : witness_state_len (u64 LE)
      bytes 24..32 : witness_codes_len (u64 LE)
      bytes 32..40 : code_offset (u64 LE)
      bytes 40..48 : length (u64 LE; must be <= 65536)
      bytes 48..68 : address (20 bytes)
      bytes 68..68+H              : header_rlp
      bytes 68+H..68+H+WS         : witness.state
      bytes 68+H+WS..             : witness.codes
    Output layout:
      bytes  0.. 8 : status (0 / 2 / 3 / 4 / 5 / 6)
      bytes  8..16 : effective length (= length on success; 0 otherwise)
      bytes 16..(16+length) : copied code bytes, zero-padded -/
def ziskExtcodecopyAtHeaderStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1,  8(s0)               # header_rlp_len\n" ++
  "  ld s2, 16(s0)               # witness_state_len\n" ++
  "  ld s3, 24(s0)               # witness_codes_len\n" ++
  "  ld s4, 32(s0)               # code_offset\n" ++
  "  ld s5, 40(s0)               # length\n" ++
  "  addi s6, s0, 68             # header_rlp ptr\n" ++
  "  add s7, s6, s1              # witness.state ptr\n" ++
  "  add s8, s7, s2              # witness.codes ptr\n" ++
  "  mv a0, s8; mv a1, s3; jal ra, witness_codes_index_build\n" ++
  "  mv a0, s6                   # header_rlp ptr\n" ++
  "  mv a1, s1                   # header_rlp_len\n" ++
  "  addi a2, s0, 48             # address ptr\n" ++
  "  mv a3, s4                   # code_offset\n" ++
  "  mv a4, s5                   # length\n" ++
  "  li a5, 0xa0010010           # output buffer at OUTPUT + 16\n" ++
  "  mv a6, s7                   # witness.state ptr\n" ++
  "  mv a7, s2                   # witness.state len\n" ++
  "  la t0, eccp_codes_ptr; sd s8, 0(t0)\n" ++
  "  la t0, eccp_codes_len; sd s3, 0(t0)\n" ++
  "  jal ra, extcodecopy_at_header_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  # Write effective length = length on success, else 0.\n" ++
  "  bnez a0, .Lecc_no_len\n" ++
  "  sd s5, 8(t0)                # success: use saved length\n" ++
  "  j .Lecc_pdone\n" ++
  ".Lecc_no_len:\n" ++
  "  sd zero, 8(t0)\n" ++
  "  j .Lecc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  witnessCodesLookupByHashBundle ++ "\n" ++
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
  extcodecopyAtHeaderStateRootFunction ++ "\n" ++
  ".Lecc_pdone:"

def ziskExtcodecopyAtHeaderStateRootDataSection : String :=
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
  "ecc_state_root:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ecc_acct_struct:\n" ++
  "  .zero 104\n" ++
  ".balign 8\n" ++
  "eccp_codes_ptr:\n" ++
  "  .zero 8\n" ++
  "eccp_codes_len:\n" ++
  "  .zero 8\n" ++
  "ecc_match_offset:\n" ++
  "  .zero 8\n" ++
  "ecc_match_len:\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  "ecc_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70"

def ziskExtcodecopyAtHeaderStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskExtcodecopyAtHeaderStateRootPrologue
  dataAsm     := ziskExtcodecopyAtHeaderStateRootDataSection
}

end EvmAsm.Codegen
