/-
  EvmAsm.Codegen.Programs.HeadersKeccak

  SSZ-list-of-headers Keccak walk + parent-hash linkage utilities
  carved out of `EvmAsm.Codegen.Programs` per the file-size hard
  cap. Hosts:

    K15  headers_keccak_chain     (walk + per-element keccak)
    K16  headers_keccak_array     (write each digest)
    K17  headers_parent_hash      (RLP-walk to parent_hash field)
    K18  headers_validate_chain   (parent_hash chain check)
    K94  header_validate_parent_hash
    K96  header_chain_walk_step

  All six iterate over a contiguous header-bytes section and call
  `zkvm_keccak256` (from `HashBridge.lean`) plus the
  `headers_parent_hash` RLP-walk; no other inter-cluster deps.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## headers_keccak_chain -- PR-K15 walk an SSZ list section,
    keccak each element, return the last digest + count.

    Walks the SSZ inner-offset table to derive per-element
    bounds (same parsing shape as the SSZ list-merkleize work),
    then calls `zkvm_keccak256(el_i_start, el_i_len, out_ptr)`
    for each element. The output buffer is overwritten on every
    iteration; after the loop, it holds the LAST element's
    digest. Returns the element count `N` in `a0`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len (0 ⇒ empty list)
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *a2 : keccak256(element[N-1]) if N > 0, else 0.

    No per-element scratch; works for any N. -/
def headersKeccakChainFunction : String :=
  "headers_keccak_chain:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # s0 = section ptr\n" ++
  "  mv s1, a1                  # s1 = section_len\n" ++
  "  mv s2, a2                  # s2 = output ptr\n" ++
  "  beqz s1, .Lhkc_n0          # empty section ⇒ N = 0\n" ++
  "  lwu t0, 0(s0)              # offset_0 = 4 * N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lhkc_loop:\n" ++
  "  beq s4, s3, .Lhkc_done\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lhkc_use_end\n" ++
  "  slli t3, t3, 2             # 4*(i+1)\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lhkc_have_end\n" ++
  ".Lhkc_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lhkc_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s2                  # output (overwritten each iter)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lhkc_loop\n" ++
  ".Lhkc_n0:\n" ++
  "  sd zero,  0(s2)\n" ++
  "  sd zero,  8(s2)\n" ++
  "  sd zero, 16(s2)\n" ++
  "  sd zero, 24(s2)\n" ++
  "  li s3, 0                   # N = 0\n" ++
  ".Lhkc_done:\n" ++
  "  mv a0, s3                  # return N\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_headers_keccak_chain`: probe BuildUnit that reads an
    SSZ list section from host input and writes the count + last
    digest to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : N (u64 LE)
      bytes  8..40 : keccak256(element[N-1]) or 0 if N=0 -/
def ziskHeadersKeccakChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # last_hash output (OUTPUT + 8)\n" ++
  "  jal ra, headers_keccak_chain\n" ++
  "  li t0, 0xa0010000           # write N at OUTPUT + 0\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhkc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakChainFunction ++ "\n" ++
  ".Lhkc_pdone:"

def ziskHeadersKeccakChainDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakChainPrologue
  dataAsm     := ziskHeadersKeccakChainDataSection
}

/-! ## headers_keccak_array -- PR-K16 walk SSZ list section,
    keccak each element, store every digest in caller table.

    Sibling of `headers_keccak_chain` (PR-K15): same SSZ-list
    parsing loop, but each iteration writes the digest to
    `table[i]` instead of overwriting the same slot. Returns the
    element count `N`.

    Calling convention:
      a0 (input)  : section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : table base ptr (must hold N*32 bytes)
      ra (input)  : return
      a0 (output) : N (element count)
      32 bytes at *(table + 32*i) = keccak256(element[i])
        for each i in 0..N. -/
def headersKeccakArray_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .BEQ .x9 .x0 (92 : BitVec 13),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x19 .x5 (2 : BitVec 6),
    .LI .x20 (0 : Word),
    .BEQ .x20 .x19 (80 : BitVec 13),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x20 (1 : BitVec 12),
    .BEQ .x28 .x19 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x11 .x29 .x10,
    .SLLI .x5 .x20 (5 : BitVec 6),
    .ADD .x12 .x18 .x5,
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.headers_keccak_array + 120)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-72 : BitVec 21),
    .LI .x19 (0 : Word),
    .MV .x10 .x19,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headersKeccakArray_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headersKeccakArray_relocs : RelocTable :=
  [ (30, .jal .x1 "zkvm_keccak256") ]

def headersKeccakArrayFunction : String :=
  "headers_keccak_array:\n" ++ emitProgramR headersKeccakArray_prog headersKeccakArray_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headersKeccakArray_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headersKeccakArrayFunction_eq_prog :
    headersKeccakArrayFunction = "headers_keccak_array:\n" ++ emitProgramR headersKeccakArray_prog headersKeccakArray_relocs := rfl

#guard headersKeccakArrayFunction.startsWith "headers_keccak_array:\n"
#guard headersKeccakArray_prog.length = 43
/-- `zisk_headers_keccak_array`: probe BuildUnit that reads an
    SSZ list section from host input and writes (count, table)
    to OUTPUT, capped at N ≤ 7 to fit ziskemu's 256-byte output
    channel.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8     : N (u64 LE)
      bytes  8..8+32*N : N digests of 32 bytes each -/
def ziskHeadersKeccakArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # table at OUTPUT + 8\n" ++
  "  jal ra, headers_keccak_array\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write N at OUTPUT + 0\n" ++
  "  j .Lhka_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  ".Lhka_pdone:"

def ziskHeadersKeccakArrayDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskHeadersKeccakArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersKeccakArrayPrologue
  dataAsm     := ziskHeadersKeccakArrayDataSection
}

/-! ## headers_parent_hash -- PR-K17 RLP-walk to extract the
    first 32-byte field of an RLP-encoded Ethereum header
    (`parent_hash`).

    Skips the outer list prefix (0xc0..0xc0+55 short form, 0xf8
    1-byte-length, or 0xf9 2-byte-length forms), expects a
    0xa0 Bytes32 string prefix, then copies the 32 raw bytes
    to the caller's output.

    Calling convention:
      a0 (input)  : RLP-encoded header ptr (read-only)
      a1 (input)  : header byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 on success; 32 bytes at *a2 = parent_hash
        1 on RLP parse failure

    Pure register arithmetic; no scratch memory, no callee-saved
    registers used. Leaf-callable. -/
def headersParentHash_prog : Program :=
  [ .LBU .x5 .x10 (0 : BitVec 12),
    .LI .x6 (192 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 8)),
    .LI .x6 (248 : Word),
    .BLTU .x5 .x6 (36 : BitVec 13),
    .LI .x6 (247 : Word),
    .SUB .x7 .x5 .x6,
    .LI .x28 (2 : Word),
    .BLTU .x28 .x7 (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 32)),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADD .x10 .x10 .x7,
    .SUB .x11 .x11 .x7,
    .JAL .x0 (12 : BitVec 21),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (-1 : BitVec 12),
    .LI .x5 (33 : Word),
    .BLTU .x11 .x5 (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 64)),
    .LBU .x6 .x10 (0 : BitVec 12),
    .LI .x7 (160 : Word),
    .BNE .x6 .x7 (52 : BitVec 13),
    .LI .x5 (0 : Word),
    .LI .x6 (32 : Word),
    .BEQ .x5 .x6 (32 : BitVec 13),
    .ADDI .x7 .x10 (1 : BitVec 12),
    .ADD .x7 .x7 .x5,
    .LBU .x28 .x7 (0 : BitVec 12),
    .ADD .x7 .x12 .x5,
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def headersParentHashFunction : String :=
  "headers_parent_hash:\n" ++ emitProgram headersParentHash_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `headersParentHash_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem headersParentHashFunction_eq_prog :
    headersParentHashFunction = "headers_parent_hash:\n" ++ emitProgram headersParentHash_prog := rfl

#guard headersParentHashFunction.startsWith "headers_parent_hash:\n"
#guard headersParentHash_prog.length = 34
/-- `zisk_headers_parent_hash`: probe BuildUnit that reads an
    RLP-encoded header from host input and writes
    `(status, parent_hash)` to OUTPUT.
    Input layout:
      bytes  0.. 8 : header_len (u64)
      bytes  8..   : RLP-encoded header bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 = ok, 1 = parse fail)
      bytes  8..40 : parent_hash (32 bytes; meaningful only on
                     status=0; on failure, contains zeros) -/
def ziskHeadersParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # parent_hash output (OUTPUT + 8)\n" ++
  "  # Pre-zero output[8..40] so a parse failure surfaces as zeros.\n" ++
  "  sd zero,  0(a2); sd zero,  8(a2); sd zero, 16(a2); sd zero, 24(a2)\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # write status at OUTPUT + 0\n" ++
  "  j .Lhph_pdone\n" ++
  headersParentHashFunction ++ "\n" ++
  ".Lhph_pdone:"

def ziskHeadersParentHashDataSection : String :=
  ".section .data\n" ++
  "hph_scratch:\n" ++
  "  .zero 8"

def ziskHeadersParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersParentHashPrologue
  dataAsm     := ziskHeadersParentHashDataSection
}

/-! ## header_validate_parent_hash -- PR-K94

    Per-header parent-hash continuity check from `validate_header`
    in `forks/amsterdam/fork.py`:

      block_parent_hash = keccak256(rlp.encode(parent_header))
      if header.parent_hash != block_parent_hash:
          raise InvalidBlock

    The single-pair check that anchors a block to its parent. Used
    by `validate_header` directly; the multi-header walk in
    `validate_headers(headers, parent_header)` consists of K18-style
    pairwise iterations of exactly this primitive (K18 already
    handles the iteration via the SSZ digest table, but expects a
    pre-computed digest array; K94 is the standalone form that
    callers without that pipeline can use).

    Composes:
      - PR-K17 `headers_parent_hash`  — extract this header's
                                        parent_hash field (RLP[0])
      - PR-K3  `zkvm_keccak256`       — Keccak-f[1600] sponge

    Calling convention:
      a0 (input)  : this_header_rlp ptr
      a1 (input)  : this_header_rlp byte length
      a2 (input)  : parent_header_rlp ptr
      a3 (input)  : parent_header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : match — parent_hash field == keccak256(parent_rlp)
        1 : RLP parse failure of this_header (field 0 not 32 B)
        2 : mismatch — both decode/hash succeeded, values differ

    Uses 64 bytes of `.data` scratch (`hvph_claimed` 32 B +
    `hvph_computed` 32 B). -/
def headerValidateParentHash_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .AUIPC .x12 (laHi GuestAddrs.hvph_claimed (GuestAddrs.header_validate_parent_hash + 28)),
    .ADDI .x12 .x12 (laLo GuestAddrs.hvph_claimed (GuestAddrs.header_validate_parent_hash + 28)),
    .JAL .x1 (jalOff GuestAddrs.headers_parent_hash (GuestAddrs.header_validate_parent_hash + 36)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (100 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.hvph_computed (GuestAddrs.header_validate_parent_hash + 60)),
    .ADDI .x12 .x12 (laLo GuestAddrs.hvph_computed (GuestAddrs.header_validate_parent_hash + 60)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.header_validate_parent_hash + 68)),
    .AUIPC .x5 (laHi GuestAddrs.hvph_claimed (GuestAddrs.header_validate_parent_hash + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hvph_claimed (GuestAddrs.header_validate_parent_hash + 72)),
    .AUIPC .x6 (laHi GuestAddrs.hvph_computed (GuestAddrs.header_validate_parent_hash + 80)),
    .ADDI .x6 .x6 (laLo GuestAddrs.hvph_computed (GuestAddrs.header_validate_parent_hash + 80)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (48 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (36 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (24 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerValidateParentHash_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerValidateParentHash_relocs : RelocTable :=
  [ (7, .la .x12 "hvph_claimed"),
    (9, .jal .x1 "headers_parent_hash"),
    (15, .la .x12 "hvph_computed"),
    (17, .jal .x1 "zkvm_keccak256"),
    (18, .la .x5 "hvph_claimed"),
    (20, .la .x6 "hvph_computed") ]

def headerValidateParentHashFunction : String :=
  "header_validate_parent_hash:\n" ++ emitProgramR headerValidateParentHash_prog headerValidateParentHash_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerValidateParentHash_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerValidateParentHashFunction_eq_prog :
    headerValidateParentHashFunction = "header_validate_parent_hash:\n" ++ emitProgramR headerValidateParentHash_prog headerValidateParentHash_relocs := rfl

#guard headerValidateParentHashFunction.startsWith "header_validate_parent_hash:\n"
#guard headerValidateParentHash_prog.length = 43
/-- `zisk_header_validate_parent_hash`: probe BuildUnit. Reads
    (this_len, parent_len, this_bytes ‖ parent_bytes) from host
    input, writes 8-byte status to OUTPUT.
    Input layout:
      bytes  0.. 8 : this_header_len
      bytes  8..16 : parent_header_len
      bytes 16..   : this_header_rlp ‖ parent_header_rlp -/
def ziskHeaderValidateParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # this_header_len\n" ++
  "  ld a3, 16(a4)               # parent_header_len\n" ++
  "  addi a0, a4, 24             # this_header_ptr\n" ++
  "  add a2, a0, a1              # parent_header_ptr\n" ++
  "  jal ra, header_validate_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhvph_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerValidateParentHashFunction ++ "\n" ++
  ".Lhvph_pdone:"

def ziskHeaderValidateParentHashDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hvph_claimed:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "hvph_computed:\n" ++
  "  .zero 32"

def ziskHeaderValidateParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateParentHashPrologue
  dataAsm     := ziskHeaderValidateParentHashDataSection
}

/-! ## header_chain_walk_step -- PR-K96

    Per-step primitive for chain validation: given the previous
    block's hash and a candidate child header's RLP, verify
    `child.parent_hash == previous_hash` and compute
    `keccak256(child_rlp)` as the new running hash.

    A caller iterating over N headers does N calls; at the end
    `*new_hash` holds the latest block's hash, and any mid-chain
    mismatch returns status 2.

    PR-K18 `headers_validate_chain` already implements the chain
    walk on top of a pre-computed SSZ digest table; K96 is the
    standalone per-step that works without that pipeline (raw
    RLP-encoded headers in, no precomputed digest array required).

    Composes:
      - PR-K17 `headers_parent_hash` — extract child's parent_hash
      - PR-K3  `zkvm_keccak256`      — compute child's hash

    Calling convention:
      a0 (input)  : prev_hash ptr (32 B, caller-supplied)
      a1 (input)  : child_header_rlp ptr
      a2 (input)  : child_header_rlp byte length
      a3 (input)  : 32-byte out ptr (receives child's hash on
                    success, zeros on failure)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : child header parse failed (field 0 not 32 B)
        2 : mismatch — child.parent_hash != prev_hash

    Uses 32 bytes of `.data` scratch (`hcws_claimed`). -/
def headerChainWalkStepFunction : String :=
  "header_chain_walk_step:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # prev_hash ptr\n" ++
  "  mv s1, a1                   # child_rlp ptr\n" ++
  "  mv s2, a2                   # child_len\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  # Step 1: extract child's parent_hash → hcws_claimed.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, hcws_claimed\n" ++
  "  jal ra, headers_parent_hash\n" ++
  "  beqz a0, .Lhcws_compare\n" ++
  "  li a0, 1\n" ++
  "  j .Lhcws_zero_out\n" ++
  ".Lhcws_compare:\n" ++
  "  # Compare prev_hash (s0) to claimed (hcws_claimed) byte-by-byte.\n" ++
  "  la t0, hcws_claimed\n" ++
  "  ld t1,  0(s0); ld t2,  0(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1,  8(s0); ld t2,  8(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1, 16(s0); ld t2, 16(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  ld t1, 24(s0); ld t2, 24(t0); bne t1, t2, .Lhcws_diff\n" ++
  "  # Match — compute child hash → *out.\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcws_ret\n" ++
  ".Lhcws_diff:\n" ++
  "  li a0, 2\n" ++
  ".Lhcws_zero_out:\n" ++
  "  # Zero the output on any failure.\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  ".Lhcws_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_header_chain_walk_step`: probe BuildUnit. Reads
    (child_len, prev_hash[32], child_rlp) from host input, writes
    (status, child_hash[32]) to OUTPUT.
    Input layout:
      bytes  0.. 8 : child_header_len
      bytes  8..40 : prev_hash (32 B)
      bytes 40..   : child_header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : child block hash on success, zero otherwise -/
def ziskHeaderChainWalkStepPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a2, 8(a4)                # child_header_len\n" ++
  "  addi a0, a4, 16             # prev_hash ptr\n" ++
  "  addi a1, a4, 48             # child_rlp ptr\n" ++
  "  li a3, 0xa0010008           # child_hash output (OUTPUT + 8)\n" ++
  "  jal ra, header_chain_walk_step\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhcws_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headerChainWalkStepFunction ++ "\n" ++
  ".Lhcws_pdone:"

def ziskHeaderChainWalkStepDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "hcws_claimed:\n" ++
  "  .zero 32"

def ziskHeaderChainWalkStepProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderChainWalkStepPrologue
  dataAsm     := ziskHeaderChainWalkStepDataSection
}

/-! ## K99 / K126 / K127 address-derivation cluster — moved to `Programs/Address.lean` (file-size hard cap). -/
/-! ## K100 mpt_account_path_nibbles — moved to `Programs/Mpt.lean` (file-size hard cap). -/


/-! ## headers_validate_chain -- PR-K18 parent_hash chain check

    Composes PR-K16 `headers_keccak_array` (build per-header
    digest table) with PR-K17 `headers_parent_hash` (RLP-extract
    each header's first 32-byte field) to verify the
    `validate_headers` invariant:

        header[i].parent_hash == keccak256(header[i-1])
            for every i in 1..N

    matches the Python check in
    `execution-specs/.../stateless.py::validate_headers`.

    Calling convention:
      a0 (input)  : SSZ list section ptr (witness.headers)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : 8-byte output ptr (receives N as u64 LE)
      ra (input)  : return
      a0 (output) : 0 on success (chain valid) or N ≤ 1
                    1 on mismatch / RLP-decode failure

    Walks the list using the same SSZ inner-offset table as
    PR-K15/K16. Caps at N ≤ 256 (matches `MAX_WITNESS_HEADERS`).

    Uses two `.data` scratch buffers:
      vh_keccak_table          : 256 × 32 = 8 KB
      vh_extracted_parent_hash : 32 B
-/
def headersValidateChain_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .BEQ .x9 .x0 (20 : BitVec 13),
    .LWU .x5 .x8 (0 : BitVec 12),
    .SRLI .x5 .x5 (2 : BitVec 6),
    .LI .x6 (256 : Word),
    .BLTU .x6 .x5 (208 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.vh_keccak_table (GuestAddrs.headers_validate_chain + 68)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vh_keccak_table (GuestAddrs.headers_validate_chain + 68)),
    .JAL .x1 (jalOff GuestAddrs.headers_keccak_array (GuestAddrs.headers_validate_chain + 76)),
    .MV .x19 .x10,
    .SD .x18 .x19 (0 : BitVec 12),
    .LI .x5 (2 : Word),
    .BLTU .x19 .x5 (164 : BitVec 13),
    .LI .x20 (1 : Word),
    .BEQ .x20 .x19 (156 : BitVec 13),
    .SLLI .x5 .x20 (2 : BitVec 6),
    .ADD .x6 .x8 .x5,
    .LWU .x7 .x6 (0 : BitVec 12),
    .ADD .x10 .x8 .x7,
    .ADDI .x28 .x20 (1 : BitVec 12),
    .BEQ .x28 .x19 (24 : BitVec 13),
    .SLLI .x28 .x28 (2 : BitVec 6),
    .ADD .x28 .x8 .x28,
    .LWU .x29 .x28 (0 : BitVec 12),
    .ADD .x29 .x8 .x29,
    .JAL .x0 (8 : BitVec 21),
    .ADD .x29 .x8 .x9,
    .SUB .x11 .x29 .x10,
    .AUIPC .x12 (laHi GuestAddrs.vh_extracted_parent_hash (GuestAddrs.headers_validate_chain + 156)),
    .ADDI .x12 .x12 (laLo GuestAddrs.vh_extracted_parent_hash (GuestAddrs.headers_validate_chain + 156)),
    .JAL .x1 (jalOff GuestAddrs.headers_parent_hash (GuestAddrs.headers_validate_chain + 164)),
    .BNE .x10 .x0 (96 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.vh_keccak_table (GuestAddrs.headers_validate_chain + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.vh_keccak_table (GuestAddrs.headers_validate_chain + 172)),
    .ADDI .x6 .x20 (-1 : BitVec 12),
    .SLLI .x6 .x6 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.vh_extracted_parent_hash (GuestAddrs.headers_validate_chain + 192)),
    .ADDI .x6 .x6 (laLo GuestAddrs.vh_extracted_parent_hash (GuestAddrs.headers_validate_chain + 192)),
    .LD .x7 .x5 (0 : BitVec 12),
    .LD .x28 .x6 (0 : BitVec 12),
    .BNE .x7 .x28 (56 : BitVec 13),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x28 .x6 (8 : BitVec 12),
    .BNE .x7 .x28 (44 : BitVec 13),
    .LD .x7 .x5 (16 : BitVec 12),
    .LD .x28 .x6 (16 : BitVec 12),
    .BNE .x7 .x28 (32 : BitVec 13),
    .LD .x7 .x5 (24 : BitVec 12),
    .LD .x28 .x6 (24 : BitVec 12),
    .BNE .x7 .x28 (20 : BitVec 13),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-152 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headersValidateChain_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headersValidateChain_relocs : RelocTable :=
  [ (17, .la .x12 "vh_keccak_table"),
    (19, .jal .x1 "headers_keccak_array"),
    (39, .la .x12 "vh_extracted_parent_hash"),
    (41, .jal .x1 "headers_parent_hash"),
    (43, .la .x5 "vh_keccak_table"),
    (48, .la .x6 "vh_extracted_parent_hash") ]

def headersValidateChainFunction : String :=
  "headers_validate_chain:\n" ++ emitProgramR headersValidateChain_prog headersValidateChain_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headersValidateChain_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headersValidateChainFunction_eq_prog :
    headersValidateChainFunction = "headers_validate_chain:\n" ++ emitProgramR headersValidateChain_prog headersValidateChain_relocs := rfl

#guard headersValidateChainFunction.startsWith "headers_validate_chain:\n"
#guard headersValidateChain_prog.length = 75
/-- `zisk_headers_validate_chain`: probe BuildUnit that reads an
    SSZ list of RLP-encoded headers from host input and writes
    (status, N) to OUTPUT.
    Input layout:
      bytes  0.. 8 : section_len (u64)
      bytes  8..   : SSZ list section bytes
    Output layout:
      bytes  0.. 8 : status (u64 LE; 0 ok / 1 mismatch)
      bytes  8..16 : N (u64 LE; element count) -/
def ziskHeadersValidateChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # section_len\n" ++
  "  addi a0, a3, 16             # section ptr\n" ++
  "  li a2, 0xa0010008           # N out ptr (OUTPUT + 8)\n" ++
  "  jal ra, headers_validate_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lvh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  headersKeccakArrayFunction ++ "\n" ++
  headersParentHashFunction ++ "\n" ++
  headersValidateChainFunction ++ "\n" ++
  ".Lvh_pdone:"

def ziskHeadersValidateChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192                 # 256 × 32-byte digests\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32"

def ziskHeadersValidateChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeadersValidateChainPrologue
  dataAsm     := ziskHeadersValidateChainDataSection
}


end EvmAsm.Codegen
