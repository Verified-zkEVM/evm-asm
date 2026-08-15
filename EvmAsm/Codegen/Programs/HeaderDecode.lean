/-
  EvmAsm.Codegen.Programs.HeaderDecode

  Header decoders carved out of `EvmAsm.Codegen.Programs.Header`
  per the file-size hard cap. Hosts:

    K38  header_minimal_decode  (parent_hash + state_root + number + timestamp)
    K39  header_extended_decode (full Amsterdam header decode)
    K55  coinbase_extract_from_header (beneficiary getter)

  Compose K20 / K34 / K35 (RlpRead + Tx).

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.RlpWalk

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_minimal_decode -- PR-K38

    Decode the 4 STF-essential fields of an RLP-encoded
    Ethereum block header into a flat 96-byte output struct:

       0..32   parent_hash    (RLP field 0)
      32..64   state_root     (RLP field 3)
      64..72   number (u64)   (RLP field 8)
      72..80   timestamp(u64) (RLP field 11; rejected if > 8 B)

    Header RLP field count varies by fork (15..22 fields).
    This decoder reads only the first 12 fields' indices, so
    it works on any post-Berlin header.

     Calling convention:
       a0 (input)  : header_rlp ptr
       a1 (input)  : header_rlp byte length
       a2 (input)  : 96-byte output struct ptr
       ra (input)  : return
       a0 (output) : 0 success / 1 parse fail (not an RLP list,
                     parent_hash or state_root not 32 bytes,
                     or timestamp > 8 bytes BE).

     Composes the cursor walker (`rlp_walk_init` +
     `rlp_walk_next` + `rlp_content_to_u64_strict`). Header scalar fields use
     the strict canonical decoder selected by their execution-specs types;
     the guest's separate u64 width/representability assumption is unchanged.
     The two U64 blob fields also use `rlp_content_to_u64_strict`. The four wanted
     fields live at indices {0,3,8,11}; the walker visits the
     first 12 items once (single O(N) pass), capturing the four
     wanted fields and skipping the eight in between. The hash
     fields are copied via 4 x 8-byte `ld`/`sd`. -/
def headerMinimalDecode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init 2147483680),
    .BNE .x12 .x0 (brOff 2147484072 2147483684),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483704),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483712),
    .LI .x5 (32 : Word),
    .BNE .x12 .x5 (brOff 2147484072 2147483720),
    .SUB .x28 .x10 .x12,
    .LD .x29 .x28 (0 : BitVec 12),
    .SD .x18 .x29 (0 : BitVec 12),
    .LD .x29 .x28 (8 : BitVec 12),
    .SD .x18 .x29 (8 : BitVec 12),
    .LD .x29 .x28 (16 : BitVec 12),
    .SD .x18 .x29 (16 : BitVec 12),
    .LD .x29 .x28 (24 : BitVec 12),
    .SD .x18 .x29 (24 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483768),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483776),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483788),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483796),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483808),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483816),
    .LI .x5 (32 : Word),
    .BNE .x12 .x5 (brOff 2147484072 2147483824),
    .SUB .x28 .x10 .x12,
    .LD .x29 .x28 (0 : BitVec 12),
    .SD .x18 .x29 (32 : BitVec 12),
    .LD .x29 .x28 (8 : BitVec 12),
    .SD .x18 .x29 (40 : BitVec 12),
    .LD .x29 .x28 (16 : BitVec 12),
    .SD .x18 .x29 (48 : BitVec 12),
    .LD .x29 .x28 (24 : BitVec 12),
    .SD .x18 .x29 (56 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483872),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483880),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483892),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483900),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483912),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483920),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483932),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483940),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483952),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147483960),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict 2147483972),
    .BNE .x11 .x0 (brOff 2147484072 2147483976),
    .SD .x18 .x10 (64 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147483992),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff 2147484072 2147484000),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484012),
    .MV .x19 .x10,
    .BNE .x11 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next 2147484032),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict 2147484052),
    .BNE .x11 .x0 (16 : BitVec 13),
    .SD .x18 .x10 (72 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerMinimalDecode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerMinimalDecode_relocs : RelocTable :=
  [ (8, .jal .x1 "rlp_walk_init"),
    (14, .jal .x1 "rlp_walk_next"),
    (30, .jal .x1 "rlp_walk_next"),
    (35, .jal .x1 "rlp_walk_next"),
    (40, .jal .x1 "rlp_walk_next"),
    (56, .jal .x1 "rlp_walk_next"),
    (61, .jal .x1 "rlp_walk_next"),
    (66, .jal .x1 "rlp_walk_next"),
    (71, .jal .x1 "rlp_walk_next"),
    (76, .jal .x1 "rlp_walk_next"),
    (81, .jal .x1 "rlp_content_to_u64_strict"),
    (86, .jal .x1 "rlp_walk_next"),
    (91, .jal .x1 "rlp_walk_next"),
    (96, .jal .x1 "rlp_walk_next"),
    (101, .jal .x1 "rlp_content_to_u64_strict") ]

def headerMinimalDecodeFunction : String :=
  "header_minimal_decode:\n" ++ emitProgramR headerMinimalDecode_prog headerMinimalDecode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerMinimalDecode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerMinimalDecodeFunction_eq_prog :
    headerMinimalDecodeFunction = "header_minimal_decode:\n" ++ emitProgramR headerMinimalDecode_prog headerMinimalDecode_relocs := rfl

#guard headerMinimalDecodeFunction.startsWith "header_minimal_decode:\n"
#guard headerMinimalDecode_prog.length = 114
/-- `zisk_header_minimal_decode`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 96-byte struct) to OUTPUT. -/
def ziskHeaderMinimalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 96 bytes.\n" ++
  "  mv t0, a2; li t1, 12\n" ++
  ".Lhmd_zinit:\n" ++
  "  beqz t1, .Lhmd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhmd_zinit\n" ++
  ".Lhmd_zdone:\n" ++
  "  jal ra, header_minimal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhmd_pdone\n" ++
  rlpWalkInitFunction ++ "\n" ++
  rlpWalkNextFunction ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  headerMinimalDecodeFunction ++ "\n" ++
  ".Lhmd_pdone:"

def ziskHeaderMinimalDecodeDataSection : String := ""


/-! ## header_extended_decode -- PR-K39

    Extends PR-K38 `header_minimal_decode` with three more
    STF-essential fields:

       0..32   parent_hash    (field 0)
      32..64   state_root     (field 3)
      64..72   number         (field 8, u64)
      72..80   timestamp      (field 11, u64)
      80..88   gas_limit      (field 9, u64)
      88..96   gas_used       (field 10, u64)
      96..128  base_fee_per_gas (field 15, u256 BE)
     128..136  blob_gas_used    (field 17, u64)
     136..144  excess_blob_gas  (field 18, u64)

    The base_fee_per_gas field exists from EIP-1559 (London)
    onward. Headers older than London don't have it; this
    function rejects (status=1) if field 15 doesn't exist.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header byte length
      a2 (input)  : 144-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail. -/
def headerExtendedDecode_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x18 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_extended_decode + 32)),
    .BNE .x12 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 36)),
    .MV .x9 .x11,
    .MV .x19 .x10,
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 56)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 64)),
    .LI .x5 (32 : Word),
    .BNE .x12 .x5 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 72)),
    .SUB .x28 .x10 .x12,
    .MV .x29 .x18,
    .LI .x5 (32 : Word),
    .LBU .x6 .x28 (0 : BitVec 12),
    .SB .x29 .x6 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-20 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 120)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 128)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 140)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 148)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 160)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 168)),
    .LI .x5 (32 : Word),
    .BNE .x12 .x5 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 176)),
    .SUB .x28 .x10 .x12,
    .ADDI .x29 .x18 (32 : BitVec 12),
    .LI .x5 (32 : Word),
    .LBU .x6 .x28 (0 : BitVec 12),
    .SB .x29 .x6 (0 : BitVec 12),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-20 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 224)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 232)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 244)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 252)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 264)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 272)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 284)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 292)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 304)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 312)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode + 324)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 328)),
    .SD .x18 .x10 (64 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 344)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 352)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode + 364)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 368)),
    .SD .x18 .x10 (80 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 384)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 392)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode + 404)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 408)),
    .SD .x18 .x10 (88 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 424)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 432)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode + 444)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 448)),
    .SD .x18 .x10 (72 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 464)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 472)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 484)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 492)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 504)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 512)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 524)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 532)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .ADDI .x12 .x18 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.header_extended_decode + 548)),
    .BNE .x10 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 552)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 564)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 572)),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 584)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode + 664) (GuestAddrs.header_extended_decode + 592)),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode + 604)),
    .BNE .x11 .x0 (56 : BitVec 13),
    .SD .x18 .x10 (128 : BitVec 12),
    .MV .x10 .x19,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.header_extended_decode + 624)),
    .MV .x19 .x10,
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x10 .x10 .x12,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode + 644)),
    .BNE .x11 .x0 (16 : BitVec 13),
    .SD .x18 .x10 (136 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtendedDecode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtendedDecode_relocs : RelocTable :=
  [ (8, .jal .x1 "rlp_walk_init"),
    (14, .jal .x1 "rlp_walk_next"),
    (30, .jal .x1 "rlp_walk_next"),
    (35, .jal .x1 "rlp_walk_next"),
    (40, .jal .x1 "rlp_walk_next"),
    (56, .jal .x1 "rlp_walk_next"),
    (61, .jal .x1 "rlp_walk_next"),
    (66, .jal .x1 "rlp_walk_next"),
    (71, .jal .x1 "rlp_walk_next"),
    (76, .jal .x1 "rlp_walk_next"),
    (81, .jal .x1 "rlp_content_to_u64_strict"),
    (86, .jal .x1 "rlp_walk_next"),
    (91, .jal .x1 "rlp_content_to_u64_strict"),
    (96, .jal .x1 "rlp_walk_next"),
    (101, .jal .x1 "rlp_content_to_u64_strict"),
    (106, .jal .x1 "rlp_walk_next"),
    (111, .jal .x1 "rlp_content_to_u64_strict"),
    (116, .jal .x1 "rlp_walk_next"),
    (121, .jal .x1 "rlp_walk_next"),
    (126, .jal .x1 "rlp_walk_next"),
    (131, .jal .x1 "rlp_walk_next"),
    (137, .jal .x1 "rlp_content_to_u256_be_strict"),
    (141, .jal .x1 "rlp_walk_next"),
    (146, .jal .x1 "rlp_walk_next"),
    (151, .jal .x1 "rlp_content_to_u64_strict"),
    (156, .jal .x1 "rlp_walk_next"),
    (161, .jal .x1 "rlp_content_to_u64_strict") ]

def headerExtendedDecodeFunction : String :=
  "header_extended_decode:\n" ++ emitProgramR headerExtendedDecode_prog headerExtendedDecode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtendedDecode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtendedDecodeFunction_eq_prog :
    headerExtendedDecodeFunction = "header_extended_decode:\n" ++ emitProgramR headerExtendedDecode_prog headerExtendedDecode_relocs := rfl

#guard headerExtendedDecodeFunction.startsWith "header_extended_decode:\n"
#guard headerExtendedDecode_prog.length = 174
/-! Leaf-only cursor wrapper used by the header checker.  The shared walker
    returns a list's full span at its item start; this wrapper preserves the
    normal `(cursor, status, length)` ABI but reports status 8 for a valid list
    item, so typed header fields cannot mistake a list span for a byte string. -/
def rlpWalkNextLeaf_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x10 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.rlp_walk_next_leaf + 12)),
    .BNE .x11 .x0 (32 : BitVec 13),
    .SUB .x5 .x10 .x12,
    .LD .x6 .x2 (8 : BitVec 12),
    .BNE .x5 .x6 (20 : BitVec 13),
    .LBU .x7 .x5 (0 : BitVec 12),
    .LI .x28 (192 : Word),
    .BLTU .x7 .x28 (8 : BitVec 13),
    .LI .x11 (8 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `rlpWalkNextLeaf_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def rlpWalkNextLeaf_relocs : RelocTable :=
  [ (3, .jal .x1 "rlp_walk_next") ]

def rlpWalkNextLeafFunction : String :=
  "rlp_walk_next_leaf:\n" ++ emitProgramR rlpWalkNextLeaf_prog rlpWalkNextLeaf_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `rlpWalkNextLeaf_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem rlpWalkNextLeafFunction_eq_prog :
    rlpWalkNextLeafFunction = "rlp_walk_next_leaf:\n" ++ emitProgramR rlpWalkNextLeaf_prog rlpWalkNextLeaf_relocs := rfl

#guard rlpWalkNextLeafFunction.startsWith "rlp_walk_next_leaf:\n"
#guard rlpWalkNextLeaf_prog.length = 15
/-! The checker is a separate single-entry routine so the conversion guard can
    keep the decoder and checker's global entry points explicit.  Its caller
    relocates to this symbol; the two functions are emitted consecutively in
    every header-decoder closure. -/
def headerExtendedDecodeArityCheck_prog : Program :=
  [ .ADDI .x2 .x2 (-96 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SUB .x11 .x9 .x8,
    .MV .x10 .x8,
    .ADDI .x12 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.header_extended_decode_arity_check + 48)),
    .BNE .x10 .x0 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 52)),
    .LD .x20 .x2 (64 : BitVec 12),
    .MV .x10 .x8,
    .SUB .x11 .x9 .x8,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.header_extended_decode_arity_check + 68)),
    .BNE .x12 .x0 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 72)),
    .MV .x18 .x10,
    .MV .x19 .x11,
    .LI .x5 (21 : Word),
    .BEQ .x20 .x5 (12 : BitVec 13),
    .LI .x5 (23 : Word),
    .BNE .x20 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 96)),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x20 (brOff (GuestAddrs.header_extended_decode_arity_check + 424) (GuestAddrs.header_extended_decode_arity_check + 104)),
    .MV .x10 .x18,
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.rlp_walk_next_leaf (GuestAddrs.header_extended_decode_arity_check + 116)),
    .BNE .x11 .x0 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 120)),
    .SUB .x22 .x10 .x12,
    .MV .x18 .x10,
    .LI .x5 (0 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 136)),
    .LI .x5 (1 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 144)),
    .LI .x5 (3 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 152)),
    .LI .x5 (4 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 160)),
    .LI .x5 (5 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 168)),
    .LI .x5 (13 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 176)),
    .LI .x5 (16 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 184)),
    .LI .x5 (19 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 192)),
    .LI .x5 (20 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 200)),
    .LI .x5 (21 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 312) (GuestAddrs.header_extended_decode_arity_check + 208)),
    .LI .x5 (2 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 324) (GuestAddrs.header_extended_decode_arity_check + 216)),
    .LI .x5 (6 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 336) (GuestAddrs.header_extended_decode_arity_check + 224)),
    .LI .x5 (14 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 348) (GuestAddrs.header_extended_decode_arity_check + 232)),
    .LI .x5 (11 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 396) (GuestAddrs.header_extended_decode_arity_check + 240)),
    .LI .x5 (17 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 376) (GuestAddrs.header_extended_decode_arity_check + 248)),
    .LI .x5 (18 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 376) (GuestAddrs.header_extended_decode_arity_check + 256)),
    .LI .x5 (22 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 376) (GuestAddrs.header_extended_decode_arity_check + 264)),
    .LI .x5 (7 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 360) (GuestAddrs.header_extended_decode_arity_check + 272)),
    .LI .x5 (8 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 360) (GuestAddrs.header_extended_decode_arity_check + 280)),
    .LI .x5 (9 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 360) (GuestAddrs.header_extended_decode_arity_check + 288)),
    .LI .x5 (10 : Word),
    .BEQ .x21 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 360) (GuestAddrs.header_extended_decode_arity_check + 296)),
    .LI .x5 (15 : Word),
    .BEQ .x21 .x5 (56 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.header_extended_decode_arity_check + 416) (GuestAddrs.header_extended_decode_arity_check + 308)),
    .LI .x5 (32 : Word),
    .BNE .x12 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 316)),
    .JAL .x0 (jalOff (GuestAddrs.header_extended_decode_arity_check + 416) (GuestAddrs.header_extended_decode_arity_check + 320)),
    .LI .x5 (20 : Word),
    .BNE .x12 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 328)),
    .JAL .x0 (jalOff (GuestAddrs.header_extended_decode_arity_check + 416) (GuestAddrs.header_extended_decode_arity_check + 332)),
    .LI .x5 (256 : Word),
    .BNE .x12 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 340)),
    .JAL .x0 (jalOff (GuestAddrs.header_extended_decode_arity_check + 416) (GuestAddrs.header_extended_decode_arity_check + 344)),
    .LI .x5 (8 : Word),
    .BNE .x12 .x5 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 352)),
    .JAL .x0 (60 : BitVec 21),
    .BEQ .x12 .x0 (56 : BitVec 13),
    .LBU .x5 .x22 (0 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.header_extended_decode_arity_check + 432) (GuestAddrs.header_extended_decode_arity_check + 368)),
    .JAL .x0 (44 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x12,
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u64_strict (GuestAddrs.header_extended_decode_arity_check + 384)),
    .BNE .x11 .x0 (44 : BitVec 13),
    .JAL .x0 (24 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x12,
    .ADDI .x12 .x2 (64 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.rlp_content_to_u256_be_strict (GuestAddrs.header_extended_decode_arity_check + 408)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.header_extended_decode_arity_check + 104) (GuestAddrs.header_extended_decode_arity_check + 420)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (96 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerExtendedDecodeArityCheck_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerExtendedDecodeArityCheck_relocs : RelocTable :=
  [ (12, .jal .x1 "rlp_list_count_items"),
    (17, .jal .x1 "rlp_walk_init"),
    (29, .jal .x1 "rlp_walk_next_leaf"),
    (96, .jal .x1 "rlp_content_to_u64_strict"),
    (102, .jal .x1 "rlp_content_to_u256_be_strict") ]

def headerExtendedDecodeArityCheckFunction : String :=
  "header_extended_decode_arity_check:\n" ++ emitProgramR headerExtendedDecodeArityCheck_prog headerExtendedDecodeArityCheck_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerExtendedDecodeArityCheck_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerExtendedDecodeArityCheckFunction_eq_prog :
    headerExtendedDecodeArityCheckFunction = "header_extended_decode_arity_check:\n" ++ emitProgramR headerExtendedDecodeArityCheck_prog headerExtendedDecodeArityCheck_relocs := rfl

#guard headerExtendedDecodeArityCheckFunction.startsWith "header_extended_decode_arity_check:\n"
#guard headerExtendedDecodeArityCheck_prog.length = 119
/-- `zisk_header_extended_decode`: probe BuildUnit. -/
def ziskHeaderExtendedDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 144 bytes.\n" ++
  "  mv t0, a2; li t1, 18\n" ++
  ".Lhed_zinit:\n" ++
  "  beqz t1, .Lhed_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhed_zinit\n" ++
  ".Lhed_zdone:\n" ++
  "  jal ra, header_extended_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhed_pdone\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpContentToU64StrictFunction ++ "\n" ++
  rlpWalkNextLeafFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  headerExtendedDecodeArityCheckFunction ++ "\n" ++
  ".Lhed_pdone:"

def ziskHeaderExtendedDecodeDataSection : String := ""


/-! ## coinbase_extract_from_header -- PR-K55 beneficiary getter

    Extract the 20-byte beneficiary (coinbase) address — field 2
    of an RLP-encoded block header. Direct input to
    `process_transaction`'s priority-fee credit:

      coinbase.balance += effective_priority_fee × gas_used

    The header decoders PR-K38 / PR-K39 read parent_hash,
    state_root, gas_limit, gas_used, etc., but skip the
    beneficiary since it isn't part of the STF skeleton's
    minimal/extended struct. This helper is the dedicated getter
    for callers that only need the coinbase.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a list or field
                    2 not 20 bytes). On failure, output is zeroed.

    Composes PR-K20 `rlp_list_nth_item`. Uses two 8-byte `.data`
    scratch slots (`ceh_offset`, `ceh_length`). -/
def coinbaseExtractFromHeaderFunction : String :=
  "coinbase_extract_from_header:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 20B ptr\n" ++
  "  # Get field 2 (coinbase) bounds.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, ceh_offset; la a4, ceh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lceh_fail\n" ++
  "  la t0, ceh_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lceh_fail\n" ++
  "  la t0, ceh_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  # Copy 20 bytes: 8 + 8 + 4 = 20.\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lceh_ret\n" ++
  ".Lceh_fail:\n" ++
  "  sd zero,  0(s2); sd zero, 8(s2); sw zero, 16(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lceh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_coinbase_extract_from_header`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 20B address + 4B pad) to OUTPUT (32 bytes total). -/
def ziskCoinbaseExtractFromHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 20B output at OUTPUT + 8\n" ++
  "  # Pre-zero the 20B output + 4B trailing pad.\n" ++
  "  mv t0, a2\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sw zero, 16(t0)\n" ++
  "  jal ra, coinbase_extract_from_header\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lceh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  coinbaseExtractFromHeaderFunction ++ "\n" ++
  ".Lceh_pdone:"

def ziskCoinbaseExtractFromHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ceh_offset:\n" ++
  "  .zero 8\n" ++
  "ceh_length:\n" ++
  "  .zero 8"



end EvmAsm.Codegen
