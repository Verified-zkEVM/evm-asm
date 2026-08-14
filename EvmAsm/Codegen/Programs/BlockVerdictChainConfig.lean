/-
  EvmAsm.Codegen.Programs.BlockVerdictChainConfig

  Assembly helpers for stateless-input structural validation:
  public_keys_valid and chain_config_valid.
  Carved out of BlockVerdict.lean to stay within the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## public_keys_valid -- structural stateless-input public key guard.
    a0 = SSZ_BASE   a1 = exec_payload ptr
    a0 (output) = 0 ok, 1 malformed/mismatched public_keys.

    Amsterdam passes `stateless_input.public_keys` to `execute_block`; the
    executable spec rejects if the count differs from the transaction count,
    and then compares each supplied 65-byte uncompressed SEC1 public key against
    recovered transaction keys. This guard implements the count check plus the
    cheap canonical shape checks that catch malformed optional-proof fixtures:
    each key is exactly an SSZ fixed 65-byte entry, starts with 0x04, and does
    not have an all-zero 64-byte coordinate payload. -/
def publicKeysValid_prog : Program :=
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
    .ADDI .x10 .x9 (504 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.public_keys_valid + 60)),
    .MV .x18 .x10,
    .ADDI .x10 .x9 (508 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.public_keys_valid + 72)),
    .MV .x19 .x10,
    .LI .x20 (0 : Word),
    .BGEU .x18 .x19 (48 : BitVec 13),
    .SUB .x5 .x19 .x18,
    .LI .x6 (4 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.public_keys_valid + 308) (GuestAddrs.public_keys_valid + 96)),
    .ADD .x7 .x9 .x18,
    .MV .x10 .x7,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.public_keys_valid + 108)),
    .ANDI .x6 .x10 (3 : BitVec 12),
    .BNE .x6 .x0 (brOff (GuestAddrs.public_keys_valid + 308) (GuestAddrs.public_keys_valid + 116)),
    .SRLI .x20 .x10 (2 : BitVec 6),
    .SLLI .x6 .x20 (2 : BitVec 6),
    .BLTU .x5 .x6 (brOff (GuestAddrs.public_keys_valid + 308) (GuestAddrs.public_keys_valid + 128)),
    .ADDI .x10 .x8 (12 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.public_keys_valid + 136)),
    .ADD .x21 .x8 .x10,
    .LUI .x10 (262144 : BitVec 20),
    .ADDIW .x10 .x10 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.public_keys_valid + 152)),
    .LUI .x5 (262144 : BitVec 20),
    .ADDIW .x5 .x5 (16 : BitVec 12),
    .ADD .x22 .x5 .x10,
    .BLTU .x22 .x21 (brOff (GuestAddrs.public_keys_valid + 308) (GuestAddrs.public_keys_valid + 168)),
    .SUB .x23 .x22 .x21,
    .LI .x5 (65 : Word),
    .REMU .x6 .x23 .x5,
    .BNE .x6 .x0 (brOff (GuestAddrs.public_keys_valid + 308) (GuestAddrs.public_keys_valid + 184)),
    .DIVU .x24 .x23 .x5,
    .BNE .x24 .x20 (brOff (GuestAddrs.public_keys_valid + 308) (GuestAddrs.public_keys_valid + 192)),
    .AUIPC .x5 (laHi GuestAddrs.bv_public_keys_ptr (GuestAddrs.public_keys_valid + 196)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_public_keys_ptr (GuestAddrs.public_keys_valid + 196)),
    .SD .x5 .x21 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bv_public_keys_len (GuestAddrs.public_keys_valid + 208)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_public_keys_len (GuestAddrs.public_keys_valid + 208)),
    .SD .x5 .x23 (0 : BitVec 12),
    .LI .x25 (0 : Word),
    .BEQ .x25 .x20 (brOff (GuestAddrs.public_keys_valid + 300) (GuestAddrs.public_keys_valid + 224)),
    .LI .x5 (65 : Word),
    .MUL .x6 .x25 .x5,
    .ADD .x7 .x21 .x6,
    .LBU .x28 .x7 (0 : BitVec 12),
    .LI .x29 (4 : Word),
    .BNE .x28 .x29 (60 : BitVec 13),
    .LI .x28 (1 : Word),
    .LI .x29 (0 : Word),
    .LI .x30 (65 : Word),
    .BEQ .x28 .x30 (24 : BitVec 13),
    .ADD .x31 .x7 .x28,
    .LBU .x31 .x31 (0 : BitVec 12),
    .OR .x29 .x29 .x31,
    .ADDI .x28 .x28 (1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .BEQ .x29 .x0 (20 : BitVec 13),
    .ADDI .x25 .x25 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.public_keys_valid + 224) (GuestAddrs.public_keys_valid + 296)),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
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

/-- Reloc side-table for `publicKeysValid_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def publicKeysValid_relocs : RelocTable :=
  [ (15, .jal .x1 "bgv_u32le"),
    (18, .jal .x1 "bgv_u32le"),
    (27, .jal .x1 "bgv_u32le"),
    (34, .jal .x1 "bgv_u32le"),
    (38, .jal .x1 "bgv_u64le"),
    (49, .la .x5 "bv_public_keys_ptr"),
    (52, .la .x5 "bv_public_keys_len") ]

def publicKeysValidFunction : String :=
  "public_keys_valid:\n" ++ emitProgramR publicKeysValid_prog publicKeysValid_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `publicKeysValid_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem publicKeysValidFunction_eq_prog :
    publicKeysValidFunction = "public_keys_valid:\n" ++ emitProgramR publicKeysValid_prog publicKeysValid_relocs := rfl

#guard publicKeysValidFunction.startsWith "public_keys_valid:\n"
/-! ## chain_config_valid -- execution-specs validate_chain_config mirror
    (tests-zkevm@v0.6.0, 40f956fab: `ForkConfig` = `{activation}`; the
    Amsterdam-fork and blob-schedule checks are DELETED upstream — fork
    identity travels in the schema id).
    a0 = SSZ_BASE   a1 = exec_payload ptr
    a0 (output) = 0 ok, 1 inactive/malformed chain_config.

    This checks the Amsterdam stateless guest's semantic chain-config contract:
    activation sets block_number or timestamp and is active for the target
    payload. -/
def chainConfigValid_prog : Program :=
  [ .ADDI .x2 .x2 (-112 : BitVec 12),
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
    .SD .x2 .x26 (88 : BitVec 12),
    .SD .x2 .x27 (96 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 68)),
    .ADD .x18 .x8 .x10,
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 80)),
    .AUIPC .x5 (laHi GuestAddrs.bv_chain_id (GuestAddrs.chain_config_valid + 84)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bv_chain_id (GuestAddrs.chain_config_valid + 84)),
    .SD .x5 .x10 (0 : BitVec 12),
    .ADDI .x10 .x8 (12 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 100)),
    .ADD .x19 .x8 .x10,
    .BLTU .x19 .x18 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 108)),
    .SUB .x5 .x19 .x18,
    .LI .x6 (12 : Word),
    .BLTU .x5 .x6 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 120)),
    .ADDI .x10 .x18 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 128)),
    .LI .x5 (12 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 136)),
    .ADD .x20 .x18 .x10,
    .BLTU .x19 .x20 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 144)),
    .SUB .x26 .x19 .x20,
    .LI .x5 (12 : Word),
    .BLTU .x26 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 156)),
    .MV .x10 .x20,
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 164)),
    .LI .x5 (4 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 172)),
    .ADDI .x21 .x20 (4 : BitVec 12),
    .ADDI .x22 .x26 (-4 : BitVec 12),
    .LI .x5 (8 : Word),
    .BEQ .x22 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 188)),
    .LI .x5 (16 : Word),
    .BEQ .x22 .x5 (16 : BitVec 13),
    .LI .x5 (24 : Word),
    .BEQ .x22 .x5 (52 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 208)),
    .ADDI .x10 .x21 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 216)),
    .LI .x5 (8 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 224)),
    .ADDI .x10 .x21 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 232)),
    .LI .x5 (8 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 368) (GuestAddrs.chain_config_valid + 240)),
    .LI .x5 (16 : Word),
    .BEQ .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 340) (GuestAddrs.chain_config_valid + 248)),
    .JAL .x0 (jalOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 252)),
    .ADDI .x10 .x21 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 260)),
    .LI .x5 (8 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 268)),
    .ADDI .x10 .x21 (4 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u32le (GuestAddrs.chain_config_valid + 276)),
    .LI .x5 (16 : Word),
    .BNE .x10 .x5 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 284)),
    .ADDI .x10 .x21 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 292)),
    .MV .x25 .x10,
    .ADDI .x10 .x9 (404 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 304)),
    .BLTU .x10 .x25 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 308)),
    .ADDI .x10 .x21 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 316)),
    .MV .x25 .x10,
    .ADDI .x10 .x9 (428 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 328)),
    .BLTU .x10 .x25 (brOff (GuestAddrs.chain_config_valid + 400) (GuestAddrs.chain_config_valid + 332)),
    .JAL .x0 (56 : BitVec 21),
    .ADDI .x10 .x21 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 344)),
    .MV .x25 .x10,
    .ADDI .x10 .x9 (404 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 356)),
    .BLTU .x10 .x25 (40 : BitVec 13),
    .JAL .x0 (28 : BitVec 21),
    .ADDI .x10 .x21 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 372)),
    .MV .x25 .x10,
    .ADDI .x10 .x9 (428 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bgv_u64le (GuestAddrs.chain_config_valid + 384)),
    .BLTU .x10 .x25 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
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
    .LD .x26 .x2 (88 : BitVec 12),
    .LD .x27 .x2 (96 : BitVec 12),
    .ADDI .x2 .x2 (112 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `chainConfigValid_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def chainConfigValid_relocs : RelocTable :=
  [ (17, .jal .x1 "bgv_u32le"),
    (20, .jal .x1 "bgv_u64le"),
    (21, .la .x5 "bv_chain_id"),
    (25, .jal .x1 "bgv_u32le"),
    (32, .jal .x1 "bgv_u32le"),
    (41, .jal .x1 "bgv_u32le"),
    (54, .jal .x1 "bgv_u32le"),
    (58, .jal .x1 "bgv_u32le"),
    (65, .jal .x1 "bgv_u32le"),
    (69, .jal .x1 "bgv_u32le"),
    (73, .jal .x1 "bgv_u64le"),
    (76, .jal .x1 "bgv_u64le"),
    (79, .jal .x1 "bgv_u64le"),
    (82, .jal .x1 "bgv_u64le"),
    (86, .jal .x1 "bgv_u64le"),
    (89, .jal .x1 "bgv_u64le"),
    (93, .jal .x1 "bgv_u64le"),
    (96, .jal .x1 "bgv_u64le") ]

def chainConfigValidFunction : String :=
  "chain_config_valid:\n" ++ emitProgramR chainConfigValid_prog chainConfigValid_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `chainConfigValid_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem chainConfigValidFunction_eq_prog :
    chainConfigValidFunction = "chain_config_valid:\n" ++ emitProgramR chainConfigValid_prog chainConfigValid_relocs := rfl

#guard chainConfigValidFunction.startsWith "chain_config_valid:\n"
end EvmAsm.Codegen
