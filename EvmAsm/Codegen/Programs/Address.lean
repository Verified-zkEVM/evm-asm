/-
  EvmAsm.Codegen.Programs.Address

  Ethereum address-derivation helpers extracted from
  `EvmAsm.Codegen.Programs` per the file-size hard cap. Hosts the
  three canonical address builders:

    K99   address_from_pubkey
    K126  address_compute_create2
    K127  address_compute_create

  All three are `keccak256`-based; the new module only needs the
  `Rv64.Program` core, `Codegen.Layout`, and the `HashBridge` for
  the keccak intrinsic wrapper.

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

/-! ## address_from_pubkey -- PR-K99

    Compute an Ethereum address from an uncompressed secp256k1
    public key:

      address = keccak256(pubkey_x ‖ pubkey_y)[12:32]   (20 bytes)

    This is the canonical 20-byte address derivation used by:
    - secp256k1 ecrecover (the final step after curve recovery)
    - CREATE / CREATE2 address computation (with different inputs)
    - Account address generation from a key

    Input layout (64 bytes, big-endian):
       0..32  : X coordinate
      32..64  : Y coordinate

    Output (20 bytes): the rightmost 20 bytes of keccak256 of the
    above. The leading 12 bytes of the digest are discarded.

    Composes PR-K3 `zkvm_keccak256`. Uses 32 bytes of `.data`
    scratch (`afp_digest`).

    Calling convention:
      a0 (input)  : pubkey ptr (64 bytes, x ‖ y BE)
      a1 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds; keccak is total). -/
def addressFromPubkey_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x11,
    .LI .x11 (64 : Word),
    .AUIPC .x12 (laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)),
    .ADDI .x12 .x12 (laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_from_pubkey + 28)),
    .AUIPC .x5 (laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)),
    .LD .x6 .x5 (12 : BitVec 12),
    .SD .x8 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (20 : BitVec 12),
    .SD .x8 .x6 (8 : BitVec 12),
    .LWU .x6 .x5 (28 : BitVec 12),
    .SW .x8 .x6 (16 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `addressFromPubkey_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def addressFromPubkey_relocs : RelocTable :=
  [ (5, .la .x12 "afp_digest"),
    (7, .jal .x1 "zkvm_keccak256"),
    (8, .la .x5 "afp_digest") ]

def addressFromPubkeyFunction : String :=
  "address_from_pubkey:\n" ++ emitProgramR addressFromPubkey_prog addressFromPubkey_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `addressFromPubkey_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem addressFromPubkeyFunction_eq_prog :
    addressFromPubkeyFunction = "address_from_pubkey:\n" ++ emitProgramR addressFromPubkey_prog addressFromPubkey_relocs := rfl

#guard addressFromPubkeyFunction.startsWith "address_from_pubkey:\n"
#guard addressFromPubkey_prog.length = 21
/-- `zisk_address_from_pubkey`: probe BuildUnit. Reads 64 bytes
    of pubkey from host input, writes (status, 20-byte address +
    4 byte padding) to OUTPUT (32 bytes total). -/
def ziskAddressFromPubkeyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 16             # pubkey ptr\n" ++
  "  li a1, 0xa0010008           # 20B address output\n" ++
  "  sd zero, 0(a1); sd zero, 8(a1); sw zero, 16(a1)\n" ++
  "  jal ra, address_from_pubkey\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lafp_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  ".Lafp_pdone:"

def ziskAddressFromPubkeyDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "afp_digest:\n" ++
  "  .zero 32"

def ziskAddressFromPubkeyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAddressFromPubkeyPrologue
  dataAsm     := ziskAddressFromPubkeyDataSection
}

/-! ## address_compute_create2 -- PR-K126

    Compute the CREATE2 contract address per EIP-1014:

      address = keccak256(0xff || sender || salt || keccak256(init_code))[12:32]

    Preimage is exactly 85 bytes laid out as:
       0       :  0xff (single byte marker)
       1..21   :  sender (20 bytes)
       21..53  :  salt (32 bytes, BE)
       53..85  :  inner_hash = keccak256(init_code) (32 bytes)

    Used by the EVM's `CREATE2` opcode and by off-chain tooling
    that needs deterministic deploy addresses. Sister primitive to
    PR-K99 `address_from_pubkey` (the ECRECOVER trailing step) and
    a future `address_compute_create` (for the non-deterministic
    nonce-based form).

    Composes PR-K3 `zkvm_keccak256` (called twice — once over
    `init_code` and once over the 85-byte preimage).

    Calling convention:
      a0 (input)  : sender ptr (20 B, big-endian)
      a1 (input)  : salt ptr   (32 B, big-endian)
      a2 (input)  : init_code ptr
      a3 (input)  : init_code byte length
      a4 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds; keccak is total).

    Uses 85 + 32 + 32 = 149 bytes of `.data` scratch
    (`ac2_preimage` 85 B + `ac2_inner_digest` 32 B + `ac2_outer_digest`
    32 B), plus the keccak sponge state (`zk3_state`, 200 B). -/
def addressComputeCreate2_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x20 .x14,
    .MV .x10 .x12,
    .MV .x11 .x13,
    .AUIPC .x12 (laHi GuestAddrs.ac2_inner_digest (GuestAddrs.address_compute_create2 + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ac2_inner_digest (GuestAddrs.address_compute_create2 + 48)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_compute_create2 + 56)),
    .AUIPC .x18 (laHi GuestAddrs.ac2_preimage (GuestAddrs.address_compute_create2 + 60)),
    .ADDI .x18 .x18 (laLo GuestAddrs.ac2_preimage (GuestAddrs.address_compute_create2 + 60)),
    .LI .x5 (255 : Word),
    .SB .x18 .x5 (0 : BitVec 12),
    .LD .x5 .x8 (0 : BitVec 12),
    .SD .x18 .x5 (1 : BitVec 12),
    .LD .x5 .x8 (8 : BitVec 12),
    .SD .x18 .x5 (9 : BitVec 12),
    .LWU .x5 .x8 (16 : BitVec 12),
    .SW .x18 .x5 (17 : BitVec 12),
    .LD .x5 .x9 (0 : BitVec 12),
    .SD .x18 .x5 (21 : BitVec 12),
    .LD .x5 .x9 (8 : BitVec 12),
    .SD .x18 .x5 (29 : BitVec 12),
    .LD .x5 .x9 (16 : BitVec 12),
    .SD .x18 .x5 (37 : BitVec 12),
    .LD .x5 .x9 (24 : BitVec 12),
    .SD .x18 .x5 (45 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.ac2_inner_digest (GuestAddrs.address_compute_create2 + 132)),
    .ADDI .x6 .x6 (laLo GuestAddrs.ac2_inner_digest (GuestAddrs.address_compute_create2 + 132)),
    .LD .x5 .x6 (0 : BitVec 12),
    .SD .x18 .x5 (53 : BitVec 12),
    .LD .x5 .x6 (8 : BitVec 12),
    .SD .x18 .x5 (61 : BitVec 12),
    .LD .x5 .x6 (16 : BitVec 12),
    .SD .x18 .x5 (69 : BitVec 12),
    .LD .x5 .x6 (24 : BitVec 12),
    .SD .x18 .x5 (77 : BitVec 12),
    .MV .x10 .x18,
    .LI .x11 (85 : Word),
    .AUIPC .x12 (laHi GuestAddrs.ac2_outer_digest (GuestAddrs.address_compute_create2 + 180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ac2_outer_digest (GuestAddrs.address_compute_create2 + 180)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_compute_create2 + 188)),
    .AUIPC .x5 (laHi GuestAddrs.ac2_outer_digest (GuestAddrs.address_compute_create2 + 192)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ac2_outer_digest (GuestAddrs.address_compute_create2 + 192)),
    .LD .x6 .x5 (12 : BitVec 12),
    .SD .x20 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (20 : BitVec 12),
    .SD .x20 .x6 (8 : BitVec 12),
    .LWU .x6 .x5 (28 : BitVec 12),
    .SW .x20 .x6 (16 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `addressComputeCreate2_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def addressComputeCreate2_relocs : RelocTable :=
  [ (12, .la .x12 "ac2_inner_digest"),
    (14, .jal .x1 "zkvm_keccak256"),
    (15, .la .x18 "ac2_preimage"),
    (33, .la .x6 "ac2_inner_digest"),
    (45, .la .x12 "ac2_outer_digest"),
    (47, .jal .x1 "zkvm_keccak256"),
    (48, .la .x5 "ac2_outer_digest") ]

def addressComputeCreate2Function : String :=
  "address_compute_create2:\n" ++ emitProgramR addressComputeCreate2_prog addressComputeCreate2_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `addressComputeCreate2_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem addressComputeCreate2Function_eq_prog :
    addressComputeCreate2Function = "address_compute_create2:\n" ++ emitProgramR addressComputeCreate2_prog addressComputeCreate2_relocs := rfl

#guard addressComputeCreate2Function.startsWith "address_compute_create2:\n"
#guard addressComputeCreate2_prog.length = 65
/-- `zisk_address_compute_create2`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : init_code length
      bytes  8..28 : sender (20 bytes)
      bytes 28..60 : salt (32 bytes)
      bytes 60..   : init_code bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..28 : 20-byte address
      bytes 28..32 : padding -/
def ziskAddressComputeCreate2Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a3, 8(a5)                # init_code length\n" ++
  "  addi a0, a5, 16             # sender ptr\n" ++
  "  addi a1, a5, 36             # salt ptr\n" ++
  "  addi a2, a5, 68             # init_code ptr\n" ++
  "  li a4, 0xa0010008           # 20B address output\n" ++
  "  sd zero, 0(a4); sd zero, 8(a4); sw zero, 16(a4)\n" ++
  "  jal ra, address_compute_create2\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lac2_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreate2Function ++ "\n" ++
  ".Lac2_pdone:"

def ziskAddressComputeCreate2DataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "ac2_inner_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_outer_digest:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac2_preimage:\n" ++
  "  .zero 88"  -- 85 + 3 padding for 8-byte alignment of next

def ziskAddressComputeCreate2ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAddressComputeCreate2Prologue
  dataAsm     := ziskAddressComputeCreate2DataSection
}

/-! ## address_compute_create -- PR-K127

    Compute the CREATE contract address (non-deterministic form):

      address = keccak256(rlp.encode([sender, nonce]))[12:32]

    Used by:
    - the EVM's `CREATE` opcode (when a contract creates another)
    - the tx-level contract-creation path (when `tx.to == empty`),
      where `sender` is the tx sender (recovered via ECRECOVER)
      and `nonce` is the sender's pre-tx account nonce.

    Sister primitive to PR-K126 `address_compute_create2` (the
    deterministic salt-based form). EIP-2681 caps `nonce` at
    `2^64 - 1` so the u64 input always fits the RLP encoding's
    1+8-byte upper bound.

    RLP encoding of `[sender, nonce]`:
      [0]   : list prefix = 0xc0 + payload_len
      [1]   : sender prefix = 0x94 (20-byte string marker)
      [2..22] : sender 20 bytes
      [22..] : nonce RLP, one of:
        nonce == 0       : single byte 0x80
        nonce in 1..127  : single byte = nonce
        nonce >= 128     : 0x80 + bc, then `bc` BE-encoded bytes,
                           where `bc ∈ {1..8}` (= effective byte
                           count, no leading zeros)

    Payload (sender_rlp + nonce_rlp) is at most 21 + 9 = 30 bytes,
    so the list prefix is always the short form `0xc0..0xde`.

    Composes PR-K3 `zkvm_keccak256`. Uses 32 + 8 + 32 bytes of
    `.data` scratch (`ac_buffer` for the RLP, `ac_nonce_be` for
    long-form byte counting, `ac_digest` for keccak output).

    Calling convention:
      a0 (input)  : sender ptr (20 B, big-endian)
      a1 (input)  : nonce (u64)
      a2 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) : 0 (always succeeds; keccak is total). -/
def addressComputeCreate_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x5 (laHi GuestAddrs.ac_buffer (GuestAddrs.address_compute_create + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ac_buffer (GuestAddrs.address_compute_create + 32)),
    .LI .x6 (148 : Word),
    .SB .x5 .x6 (1 : BitVec 12),
    .LD .x6 .x8 (0 : BitVec 12),
    .SD .x5 .x6 (2 : BitVec 12),
    .LD .x6 .x8 (8 : BitVec 12),
    .SD .x5 .x6 (10 : BitVec 12),
    .LWU .x6 .x8 (16 : BitVec 12),
    .SW .x5 .x6 (18 : BitVec 12),
    .BEQ .x9 .x0 (24 : BitVec 13),
    .LI .x6 (128 : Word),
    .BGEU .x9 .x6 (32 : BitVec 13),
    .SB .x5 .x9 (22 : BitVec 12),
    .LI .x7 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.address_compute_create + 264) (GuestAddrs.address_compute_create + 92)),
    .LI .x6 (128 : Word),
    .SB .x5 .x6 (22 : BitVec 12),
    .LI .x7 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.address_compute_create + 264) (GuestAddrs.address_compute_create + 108)),
    .AUIPC .x28 (laHi GuestAddrs.ac_nonce_be (GuestAddrs.address_compute_create + 112)),
    .ADDI .x28 .x28 (laLo GuestAddrs.ac_nonce_be (GuestAddrs.address_compute_create + 112)),
    .SRLI .x29 .x9 (56 : BitVec 6),
    .SB .x28 .x29 (0 : BitVec 12),
    .SRLI .x29 .x9 (48 : BitVec 6),
    .SB .x28 .x29 (1 : BitVec 12),
    .SRLI .x29 .x9 (40 : BitVec 6),
    .SB .x28 .x29 (2 : BitVec 12),
    .SRLI .x29 .x9 (32 : BitVec 6),
    .SB .x28 .x29 (3 : BitVec 12),
    .SRLI .x29 .x9 (24 : BitVec 6),
    .SB .x28 .x29 (4 : BitVec 12),
    .SRLI .x29 .x9 (16 : BitVec 6),
    .SB .x28 .x29 (5 : BitVec 12),
    .SRLI .x29 .x9 (8 : BitVec 6),
    .SB .x28 .x29 (6 : BitVec 12),
    .SB .x28 .x9 (7 : BitVec 12),
    .LI .x29 (0 : Word),
    .ADD .x30 .x28 .x29,
    .LBU .x31 .x30 (0 : BitVec 12),
    .BNE .x31 .x0 (12 : BitVec 13),
    .ADDI .x29 .x29 (1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .LI .x30 (8 : Word),
    .SUB .x7 .x30 .x29,
    .ADDI .x30 .x7 (128 : BitVec 12),
    .SB .x5 .x30 (22 : BitVec 12),
    .ADDI .x31 .x5 (23 : BitVec 12),
    .ADD .x30 .x28 .x29,
    .MV .x6 .x7,
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x29 .x30 (0 : BitVec 12),
    .SB .x31 .x29 (0 : BitVec 12),
    .ADDI .x30 .x30 (1 : BitVec 12),
    .ADDI .x31 .x31 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x6 .x7 (21 : BitVec 12),
    .ADDI .x28 .x6 (192 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x11 .x7 (22 : BitVec 12),
    .MV .x10 .x5,
    .AUIPC .x12 (laHi GuestAddrs.ac_digest (GuestAddrs.address_compute_create + 284)),
    .ADDI .x12 .x12 (laLo GuestAddrs.ac_digest (GuestAddrs.address_compute_create + 284)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_compute_create + 292)),
    .AUIPC .x5 (laHi GuestAddrs.ac_digest (GuestAddrs.address_compute_create + 296)),
    .ADDI .x5 .x5 (laLo GuestAddrs.ac_digest (GuestAddrs.address_compute_create + 296)),
    .LD .x6 .x5 (12 : BitVec 12),
    .SD .x18 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (20 : BitVec 12),
    .SD .x18 .x6 (8 : BitVec 12),
    .LWU .x6 .x5 (28 : BitVec 12),
    .SW .x18 .x6 (16 : BitVec 12),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `addressComputeCreate_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def addressComputeCreate_relocs : RelocTable :=
  [ (8, .la .x5 "ac_buffer"),
    (28, .la .x28 "ac_nonce_be"),
    (71, .la .x12 "ac_digest"),
    (73, .jal .x1 "zkvm_keccak256"),
    (74, .la .x5 "ac_digest") ]

def addressComputeCreateFunction : String :=
  "address_compute_create:\n" ++ emitProgramR addressComputeCreate_prog addressComputeCreate_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `addressComputeCreate_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem addressComputeCreateFunction_eq_prog :
    addressComputeCreateFunction = "address_compute_create:\n" ++ emitProgramR addressComputeCreate_prog addressComputeCreate_relocs := rfl

#guard addressComputeCreateFunction.startsWith "address_compute_create:\n"
#guard addressComputeCreate_prog.length = 89
/-- `zisk_address_compute_create`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : nonce (u64)
      bytes  8..28 : sender (20 bytes)
    Output layout:
      bytes  0.. 8 : status
      bytes  8..28 : 20-byte address
      bytes 28..32 : padding -/
def ziskAddressComputeCreatePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # nonce\n" ++
  "  addi a0, a3, 16             # sender ptr\n" ++
  "  li a2, 0xa0010008           # 20B address output\n" ++
  "  sd zero, 0(a2); sd zero, 8(a2); sw zero, 16(a2)\n" ++
  "  jal ra, address_compute_create\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lac_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressComputeCreateFunction ++ "\n" ++
  ".Lac_pdone:"

def ziskAddressComputeCreateDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "ac_buffer:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "ac_digest:\n" ++
  "  .zero 32"

def ziskAddressComputeCreateProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAddressComputeCreatePrologue
  dataAsm     := ziskAddressComputeCreateDataSection
}


end EvmAsm.Codegen
