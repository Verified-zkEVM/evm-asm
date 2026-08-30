/-
  EvmAsm.Codegen.Programs.TxExtractTail

  Tail transaction helpers extracted from TxExtract to keep each
  Codegen/Programs module below the file-size cap. Public names and
  emitted strings are unchanged.
-/

import EvmAsm.Codegen.Programs.TxExtractBase
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_effective_gas_pricing -- EEST reusable fee pricing

    Compose `tx_extract_gas_pricing` with the u256 fee-pricing helpers to
    produce the values needed by general transaction settlement:

      priority_fee_per_gas = min(max_priority_fee, max_fee - base_fee)
      effective_gas_price  = base_fee + priority_fee_per_gas

    `tx_extract_gas_pricing` normalizes legacy and EIP-2930 `gas_price` by
    writing it to both max-priority and max-fee outputs, so the same formula
    gives `effective_gas_price = gas_price` and
    `priority_fee_per_gas = gas_price - base_fee`.

    Calling convention:
      a0 (input)  : tx bytes ptr
      a1 (input)  : tx byte length
      a2 (input)  : base_fee_per_gas ptr (32 B BE)
      a3 (input)  : effective_gas_price out ptr (32 B BE)
      a4 (input)  : priority_fee_per_gas out ptr (32 B BE)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : tx pricing extraction failed
        2 : max_fee_per_gas < max_priority_fee_per_gas
        3 : max_fee_per_gas < base_fee_per_gas
        4 : effective_gas_price addition overflowed -/
def txEffectiveGasPricing_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x12,
    .MV .x9 .x13,
    .MV .x18 .x14,
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 68)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 68)),
    .AUIPC .x13 (laHi GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 76)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 76)),
    .JAL .x1 (jalOff GuestAddrs.tx_extract_gas_pricing (GuestAddrs.tx_effective_gas_pricing + 84)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_effective_gas_pricing + 244) (GuestAddrs.tx_effective_gas_pricing + 96)),
    .AUIPC .x10 (laHi GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 100)),
    .AUIPC .x11 (laHi GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 108)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 108)),
    .AUIPC .x12 (laHi GuestAddrs.tefgp_tmp (GuestAddrs.tx_effective_gas_pricing + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tefgp_tmp (GuestAddrs.tx_effective_gas_pricing + 116)),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.tx_effective_gas_pricing + 124)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (jalOff (GuestAddrs.tx_effective_gas_pricing + 244) (GuestAddrs.tx_effective_gas_pricing + 136)),
    .AUIPC .x10 (laHi GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 140)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tefgp_max_priority (GuestAddrs.tx_effective_gas_pricing + 140)),
    .AUIPC .x11 (laHi GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 148)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tefgp_max_fee (GuestAddrs.tx_effective_gas_pricing + 148)),
    .MV .x12 .x8,
    .MV .x13 .x18,
    .JAL .x1 (jalOff GuestAddrs.priority_fee_per_gas_eip1559 (GuestAddrs.tx_effective_gas_pricing + 164)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x18 .x0 (8 : BitVec 12),
    .SD .x18 .x0 (16 : BitVec 12),
    .SD .x18 .x0 (24 : BitVec 12),
    .LI .x10 (3 : Word),
    .JAL .x0 (52 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.tx_effective_gas_pricing + 208)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .SD .x9 .x0 (0 : BitVec 12),
    .SD .x9 .x0 (8 : BitVec 12),
    .SD .x9 .x0 (16 : BitVec 12),
    .SD .x9 .x0 (24 : BitVec 12),
    .LI .x10 (4 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txEffectiveGasPricing_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txEffectiveGasPricing_relocs : RelocTable :=
  [ (17, .la .x12 "tefgp_max_priority"),
    (19, .la .x13 "tefgp_max_fee"),
    (21, .jal .x1 "tx_extract_gas_pricing"),
    (25, .la .x10 "tefgp_max_fee"),
    (27, .la .x11 "tefgp_max_priority"),
    (29, .la .x12 "tefgp_tmp"),
    (31, .jal .x1 "u256_sub_be"),
    (35, .la .x10 "tefgp_max_priority"),
    (37, .la .x11 "tefgp_max_fee"),
    (41, .jal .x1 "priority_fee_per_gas_eip1559"),
    (52, .jal .x1 "u256_add_be") ]

def txEffectiveGasPricingFunction : String :=
  "tx_effective_gas_pricing:\n" ++ emitProgramR txEffectiveGasPricing_prog txEffectiveGasPricing_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txEffectiveGasPricing_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txEffectiveGasPricingFunction_eq_prog :
    txEffectiveGasPricingFunction = "tx_effective_gas_pricing:\n" ++ emitProgramR txEffectiveGasPricing_prog txEffectiveGasPricing_relocs := rfl

#guard txEffectiveGasPricingFunction.startsWith "tx_effective_gas_pricing:\n"
#guard txEffectiveGasPricing_prog.length = 68
/-! ## access_list_count -- PR-K48 EIP-2930+ access-list cardinality

    Walk an RLP-encoded EIP-2930+ access_list and return
    `(num_addresses, num_storage_keys)`. These are the two
    inputs to the EIP-2930+ intrinsic-gas formula:

      gas_access_list = 2400 × num_addresses + 1900 × num_storage_keys

    Access-list shape:

      access_list = [
        [address (20 B), [slot1 (32 B), slot2 (32 B), ...]],
        ...
      ]

    Both `access_list` and each per-address `[slots...]` sub-list
    are RLP lists. This helper composes:

      1. PR-K47 `rlp_list_count_items` on the outer access_list to
         get N = num_addresses (and validate the outer shape).
      2. PR-K20 `rlp_list_nth_item` to extract each entry's bounds.
      3. PR-K20 `rlp_list_nth_item` on each entry to get field 1
         (the slots sub-list).
      4. PR-K47 `rlp_list_count_items` on the slots sub-list to add
         to num_storage_keys.

    Empty access_list (`0xc0`) → (0, 0).

    Calling convention:
      a0 (input)  : access_list bytes ptr (whole encoded item incl.
                    outer RLP list prefix)
      a1 (input)  : access_list byte length
      a2 (input)  : u64 out ptr for num_addresses
      a3 (input)  : u64 out ptr for num_storage_keys
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail.

    Uses three 8-byte `.data` scratch slots
    (`alc_scratch`, `alc_entry_offset`, `alc_entry_length`,
    `alc_keys_offset`, `alc_keys_length`). -/
def accessListCount_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 64)),
    .ADDI .x12 .x12 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 64)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.access_list_count + 72)),
    .BNE .x10 .x0 (brOff (GuestAddrs.access_list_count + 304) (GuestAddrs.access_list_count + 76)),
    .AUIPC .x5 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 80)),
    .LD .x20 .x5 (0 : BitVec 12),
    .BEQ .x20 .x0 (brOff (GuestAddrs.access_list_count + 292) (GuestAddrs.access_list_count + 92)),
    .LI .x21 (0 : Word),
    .BEQ .x21 .x20 (brOff (GuestAddrs.access_list_count + 292) (GuestAddrs.access_list_count + 100)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x21,
    .AUIPC .x13 (laHi GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 116)),
    .AUIPC .x14 (laHi GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 124)),
    .ADDI .x14 .x14 (laLo GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 124)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.access_list_count + 132)),
    .BNE .x10 .x0 (brOff (GuestAddrs.access_list_count + 304) (GuestAddrs.access_list_count + 136)),
    .AUIPC .x5 (laHi GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 140)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 140)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 152)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_entry_length (GuestAddrs.access_list_count + 152)),
    .LD .x7 .x5 (0 : BitVec 12),
    .ADD .x10 .x8 .x6,
    .MV .x11 .x7,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 176)),
    .ADDI .x13 .x13 (laLo GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 176)),
    .AUIPC .x14 (laHi GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 184)),
    .ADDI .x14 .x14 (laLo GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 184)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.access_list_count + 192)),
    .BNE .x10 .x0 (brOff (GuestAddrs.access_list_count + 304) (GuestAddrs.access_list_count + 196)),
    .AUIPC .x5 (laHi GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 200)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_entry_offset (GuestAddrs.access_list_count + 200)),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 212)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_keys_offset (GuestAddrs.access_list_count + 212)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x6 .x6 .x28,
    .ADD .x10 .x8 .x6,
    .AUIPC .x5 (laHi GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 232)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_keys_length (GuestAddrs.access_list_count + 232)),
    .LD .x11 .x5 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 244)),
    .ADDI .x12 .x12 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 244)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.access_list_count + 252)),
    .BNE .x10 .x0 (48 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.alc_scratch (GuestAddrs.access_list_count + 260)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x19 (0 : BitVec 12),
    .ADD .x7 .x7 .x6,
    .SD .x19 .x7 (0 : BitVec 12),
    .ADDI .x21 .x21 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.access_list_count + 100) (GuestAddrs.access_list_count + 288)),
    .SD .x18 .x20 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .SD .x18 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `accessListCount_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def accessListCount_relocs : RelocTable :=
  [ (16, .la .x12 "alc_scratch"),
    (18, .jal .x1 "rlp_list_count_items"),
    (20, .la .x5 "alc_scratch"),
    (29, .la .x13 "alc_entry_offset"),
    (31, .la .x14 "alc_entry_length"),
    (33, .jal .x1 "rlp_list_nth_item"),
    (35, .la .x5 "alc_entry_offset"),
    (38, .la .x5 "alc_entry_length"),
    (44, .la .x13 "alc_keys_offset"),
    (46, .la .x14 "alc_keys_length"),
    (48, .jal .x1 "rlp_list_nth_item"),
    (50, .la .x5 "alc_entry_offset"),
    (53, .la .x5 "alc_keys_offset"),
    (58, .la .x5 "alc_keys_length"),
    (61, .la .x12 "alc_scratch"),
    (63, .jal .x1 "rlp_list_count_items"),
    (65, .la .x5 "alc_scratch") ]

def accessListCountFunction : String :=
  "access_list_count:\n" ++ emitProgramR accessListCount_prog accessListCount_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `accessListCount_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem accessListCountFunction_eq_prog :
    accessListCountFunction = "access_list_count:\n" ++ emitProgramR accessListCount_prog accessListCount_relocs := rfl

#guard accessListCountFunction.startsWith "access_list_count:\n"
#guard accessListCount_prog.length = 88
end EvmAsm.Codegen
