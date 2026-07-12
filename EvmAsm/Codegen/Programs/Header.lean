/-
  EvmAsm.Codegen.Programs.Header

  Block-header decoding and validation cluster lifted out of
  `EvmAsm.Codegen.Programs` per the file-size hard cap.

  Header decoders:
    K38  header_minimal_decode
    K39  header_extended_decode
    K55  coinbase_extract_from_header
    K90  header_extract_blob_gas_pair
    K93  block_validate_blob_gas_max_cap
    K95  header_extract_block_roots

  Header validators:
    K43  validate_header_basic
    K72  check_gas_limit
    K63  calc_excess_blob_gas
         amsterdam_blob_gas_price
    K67  header_validate_post_merge
    K68  header_validate_extra_data_length

  Pre- / post-exec account mutations (placed adjacently in the
  source file; they consume the header-validation pipeline's
  outputs for gas / base-fee fields):
    K81  account_charge_gas_pre_exec
    K82  account_refund_gas_post_exec

  Header fee-validation chain:
    K73  eip1559_calc_base_fee_per_gas
    K74  header_validate_base_fee
    K75  validate_header_full

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## header_extract_blob_gas_pair -- PR-K90 Cancun blob fields

    Extract the EIP-4844 blob-gas fields from an Amsterdam header:

      blob_gas_used    (header field 17, u64) — total blob gas
        consumed by all transactions in this block (= sum of
        `len(tx.blob_versioned_hashes) × GAS_PER_BLOB` over type-3
        txs). Cross-checks against PR-K89.

      excess_blob_gas  (header field 18, u64) — running total used
        for the blob-fee adjustment formula.

    Cancun-era (and later) headers always have both. Pre-Cancun
    headers don't, and the extractor reports a parse failure.

    Direct inputs to:
      * the apply_body invariant
        `header.blob_gas_used == sum(tx.blob_gas_used)`
      * the next-block `excess_blob_gas` recurrence used in
        `calculate_excess_blob_gas`.

    Output layout (16 bytes):
       0..  8  blob_gas_used    (u64 LE)
       8.. 16  excess_blob_gas  (u64 LE)

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 16-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : header parse failed / field 17 missing / not u64
        2 : field 18 missing / not u64

    Composes PR-K20 `rlp_list_nth_item` via PR-K53
    `rlp_field_to_u64`. Uses two 8-byte `.data` scratch slots
    (`rfu_offset`, `rfu_length`) shared with other K-helpers. -/
def headerExtractBlobGasPairFunction : String :=
  "header_extract_blob_gas_pair:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 16B ptr\n" ++
  "  # Field 17: blob_gas_used → out[0..8]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 17\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lhebgp_f18\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2)\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebgp_ret\n" ++
  ".Lhebgp_f18:\n" ++
  "  # Field 18: excess_blob_gas → out[8..16]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 18\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lhebgp_ok\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lhebgp_ret\n" ++
  ".Lhebgp_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lhebgp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_blob_gas_pair`: probe BuildUnit. Reads
    (header_len, header_bytes), writes (status, blob_gas_used,
    excess_blob_gas) to OUTPUT (24 bytes total). -/
def ziskHeaderExtractBlobGasPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 16B output at OUTPUT + 8\n" ++
  "  sd zero, 0(a2); sd zero, 8(a2)\n" ++
  "  jal ra, header_extract_blob_gas_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhebgp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBlobGasPairFunction ++ "\n" ++
  ".Lhebgp_pdone:"

def ziskHeaderExtractBlobGasPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBlobGasPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBlobGasPairPrologue
  dataAsm     := ziskHeaderExtractBlobGasPairDataSection
}

/-! ## block_validate_blob_gas_max_cap -- PR-K93

    Cancun cap enforcement: a block's `blob_gas_used` cannot exceed
    `MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX × GAS_PER_BLOB`.

    Python reference (`forks/amsterdam/fork.py`):

      MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX * GAS_PER_BLOB
      blob_gas_available = MAX_BLOB_GAS_PER_BLOCK - block_output.blob_gas_used
      # …enforced per-tx as `tx_blob_gas_used > blob_gas_available`

    The block-level cap is the loop invariant: at end-of-block,
    `block_output.blob_gas_used == header.blob_gas_used`, so the
    consensus check that `header.blob_gas_used ≤ MAX_BLOB_GAS_PER_BLOCK`
    is the closed form. On Amsterdam mainnet:

      MAX_BLOB_GAS_PER_BLOCK = 21 × 131072 = 2,752,512

    Both parameters are passed in so the helper works across
    forks that adjust either.

    Computation:
      1. Extract `header.blob_gas_used` (field 17, u64) via PR-K53
         `rlp_field_to_u64`.
      2. Compute `cap = max_blobs_per_block × gas_per_blob`; reject
         on u64 overflow.
      3. Compare `blob_gas_used ≤ cap`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : max_blobs_per_block (u64; 21 on mainnet Amsterdam)
      a3 (input)  : gas_per_blob (u64; 131072 on mainnet)
      ra (input)  : return
      a0 (output) : composite status

    Status encoding:
      0 : within cap
      1 : header parse / field 17 missing / not u64
      2 : `max_blobs_per_block × gas_per_blob` overflows u64
      3 : `blob_gas_used > cap`

    Composes PR-K20 `rlp_list_nth_item` via PR-K53
    `rlp_field_to_u64`. -/
def blockValidateBlobGasMaxCapFunction : String :=
  "block_validate_blob_gas_max_cap:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # max_blobs_per_block\n" ++
  "  mv s1, a3                   # gas_per_blob\n" ++
  "  # Step 1: extract header.blob_gas_used (field 17, u64).\n" ++
  "  # a0,a1 still hold (header_ptr, header_len).\n" ++
  "  li a2, 17\n" ++
  "  la a3, bvbmc_bgu\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lbvbmc_step2\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvbmc_ret\n" ++
  ".Lbvbmc_step2:\n" ++
  "  # Step 2: cap = max_blobs × gas_per_blob, with u64 overflow check.\n" ++
  "  mulhu t0, s0, s1            # high half of unsigned product\n" ++
  "  bnez t0, .Lbvbmc_overflow\n" ++
  "  mul s2, s0, s1              # cap (low 64 bits)\n" ++
  "  # Step 3: compare blob_gas_used <= cap.\n" ++
  "  la t0, bvbmc_bgu\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bgtu t1, s2, .Lbvbmc_exceeds\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvbmc_ret\n" ++
  ".Lbvbmc_overflow:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvbmc_ret\n" ++
  ".Lbvbmc_exceeds:\n" ++
  "  li a0, 3\n" ++
  ".Lbvbmc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_blob_gas_max_cap`: probe BuildUnit. Reads
    (header_len, max_blobs, gas_per_blob, header_bytes) from host
    input, writes 8-byte status to OUTPUT. -/
def ziskBlockValidateBlobGasMaxCapPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # header_len\n" ++
  "  ld a2, 16(a4)               # max_blobs_per_block\n" ++
  "  ld a3, 24(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 32             # header_ptr\n" ++
  "  jal ra, block_validate_blob_gas_max_cap\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvbmc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  blockValidateBlobGasMaxCapFunction ++ "\n" ++
  ".Lbvbmc_pdone:"

def ziskBlockValidateBlobGasMaxCapDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvbmc_bgu:\n" ++
  "  .zero 8"

def ziskBlockValidateBlobGasMaxCapProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlobGasMaxCapPrologue
  dataAsm     := ziskBlockValidateBlobGasMaxCapDataSection
}

/-! ## header_extract_block_roots -- PR-K95

    Extract the three remaining 32-byte root fields from an
    Amsterdam header that the existing extended-decode helpers
    don't cover:

       0..32   transactions_root  (field 4)
      32..64   receipt_root       (field 5)
      64..96   withdrawals_root   (field 16)

    Used by `validate_block_body` callers that cross-check the
    body's tx/receipt/withdrawal MPT roots against the consensus-
    layer commitment, and by the trie-rebuild path. The state_root
    (field 3) is already covered by PR-K39 `header_extended_decode`;
    `parent_hash` by PR-K17; `coinbase` by PR-K55.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : field 4 (transactions_root) missing / not 32 B
        2 : field 5 (receipt_root) missing / not 32 B
        3 : field 16 (withdrawals_root) missing / not 32 B
            (pre-Shanghai headers don't have this field)

    Composes PR-K20 `rlp_list_nth_item`. Uses two 8-byte `.data`
    scratch slots (`hebr_offset`, `hebr_length`). -/
def headerExtractBlockRootsFunction : String :=
  "header_extract_block_roots:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # 96B output ptr\n" ++
  "  # Field 4: transactions_root → out[0..32]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, hebr_offset; la a4, hebr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebr_f4_fail\n" ++
  "  la t0, hebr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhebr_f4_fail\n" ++
  "  la t0, hebr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # Field 5: receipt_root → out[32..64]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, hebr_offset; la a4, hebr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebr_f5_fail\n" ++
  "  la t0, hebr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhebr_f5_fail\n" ++
  "  la t0, hebr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t5, s2, 32\n" ++
  "  ld t4,  0(t3); sd t4,  0(t5)\n" ++
  "  ld t4,  8(t3); sd t4,  8(t5)\n" ++
  "  ld t4, 16(t3); sd t4, 16(t5)\n" ++
  "  ld t4, 24(t3); sd t4, 24(t5)\n" ++
  "  # Field 16: withdrawals_root → out[64..96]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, hebr_offset; la a4, hebr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebr_f16_fail\n" ++
  "  la t0, hebr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhebr_f16_fail\n" ++
  "  la t0, hebr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t5, s2, 64\n" ++
  "  ld t4,  0(t3); sd t4,  0(t5)\n" ++
  "  ld t4,  8(t3); sd t4,  8(t5)\n" ++
  "  ld t4, 16(t3); sd t4, 16(t5)\n" ++
  "  ld t4, 24(t3); sd t4, 24(t5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhebr_ret\n" ++
  ".Lhebr_f4_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebr_zero_ret\n" ++
  ".Lhebr_f5_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lhebr_zero_ret\n" ++
  ".Lhebr_f16_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lhebr_zero_ret:\n" ++
  "  # Zero the output on any failure.\n" ++
  "  mv t0, s2; li t1, 12\n" ++
  ".Lhebr_zero:\n" ++
  "  beqz t1, .Lhebr_ret\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1\n" ++
  "  j .Lhebr_zero\n" ++
  ".Lhebr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_block_roots`: probe BuildUnit. Reads
    (header_len, header_bytes), writes (status, 3 × 32-byte roots)
    to OUTPUT (104 bytes total). -/
def ziskHeaderExtractBlockRootsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 96B output at OUTPUT + 8\n" ++
  "  # Pre-zero 96 bytes (12 dwords).\n" ++
  "  mv t0, a2; li t1, 12\n" ++
  ".Lhebr_pzero:\n" ++
  "  beqz t1, .Lhebr_pzdone\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1\n" ++
  "  j .Lhebr_pzero\n" ++
  ".Lhebr_pzdone:\n" ++
  "  jal ra, header_extract_block_roots\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhebr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractBlockRootsFunction ++ "\n" ++
  ".Lhebr_pdone:"

def ziskHeaderExtractBlockRootsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hebr_offset:\n" ++
  "  .zero 8\n" ++
  "hebr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBlockRootsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBlockRootsPrologue
  dataAsm     := ziskHeaderExtractBlockRootsDataSection
}

/-! ## validate_header_basic -- PR-K43 per-header semantic checks

    Three u64 invariants from `validate_header` (Python:
    `forks/amsterdam/fork.py`):

      1. gas_used <= gas_limit
      2. number >= 1 and number == parent.number + 1
      3. timestamp > parent.timestamp

    Both inputs are 128-byte extended-header structs as produced
    by PR-K39 `header_extended_decode`. Only the u64 fields at
    offsets 64 (number), 72 (timestamp), 80 (gas_limit), 88
    (gas_used) are read; the hash fields (parent_hash,
    state_root) and base_fee_per_gas are ignored here -- those
    are checked elsewhere (PR-K18 `validate_chain` for the hash
    chain, future PR for the EIP-1559 base-fee formula).

    Calling convention:
      a0 (input)  : header_ptr (128-byte struct, this header)
      a1 (input)  : parent_ptr (128-byte struct, parent header)
      ra (input)  : return
      a0 (output) : 0 ok
                    1 gas_used > gas_limit
                    2 number < 1 or number != parent.number + 1
                    3 timestamp <= parent.timestamp

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def validateHeaderBasic_prog : Program :=
  [ .LD .x5 .x10 (88 : BitVec 12),
    .LD .x6 .x10 (80 : BitVec 12),
    .BLTU .x6 .x5 (44 : BitVec 13),
    .LD .x5 .x10 (64 : BitVec 12),
    .BEQ .x5 .x0 (44 : BitVec 13),
    .LD .x6 .x11 (64 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .BNE .x5 .x6 (32 : BitVec 13),
    .LD .x5 .x10 (72 : BitVec 12),
    .LD .x6 .x11 (72 : BitVec 12),
    .BGEU .x6 .x5 (28 : BitVec 13),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (3 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def validateHeaderBasicFunction : String :=
  "validate_header_basic:\n" ++ emitProgram validateHeaderBasic_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `validateHeaderBasic_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem validateHeaderBasicFunction_eq_prog :
    validateHeaderBasicFunction = "validate_header_basic:\n" ++ emitProgram validateHeaderBasic_prog := rfl

#guard validateHeaderBasicFunction.startsWith "validate_header_basic:\n"
#guard validateHeaderBasic_prog.length = 19
/-- `zisk_validate_header_basic`: probe BuildUnit. Reads two
    128-byte extended-header structs from host input (after an
    8-byte tag) and writes the 8-byte status to OUTPUT. -/
def ziskValidateHeaderBasicPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  # Input layout: [pad u64][header 128B][parent 128B]\n" ++
  "  addi a0, a3, 8              # header_ptr\n" ++
  "  addi a1, a3, 136            # parent_ptr (8 + 128)\n" ++
  "  jal ra, validate_header_basic\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvhb_pdone\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  ".Lvhb_pdone:"

def ziskValidateHeaderBasicDataSection : String :=
  ".section .data\n" ++
  "vhb_pad:\n" ++
  "  .zero 8"

def ziskValidateHeaderBasicProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderBasicPrologue
  dataAsm     := ziskValidateHeaderBasicDataSection
}

/-! ## check_gas_limit -- PR-K72 gas-limit continuity check

    Verify the per-header gas-limit elasticity rules per
    Ethereum's `check_gas_limit`:

      max_adjustment_delta = parent_gas_limit // 1024
      |gas_limit - parent_gas_limit| < max_adjustment_delta
      gas_limit >= GAS_LIMIT_MINIMUM (5000)

    Used by `validate_header` to ensure consecutive blocks
    smoothly adjust their gas-limit ceiling. Adoption is
    EIP-1985 + EIP-1559 elasticity.

    Pure u64 arithmetic (shift, sub, compare). No scratch
    memory, leaf-callable.

    Calling convention:
      a0 (input)  : new.gas_limit    (u64)
      a1 (input)  : parent.gas_limit (u64)
      ra (input)  : return
      a0 (output) :
        0  : all checks pass
        1  : new.gas_limit < GAS_LIMIT_MINIMUM (5000)
        2  : |new - parent| >= parent / 1024 (jumped too far) -/
def checkGasLimit_prog : Program :=
  [ .LUI .x5 (1 : BitVec 20),
    .ADDIW .x5 .x5 (904 : BitVec 12),
    .BLTU .x10 .x5 (36 : BitVec 13),
    .SRLI .x6 .x11 (10 : BitVec 6),
    .BLTU .x11 .x10 (12 : BitVec 13),
    .SUB .x7 .x11 .x10,
    .JAL .x0 (8 : BitVec 21),
    .SUB .x7 .x10 .x11,
    .BGEU .x7 .x6 (20 : BitVec 13),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (2 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def checkGasLimitFunction : String :=
  "check_gas_limit:\n" ++ emitProgram checkGasLimit_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `checkGasLimit_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem checkGasLimitFunction_eq_prog :
    checkGasLimitFunction = "check_gas_limit:\n" ++ emitProgram checkGasLimit_prog := rfl

#guard checkGasLimitFunction.startsWith "check_gas_limit:\n"
#guard checkGasLimit_prog.length = 15
/-- `zisk_check_gas_limit`: probe BuildUnit. Reads (new_limit,
    parent_limit) as 2 u64s from host input, writes 8-byte
    status to OUTPUT. -/
def ziskCheckGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # new.gas_limit\n" ++
  "  ld a1, 16(t0)               # parent.gas_limit\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lcgl_pdone\n" ++
  checkGasLimitFunction ++ "\n" ++
  ".Lcgl_pdone:"

def ziskCheckGasLimitDataSection : String :=
  ".section .data\n" ++
  "cgl_pad:\n" ++
  "  .zero 8"

def ziskCheckGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCheckGasLimitPrologue
  dataAsm     := ziskCheckGasLimitDataSection
}

/-! ## K69 tx_validate_against_block — moved to `Programs/Tx.lean` (file-size hard cap). -/

/-! ## calc_excess_blob_gas -- PR-K63 EIP-4844 excess blob gas formula

    Compute the next header's `excess_blob_gas` field from the
    parent header. Python (`forks/cancun/fork.py::
    calculate_excess_blob_gas`):

      def calculate_excess_blob_gas(parent_header):
          excess_blob_gas = (
              parent_header.excess_blob_gas
              + parent_header.blob_gas_used
          )
          if excess_blob_gas < TARGET_BLOB_GAS_PER_BLOCK:
              return 0
          return excess_blob_gas - TARGET_BLOB_GAS_PER_BLOCK

    Equivalent to: `max(0, parent.excess_blob_gas +
    parent.blob_gas_used - target)`.

    Used by `validate_header` to check that
    `header.excess_blob_gas == calc_excess_blob_gas(parent,
    target)`.

    The `target` is parameterized — Cancun uses 3 blobs × 131072
    bytes = 393216; Prague/Amsterdam may use a higher target via
    EIP-7691 (e.g. 6 blobs × 131072 = 786432). The function takes
    `target` as an explicit u64 input so it works across forks.

    ## Precondition

    `parent_excess + parent_blob_used` must not overflow u64. In
    practice both terms are small (each < 2^30 on mainnet), so
    overflow doesn't occur. The function does NOT check.

    Calling convention:
      a0 (input)  : parent.excess_blob_gas (u64)
      a1 (input)  : parent.blob_gas_used (u64)
      a2 (input)  : target_blob_gas_per_block (u64)
      ra (input)  : return
      a0 (output) : excess_blob_gas for this header (u64).

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def calcExcessBlobGas_prog : Program :=
  [ .ADD .x5 .x10 .x11,
    .BGEU .x5 .x12 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .SUB .x10 .x5 .x12,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def calcExcessBlobGasFunction : String :=
  "calc_excess_blob_gas:\n" ++ emitProgram calcExcessBlobGas_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `calcExcessBlobGas_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem calcExcessBlobGasFunction_eq_prog :
    calcExcessBlobGasFunction = "calc_excess_blob_gas:\n" ++ emitProgram calcExcessBlobGas_prog := rfl

#guard calcExcessBlobGasFunction.startsWith "calc_excess_blob_gas:\n"
#guard calcExcessBlobGas_prog.length = 6
/-- `zisk_calc_excess_blob_gas`: probe BuildUnit. Reads
    (parent_excess, parent_used, target) from host input, writes
    the u64 result to OUTPUT. -/
def ziskCalcExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # parent_excess_blob_gas\n" ++
  "  ld a1, 16(a3)               # parent_blob_gas_used\n" ++
  "  ld a2, 24(a3)               # target_blob_gas_per_block\n" ++
  "  jal ra, calc_excess_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebg_pdone\n" ++
  calcExcessBlobGasFunction ++ "\n" ++
  ".Lcebg_pdone:"

def ziskCalcExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  "cebg_pad:\n" ++
  "  .zero 8"

def ziskCalcExcessBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCalcExcessBlobGasPrologue
  dataAsm     := ziskCalcExcessBlobGasDataSection
}

/-! ## amsterdam_blob_gas_price -- Amsterdam blob fee fake exponential

    Compute the Amsterdam `calculate_blob_gas_price` helper:

      taylor_exponential(1, excess_blob_gas, 11684671)

    from `execution-specs/src/ethereum/forks/amsterdam/vm/gas.py`.
    The generic `taylor_exponential` helper in
    `execution-specs/src/ethereum/utils/numeric.py` uses an accumulator
    scaled by the denominator:

      i = 1
      output = 0
      numerator_accumulated = denominator
      while numerator_accumulated > 0:
          output += numerator_accumulated
          numerator_accumulated =
              (numerator_accumulated * excess_blob_gas) // (denominator * i)
          i += 1
      return output // denominator

    This RV64 implementation is an exact u64 implementation for the
    EEST-relevant range where every intermediate product and sum fits
    in u64. It returns status=1 rather than wrapping if the helper's
    u64 envelope is exceeded; callers that need arbitrary-precision
    blob prices should extend this helper to the u256 toolkit.

    Calling convention:
      a0 (input)  : excess_blob_gas (u64)
      ra (input)  : return
      a0 (output) : status, 0 ok / 1 u64 overflow
      a1 (output) : blob gas price (u64; 0 on overflow).

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def amsterdamBlobGasPrice_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x18 (16 : BitVec 12),
    .SD .x2 .x19 (24 : BitVec 12),
    .SD .x2 .x20 (32 : BitVec 12),
    .MV .x8 .x10,
    .LUI .x9 (2853 : BitVec 20),
    .ADDIW .x9 .x9 (-1217 : BitVec 12),
    .LI .x18 (1 : Word),
    .LI .x19 (0 : Word),
    .MV .x20 .x9,
    .BEQ .x20 .x0 (124 : BitVec 13),
    .ADD .x5 .x19 .x20,
    .BLTU .x5 .x19 (128 : BitVec 13),
    .MV .x19 .x5,
    .MULHU .x28 .x20 .x8,
    .MUL .x29 .x20 .x8,
    .MULHU .x5 .x9 .x18,
    .BNE .x5 .x0 (108 : BitVec 13),
    .MUL .x7 .x9 .x18,
    .BEQ .x7 .x0 (100 : BitVec 13),
    .BGEU .x28 .x7 (96 : BitVec 13),
    .MV .x30 .x28,
    .LI .x31 (0 : Word),
    .LI .x6 (64 : Word),
    .SRLI .x5 .x29 (63 : BitVec 6),
    .SRLI .x28 .x30 (63 : BitVec 6),
    .SLLI .x30 .x30 (1 : BitVec 6),
    .OR .x30 .x30 .x5,
    .SLLI .x29 .x29 (1 : BitVec 6),
    .SLLI .x31 .x31 (1 : BitVec 6),
    .BNE .x28 .x0 (8 : BitVec 13),
    .BLTU .x30 .x7 (12 : BitVec 13),
    .SUB .x30 .x30 .x7,
    .ORI .x31 .x31 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .BNE .x6 .x0 (-44 : BitVec 13),
    .MV .x20 .x31,
    .ADDI .x5 .x18 (1 : BitVec 12),
    .BEQ .x5 .x0 (24 : BitVec 13),
    .MV .x18 .x5,
    .JAL .x0 (-120 : BitVec 21),
    .DIVU .x11 .x19 .x9,
    .LI .x10 (0 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (1 : Word),
    .LI .x11 (0 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x18 .x2 (16 : BitVec 12),
    .LD .x19 .x2 (24 : BitVec 12),
    .LD .x20 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def amsterdamBlobGasPriceFunction : String :=
  "amsterdam_blob_gas_price:\n" ++ emitProgram amsterdamBlobGasPrice_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `amsterdamBlobGasPrice_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem amsterdamBlobGasPriceFunction_eq_prog :
    amsterdamBlobGasPriceFunction = "amsterdam_blob_gas_price:\n" ++ emitProgram amsterdamBlobGasPrice_prog := rfl

#guard amsterdamBlobGasPriceFunction.startsWith "amsterdam_blob_gas_price:\n"
#guard amsterdamBlobGasPrice_prog.length = 55
/-! ## amsterdam_blob_gas_price_u256 -- wide-result blob fee fake exponential

    Same `taylor_exponential(1, excess_blob_gas, 11684671)` as
    `amsterdam_blob_gas_price`, but accumulates in 256-bit precision and
    returns the price as a 32-byte big-endian u256. The u64 helper saturates
    to a `status=1` overflow once the (denominator-scaled) accumulator leaves
    the u64 envelope (around excess ≈ 328M), which is well below the EIP-4844
    consensus-reachable range: e.g. `excess_blob_gas = 564,002,816` yields a
    blob gas price ≈ e^48 ≈ 9.4e20 (~70 bits). The spec's `taylor_exponential`
    is arbitrary precision, so a u64-overflowing helper false-rejects valid
    headers in `header_validate_excess_blob_gas` (the EIP-7918 reserve-price
    comparison `BLOB_BASE_COST * base_fee > PER_BLOB * blob_gas_price`). This
    256-bit variant handles the full reachable range; it only reports overflow
    if the price itself would exceed 2^256 (unreachable for valid blocks).

    Calling convention:
      a0 (input)  : excess_blob_gas (u64)
      a1 (input)  : output price ptr (32 bytes, BE)
      ra (input)  : return
      a0 (output) : status, 0 ok / 1 u256 overflow (output left undefined).

    Uses 64 bytes of stack scratch for the two u256 accumulators plus the
    `u256_mul_u64_be` `.data` scratch (`u256m_acc`). Composes u256_from_u64_be,
    u256_is_zero, u256_add_be, u256_mul_u64_be, u256_div_u64_be. -/
def amsterdamBlobGasPriceU256_prog : Program :=
  [ .ADDI .x2 .x2 (-128 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x21 .x11,
    .LUI .x9 (2853 : BitVec 20),
    .ADDIW .x9 .x9 (-1217 : BitVec 12),
    .LI .x18 (1 : Word),
    .ADDI .x19 .x2 (64 : BitVec 12),
    .ADDI .x20 .x2 (96 : BitVec 12),
    .MV .x10 .x9,
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_from_u64_be (GuestAddrs.amsterdam_blob_gas_price_u256 + 68)),
    .LI .x10 (0 : Word),
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.u256_from_u64_be (GuestAddrs.amsterdam_blob_gas_price_u256 + 80)),
    .MV .x10 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_is_zero (GuestAddrs.amsterdam_blob_gas_price_u256 + 88)),
    .BNE .x10 .x0 (88 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x19,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.amsterdam_blob_gas_price_u256 + 108)),
    .BNE .x10 .x0 (92 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x8,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_mul_u64_be (GuestAddrs.amsterdam_blob_gas_price_u256 + 128)),
    .BNE .x10 .x0 (72 : BitVec 13),
    .MULHU .x5 .x9 .x18,
    .BNE .x5 .x0 (64 : BitVec 13),
    .MUL .x6 .x9 .x18,
    .SRLI .x5 .x6 (56 : BitVec 6),
    .BNE .x5 .x0 (52 : BitVec 13),
    .MV .x10 .x19,
    .MV .x11 .x6,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_div_u64_be (GuestAddrs.amsterdam_blob_gas_price_u256 + 168)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .JAL .x0 (-92 : BitVec 21),
    .MV .x10 .x20,
    .MV .x11 .x9,
    .MV .x12 .x21,
    .JAL .x1 (jalOff GuestAddrs.u256_div_u64_be (GuestAddrs.amsterdam_blob_gas_price_u256 + 192)),
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
    .ADDI .x2 .x2 (128 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `amsterdamBlobGasPriceU256_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def amsterdamBlobGasPriceU256_relocs : RelocTable :=
  [ (17, .jal .x1 "u256_from_u64_be"),
    (20, .jal .x1 "u256_from_u64_be"),
    (22, .jal .x1 "u256_is_zero"),
    (27, .jal .x1 "u256_add_be"),
    (32, .jal .x1 "u256_mul_u64_be"),
    (42, .jal .x1 "u256_div_u64_be"),
    (48, .jal .x1 "u256_div_u64_be") ]

def amsterdamBlobGasPriceU256Function : String :=
  "amsterdam_blob_gas_price_u256:\n" ++ emitProgramR amsterdamBlobGasPriceU256_prog amsterdamBlobGasPriceU256_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `amsterdamBlobGasPriceU256_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem amsterdamBlobGasPriceU256Function_eq_prog :
    amsterdamBlobGasPriceU256Function = "amsterdam_blob_gas_price_u256:\n" ++ emitProgramR amsterdamBlobGasPriceU256_prog amsterdamBlobGasPriceU256_relocs := rfl

#guard amsterdamBlobGasPriceU256Function.startsWith "amsterdam_blob_gas_price_u256:\n"
#guard amsterdamBlobGasPriceU256_prog.length = 61
/-- `zisk_amsterdam_blob_gas_price`: probe BuildUnit. Reads
    `excess_blob_gas` from host input, writes `(status, price)` to
    OUTPUT. -/
def ziskAmsterdamBlobGasPricePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  ld a0, 8(a2)                # excess_blob_gas\n" ++
  "  jal ra, amsterdam_blob_gas_price\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  sd a1, 8(t0)                # blob gas price\n" ++
  "  j .Labgp_pdone\n" ++
  amsterdamBlobGasPriceFunction ++ "\n" ++
  ".Labgp_pdone:"

def ziskAmsterdamBlobGasPriceDataSection : String :=
  ".section .data\n" ++
  "abgp_pad:\n" ++
  "  .zero 8"

def ziskAmsterdamBlobGasPriceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAmsterdamBlobGasPricePrologue
  dataAsm     := ziskAmsterdamBlobGasPriceDataSection
}

/-! ## header_validate_post_merge -- PR-K67

    Verify the three post-merge header invariants:

      1. header.ommers_hash == EMPTY_OMMERS_HASH
         (= keccak256(rlp([])) = 0x1dcc4de8...49347)
      2. header.difficulty == 0   (canonical RLP: empty-string,
                                   content_length == 0)
      3. header.nonce == 0x0000000000000000   (8 zero bytes)

    Mirrors the Python `validate_header` checks added at the
    Merge fork:

      assert header.ommers_hash == EMPTY_OMMERS_HASH
      assert header.difficulty == 0
      assert header.nonce == b"\\x00" * 8

    Composes PR-K20 `rlp_list_nth_item` for field extraction.
    Each check has a distinct return code so callers can pinpoint
    which invariant failed.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0  : all three invariants hold
        1  : ommers_hash mismatch
        2  : difficulty != 0
        3  : nonce not 8 zero bytes
        4  : RLP parse failure (e.g. not a list, field missing)

    Uses 40 bytes of `.data` scratch (`hvpm_off`, `hvpm_len`
    + 32-byte `empty_ommers_hash` constant). -/
def headerValidatePostMerge_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (1 : Word),
    .AUIPC .x13 (laHi GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 36)),
    .ADDI .x13 .x13 (laLo GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 36)),
    .AUIPC .x14 (laHi GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 44)),
    .ADDI .x14 .x14 (laLo GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 44)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.header_validate_post_merge + 52)),
    .BNE .x10 .x0 (260 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 60)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BNE .x6 .x7 (216 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 80)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .AUIPC .x29 (laHi GuestAddrs.empty_ommers_hash (GuestAddrs.header_validate_post_merge + 96)),
    .ADDI .x29 .x29 (laLo GuestAddrs.empty_ommers_hash (GuestAddrs.header_validate_post_merge + 96)),
    .LD .x30 .x28 (0 : BitVec 12),
    .LD .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (180 : BitVec 13),
    .LD .x30 .x28 (8 : BitVec 12),
    .LD .x31 .x29 (8 : BitVec 12),
    .BNE .x30 .x31 (168 : BitVec 13),
    .LD .x30 .x28 (16 : BitVec 12),
    .LD .x31 .x29 (16 : BitVec 12),
    .BNE .x30 .x31 (156 : BitVec 13),
    .LD .x30 .x28 (24 : BitVec 12),
    .LD .x31 .x29 (24 : BitVec 12),
    .BNE .x30 .x31 (144 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (7 : Word),
    .AUIPC .x13 (laHi GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 164)),
    .ADDI .x13 .x13 (laLo GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 164)),
    .AUIPC .x14 (laHi GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 172)),
    .ADDI .x14 .x14 (laLo GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 172)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.header_validate_post_merge + 180)),
    .BNE .x10 .x0 (132 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 188)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 188)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (100 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (14 : Word),
    .AUIPC .x13 (laHi GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 216)),
    .ADDI .x13 .x13 (laLo GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 216)),
    .AUIPC .x14 (laHi GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 224)),
    .ADDI .x14 .x14 (laLo GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 224)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.header_validate_post_merge + 232)),
    .BNE .x10 .x0 (80 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hvpm_len (GuestAddrs.header_validate_post_merge + 240)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (8 : Word),
    .BNE .x6 .x7 (52 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 260)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hvpm_off (GuestAddrs.header_validate_post_merge + 260)),
    .LD .x28 .x5 (0 : BitVec 12),
    .ADD .x28 .x8 .x28,
    .LD .x30 .x28 (0 : BitVec 12),
    .BNE .x30 .x0 (28 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (3 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (4 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerValidatePostMerge_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerValidatePostMerge_relocs : RelocTable :=
  [ (9, .la .x13 "hvpm_off"),
    (11, .la .x14 "hvpm_len"),
    (13, .jal .x1 "rlp_list_nth_item"),
    (15, .la .x5 "hvpm_len"),
    (20, .la .x5 "hvpm_off"),
    (24, .la .x29 "empty_ommers_hash"),
    (41, .la .x13 "hvpm_off"),
    (43, .la .x14 "hvpm_len"),
    (45, .jal .x1 "rlp_list_nth_item"),
    (47, .la .x5 "hvpm_len"),
    (54, .la .x13 "hvpm_off"),
    (56, .la .x14 "hvpm_len"),
    (58, .jal .x1 "rlp_list_nth_item"),
    (60, .la .x5 "hvpm_len"),
    (65, .la .x5 "hvpm_off") ]

def headerValidatePostMergeFunction : String :=
  "header_validate_post_merge:\n" ++ emitProgramR headerValidatePostMerge_prog headerValidatePostMerge_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerValidatePostMerge_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerValidatePostMergeFunction_eq_prog :
    headerValidatePostMergeFunction = "header_validate_post_merge:\n" ++ emitProgramR headerValidatePostMerge_prog headerValidatePostMerge_relocs := rfl

#guard headerValidatePostMergeFunction.startsWith "header_validate_post_merge:\n"
#guard headerValidatePostMerge_prog.length = 85
/-- `zisk_header_validate_post_merge`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes 8-byte
    status to OUTPUT. -/
def ziskHeaderValidatePostMergePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhvpm_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  ".Lhvpm_pdone:"

def ziskHeaderValidatePostMergeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8"

def ziskHeaderValidatePostMergeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidatePostMergePrologue
  dataAsm     := ziskHeaderValidatePostMergeDataSection
}


/-! ## header_validate_extra_data_length -- PR-K68

    Verify the Ethereum spec constraint that `header.extra_data`
    is at most 32 bytes (Yellow Paper §4.4.4).

    Mirrors the Python check in `validate_header`:

      assert len(header.extra_data) <= 32

    Composes PR-K20 `rlp_list_nth_item` to extract field 12
    (extra_data) and a single u64 compare.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0  : extra_data length ≤ 32 bytes
        1  : extra_data length > 32 bytes (reject)
        2  : RLP parse failure (e.g. not a list, field missing)

    Uses two 8-byte `.data` scratch slots (`hved_off`,
    `hved_len`). -/
def headerValidateExtraDataLength_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .LI .x12 (12 : Word),
    .AUIPC .x13 (laHi GuestAddrs.hved_off (GuestAddrs.header_validate_extra_data_length + 12)),
    .ADDI .x13 .x13 (laLo GuestAddrs.hved_off (GuestAddrs.header_validate_extra_data_length + 12)),
    .AUIPC .x14 (laHi GuestAddrs.hved_len (GuestAddrs.header_validate_extra_data_length + 20)),
    .ADDI .x14 .x14 (laLo GuestAddrs.hved_len (GuestAddrs.header_validate_extra_data_length + 20)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.header_validate_extra_data_length + 28)),
    .BNE .x10 .x0 (40 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.hved_len (GuestAddrs.header_validate_extra_data_length + 36)),
    .ADDI .x5 .x5 (laLo GuestAddrs.hved_len (GuestAddrs.header_validate_extra_data_length + 36)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (32 : Word),
    .BLTU .x7 .x6 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `headerValidateExtraDataLength_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def headerValidateExtraDataLength_relocs : RelocTable :=
  [ (3, .la .x13 "hved_off"),
    (5, .la .x14 "hved_len"),
    (7, .jal .x1 "rlp_list_nth_item"),
    (9, .la .x5 "hved_len") ]

def headerValidateExtraDataLengthFunction : String :=
  "header_validate_extra_data_length:\n" ++ emitProgramR headerValidateExtraDataLength_prog headerValidateExtraDataLength_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `headerValidateExtraDataLength_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem headerValidateExtraDataLengthFunction_eq_prog :
    headerValidateExtraDataLengthFunction = "header_validate_extra_data_length:\n" ++ emitProgramR headerValidateExtraDataLength_prog headerValidateExtraDataLength_relocs := rfl

#guard headerValidateExtraDataLengthFunction.startsWith "header_validate_extra_data_length:\n"
#guard headerValidateExtraDataLength_prog.length = 22
/-- `zisk_header_validate_extra_data_length`: probe BuildUnit.
    Reads (header_len, header_bytes), writes 8-byte status. -/
def ziskHeaderValidateExtraDataLengthPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  jal ra, header_validate_extra_data_length\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhved_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  ".Lhved_pdone:"

def ziskHeaderValidateExtraDataLengthDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hved_off:\n" ++
  "  .zero 8\n" ++
  "hved_len:\n" ++
  "  .zero 8"

def ziskHeaderValidateExtraDataLengthProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateExtraDataLengthPrologue
  dataAsm     := ziskHeaderValidateExtraDataLengthDataSection
}


/-! ## u256-BE arithmetic / comparison / pricing helpers (PR-K51/K52/K56/K58/K59/K60/K61/K62/K70/K53/K54)
    Function + probe defs moved to `Programs/Tx.lean` (see file-size hard cap at the bottom of this file). -/


/-! ## block_hash_from_header -- PR-K172

    Compute the block hash of an Ethereum block header:
    `block_hash = keccak256(header_rlp_bytes)`.

    The header RLP is the canonical wire encoding of the
    15-or-16-field header list (parent_hash, ommers_hash,
    beneficiary, state_root, transactions_root, receipts_root,
    logs_bloom, difficulty, number, gas_limit, gas_used,
    timestamp, extra_data, prev_randao, nonce, [base_fee, ...
    withdrawals_root, blob_gas_used, excess_blob_gas,
    parent_beacon_block_root]).

    The block hash is identified by `parent_hash` in the next
    header in the chain, so this primitive is the natural
    building block for `validate_headers` (which walks the
    chain and checks each `header[i].parent_hash ==
    block_hash_from_header(header[i-1])`).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr (block_hash lands here)
      ra (input)  : return
      (no output register; result is in memory at `a2`) -/
def blockHashFromHeader_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_hash_from_header + 8)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blockHashFromHeader_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blockHashFromHeader_relocs : RelocTable :=
  [ (2, .jal .x1 "zkvm_keccak256") ]

def blockHashFromHeaderFunction : String :=
  "block_hash_from_header:\n" ++ emitProgramR blockHashFromHeader_prog blockHashFromHeader_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blockHashFromHeader_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem blockHashFromHeaderFunction_eq_prog :
    blockHashFromHeaderFunction = "block_hash_from_header:\n" ++ emitProgramR blockHashFromHeader_prog blockHashFromHeader_relocs := rfl

#guard blockHashFromHeaderFunction.startsWith "block_hash_from_header:\n"
#guard blockHashFromHeader_prog.length = 6
/-- `zisk_block_hash_from_header`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp byte length
      bytes 8..   : header_rlp
    Output layout:
      bytes 0..32 : block_hash -/
def ziskBlockHashFromHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output block_hash ptr (32 B)\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  j .Lbhfh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  ".Lbhfh_pdone:"

def ziskBlockHashFromHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskBlockHashFromHeaderProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashFromHeaderPrologue
  dataAsm     := ziskBlockHashFromHeaderDataSection
}

/-! ## K201..K208 single-field extractors -- moved to Programs/HeaderFields.lean (file-size hard cap). -/

/-! ## header_extract_timestamp -- PR-K232

    Extract `timestamp` (field 11, u64 BE) from a header RLP.
    Cross-fork — every header has timestamp.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : field 11 exceeds 8 bytes BE -/
def headerExtractTimestampFunction : String :=
  "header_extract_timestamp:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 11\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractTimestampPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_timestamp\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhets_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractTimestampFunction ++ "\n" ++
  ".Lhets_pdone:"

def ziskHeaderExtractTimestampDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractTimestampProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractTimestampPrologue
  dataAsm     := ziskHeaderExtractTimestampDataSection
}

end EvmAsm.Codegen
