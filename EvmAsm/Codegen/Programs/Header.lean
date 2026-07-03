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
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.HeaderFields

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
def checkGasLimitFunction : String :=
  "check_gas_limit:\n" ++
  "  li t0, 5000                 # GAS_LIMIT_MINIMUM\n" ++
  "  bltu a0, t0, .Lcgl_fail_min\n" ++
  "  # max_adjustment_delta = parent_gas_limit >> 10  (== /1024)\n" ++
  "  srli t1, a1, 10\n" ++
  "  # abs_diff = |new - parent|\n" ++
  "  bgtu a0, a1, .Lcgl_pos\n" ++
  "  sub t2, a1, a0\n" ++
  "  j .Lcgl_check\n" ++
  ".Lcgl_pos:\n" ++
  "  sub t2, a0, a1\n" ++
  ".Lcgl_check:\n" ++
  "  bgeu t2, t1, .Lcgl_fail_jump\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lcgl_fail_min:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lcgl_fail_jump:\n" ++
  "  li a0, 2\n" ++
  "  ret"

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
def amsterdamBlobGasPriceFunction : String :=
  "amsterdam_blob_gas_price:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd s0,  0(sp); sd s1,  8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp)\n" ++
  "  mv s0, a0                   # numerator = excess_blob_gas\n" ++
  "  li s1, 11684671             # Amsterdam BLOB_BASE_FEE_UPDATE_FRACTION\n" ++
  "  li s2, 1                    # i\n" ++
  "  li s3, 0                    # output accumulator\n" ++
  "  mv s4, s1                   # numerator_accumulated = denominator\n" ++
  ".Labgp_loop:\n" ++
  "  beqz s4, .Labgp_done\n" ++
  "  add t0, s3, s4              # output += numerator_accumulated\n" ++
  "  bltu t0, s3, .Labgp_overflow\n" ++
  "  mv s3, t0\n" ++
  "  mulhu t3, s4, s0            # hi half of accum * numerator (128-bit product)\n" ++
  "  mul t4, s4, s0             # lo half of accum * numerator\n" ++
  "  mulhu t0, s1, s2            # high half of denominator * i\n" ++
  "  bnez t0, .Labgp_overflow\n" ++
  "  mul t2, s1, s2              # deni = denominator * i\n" ++
  "  beqz t2, .Labgp_overflow\n" ++
  "  bgeu t3, t2, .Labgp_overflow # hi >= deni => quotient exceeds u64\n" ++
  "  mv t5, t3                   # rem = hi (hi < deni guaranteed)\n" ++
  "  li t6, 0                    # q = 0\n" ++
  "  li t1, 64                   # 64 division iterations\n" ++
  ".Labgp_div:\n" ++
  "  srli t0, t4, 63             # lobit = MSB of lo\n" ++
  "  srli t3, t5, 63             # topbit = carry-out of rem << 1\n" ++
  "  slli t5, t5, 1              # rem <<= 1\n" ++
  "  or t5, t5, t0               # rem |= lobit\n" ++
  "  slli t4, t4, 1              # consume next lo bit\n" ++
  "  slli t6, t6, 1              # q <<= 1\n" ++
  "  bnez t3, .Labgp_div_sub     # carry-out => true rem >= 2^64 > deni\n" ++
  "  bltu t5, t2, .Labgp_div_next\n" ++
  ".Labgp_div_sub:\n" ++
  "  sub t5, t5, t2              # rem -= deni (u64 wrap exact when topbit set)\n" ++
  "  ori t6, t6, 1               # q |= 1\n" ++
  ".Labgp_div_next:\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Labgp_div\n" ++
  "  mv s4, t6                   # next numerator_accumulated\n" ++
  "  addi t0, s2, 1\n" ++
  "  beqz t0, .Labgp_overflow\n" ++
  "  mv s2, t0\n" ++
  "  j .Labgp_loop\n" ++
  ".Labgp_done:\n" ++
  "  divu a1, s3, s1             # output // denominator\n" ++
  "  li a0, 0\n" ++
  "  j .Labgp_ret\n" ++
  ".Labgp_overflow:\n" ++
  "  li a0, 1\n" ++
  "  li a1, 0\n" ++
  ".Labgp_ret:\n" ++
  "  ld s0,  0(sp); ld s1,  8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

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
def amsterdamBlobGasPriceU256Function : String :=
  "amsterdam_blob_gas_price_u256:\n" ++
  "  addi sp, sp, -128\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # numerator = excess_blob_gas\n" ++
  "  mv s5, a1                   # caller output price ptr (u256 BE)\n" ++
  "  li s1, 11684671             # Amsterdam BLOB_BASE_FEE_UPDATE_FRACTION\n" ++
  "  li s2, 1                    # i\n" ++
  "  addi s3, sp, 64             # numerator_accumulated (u256 scratch)\n" ++
  "  addi s4, sp, 96             # output accumulator (u256 scratch)\n" ++
  "  mv a0, s1; mv a1, s3; jal ra, u256_from_u64_be   # accum = denominator\n" ++
  "  li a0, 0; mv a1, s4; jal ra, u256_from_u64_be    # output = 0\n" ++
  ".Labgpu_loop:\n" ++
  "  mv a0, s3; jal ra, u256_is_zero\n" ++
  "  bnez a0, .Labgpu_done\n" ++
  "  mv a0, s4; mv a1, s3; mv a2, s4; jal ra, u256_add_be   # output += accum\n" ++
  "  bnez a0, .Labgpu_overflow\n" ++
  "  mv a0, s3; mv a1, s0; mv a2, s3; jal ra, u256_mul_u64_be  # accum *= excess\n" ++
  "  bnez a0, .Labgpu_overflow\n" ++
  "  mulhu t0, s1, s2; bnez t0, .Labgpu_overflow         # deni = denom*i fits u64\n" ++
  "  mul t1, s1, s2\n" ++
  "  srli t0, t1, 56; bnez t0, .Labgpu_overflow          # and within div helper's 2^56\n" ++
  "  mv a0, s3; mv a1, t1; mv a2, s3; jal ra, u256_div_u64_be  # accum //= deni\n" ++
  "  addi s2, s2, 1\n" ++
  "  j .Labgpu_loop\n" ++
  ".Labgpu_done:\n" ++
  "  mv a0, s4; mv a1, s1; mv a2, s5; jal ra, u256_div_u64_be  # price = output//denom\n" ++
  "  li a0, 0\n" ++
  "  j .Labgpu_u256_ret\n" ++
  ".Labgpu_overflow:\n" ++
  "  li a0, 1\n" ++
  ".Labgpu_u256_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 128\n" ++
  "  ret"

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
def headerValidatePostMergeFunction : String :=
  "header_validate_post_merge:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # header ptr\n" ++
  "  mv s1, a1                   # header_len\n" ++
  "  # Check 1: field 1 (ommers_hash) == EMPTY_OMMERS_HASH.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhvpm_fail_oh\n" ++
  "  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, empty_ommers_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  # Check 2: field 7 (difficulty) is canonical-zero (len 0).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lhvpm_fail_diff\n" ++
  "  # Check 3: field 14 (nonce) is 8 zero bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 14\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bne t1, t2, .Lhvpm_fail_nonce\n" ++
  "  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5, 0(t3)\n" ++
  "  bnez t5, .Lhvpm_fail_nonce\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_oh:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_diff:\n" ++
  "  li a0, 2\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_nonce:\n" ++
  "  li a0, 3\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_parse:\n" ++
  "  li a0, 4\n" ++
  ".Lhvpm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

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
def headerValidateExtraDataLengthFunction : String :=
  "header_validate_extra_data_length:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  li a2, 12\n" ++
  "  la a3, hved_off\n" ++
  "  la a4, hved_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhved_parse_fail\n" ++
  "  la t0, hved_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lhved_too_long\n" ++
  "  li a0, 0\n" ++
  "  j .Lhved_ret\n" ++
  ".Lhved_too_long:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhved_ret\n" ++
  ".Lhved_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhved_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

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
def blockHashFromHeaderFunction : String :=
  "block_hash_from_header:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  # zkvm_keccak256(a0=header, a1=len, a2=out)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

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
