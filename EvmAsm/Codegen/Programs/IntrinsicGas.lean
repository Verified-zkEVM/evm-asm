/-
  EvmAsm.Codegen.Programs.IntrinsicGas

  Intrinsic-gas helpers carved out of `EvmAsm.Codegen.Programs`
  per the file-size hard cap. Hosts:

    K105  calldata_byte_counts
    K106  intrinsic_gas_calldata_floor_eip7623
    K107  init_code_cost

  Pure arithmetic — no RLP/MPT/Keccak dependencies. Self-contained:
  imports only `Rv64.Program` and `Codegen.Layout`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## calldata_byte_counts -- PR-K105

    Count zero and non-zero bytes in an arbitrary byte buffer.
    Used by intrinsic-gas pricing across all post-Istanbul forks:

      EIP-2028 standard pricing:
        data_cost = zero_count × 4  +  non_zero_count × 16
      EIP-7623 calldata-floor pricing (Pectra+):
        floor_cost = zero_count × 10  +  non_zero_count × 40

    A pure-leaf helper: no callee-saved registers used (apart from
    saving s0..s1 so the loop is human-readable), no scratch
    memory, no transitive calls. Returns both counts in one pass.

    Calling convention:
      a0 (input)  : bytes ptr
      a1 (input)  : byte length
      a2 (input)  : u64 out ptr (zero_count)
      a3 (input)  : u64 out ptr (non_zero_count)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total over the buffer).

    `zero_count + non_zero_count == byte_length` exactly. -/
def calldataByteCountsFunction : String :=
  "calldata_byte_counts:\n" ++
  "  # Pure-leaf, but we read into t-regs and update in-place; no\n" ++
  "  # callee-saved usage needed.\n" ++
  "  li t0, 0                    # zero_count\n" ++
  "  li t1, 0                    # non_zero_count\n" ++
  "  mv t2, a0                   # cursor\n" ++
  "  mv t3, a1                   # remaining bytes\n" ++
  ".Lcbc_loop:\n" ++
  "  beqz t3, .Lcbc_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bnez t4, .Lcbc_nz\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lcbc_step\n" ++
  ".Lcbc_nz:\n" ++
  "  addi t1, t1, 1\n" ++
  ".Lcbc_step:\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcbc_loop\n" ++
  ".Lcbc_done:\n" ++
  "  sd t0, 0(a2)\n" ++
  "  sd t1, 0(a3)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_calldata_byte_counts`: probe BuildUnit. Reads
    (length, bytes) from host input, writes (status,
    zero_count, non_zero_count) to OUTPUT (24 bytes total). -/
def ziskCalldataByteCountsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # byte length\n" ++
  "  addi a0, a4, 16             # bytes ptr\n" ++
  "  li a2, 0xa0010008           # zero_count out\n" ++
  "  li a3, 0xa0010010           # non_zero_count out\n" ++
  "  jal ra, calldata_byte_counts\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcbc_pdone\n" ++
  calldataByteCountsFunction ++ "\n" ++
  ".Lcbc_pdone:"

def ziskCalldataByteCountsDataSection : String :=
  ".section .data\n" ++
  "cbc_scratch:\n" ++
  "  .zero 8"

def ziskCalldataByteCountsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCalldataByteCountsPrologue
  dataAsm     := ziskCalldataByteCountsDataSection
}

/-! ## intrinsic_gas_calldata_floor_eip7623 -- PR-K106

    Compute the EIP-7623 calldata-floor gas cost for a tx, in
    closed form:

      tokens     = zero_count + 4 × non_zero_count
      floor_cost = tokens × GAS_TX_DATA_TOKEN_FLOOR  +  GAS_TX_BASE
                 = tokens × 10                       +  21000

    This is the lower bound on a tx's overall gas charge per
    EIP-7623; the actual charged amount is
    `max(intrinsic + execution, floor)`. PR-K46 covers the
    standard intrinsic-gas computation; K106 covers the floor
    side so callers can take the `max` cheaply.

    The Amsterdam constants are passed as arguments so the helper
    works across forks that re-cost the floor.

    Calling convention:
      a0 (input)  : data ptr
      a1 (input)  : data byte length
      a2 (input)  : floor_gas_per_token (10 on Amsterdam mainnet)
      a3 (input)  : token_per_nonzero (4 on Amsterdam mainnet)
      a4 (input)  : base_gas (21000 on mainnet)
      a5 (input)  : u64 out ptr (floor_cost)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls. -/
def intrinsicGasCalldataFloorEip7623Function : String :=
  "intrinsic_gas_calldata_floor_eip7623:\n" ++
  "  # Count zeros and non-zeros in one pass.\n" ++
  "  li t0, 0                    # zero_count\n" ++
  "  li t1, 0                    # non_zero_count\n" ++
  "  mv t2, a0                   # cursor\n" ++
  "  mv t3, a1                   # remaining\n" ++
  ".Ligcf_loop:\n" ++
  "  beqz t3, .Ligcf_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bnez t4, .Ligcf_nz\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Ligcf_step\n" ++
  ".Ligcf_nz:\n" ++
  "  addi t1, t1, 1\n" ++
  ".Ligcf_step:\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Ligcf_loop\n" ++
  ".Ligcf_done:\n" ++
  "  # tokens = zero + non_zero × token_per_nonzero\n" ++
  "  mul t5, t1, a3              # non_zero × token_per_nz\n" ++
  "  add t5, t5, t0              # tokens\n" ++
  "  # floor = tokens × floor_gas_per_token + base_gas\n" ++
  "  mul t6, t5, a2\n" ++
  "  add t6, t6, a4\n" ++
  "  sd t6, 0(a5)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_intrinsic_gas_calldata_floor_eip7623`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : data length
      bytes  8..16 : floor_gas_per_token
      bytes 16..24 : token_per_nonzero
      bytes 24..32 : base_gas
      bytes 32..   : data bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : floor_cost (u64 LE) -/
def ziskIntrinsicGasCalldataFloorEip7623Prologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # data length\n" ++
  "  ld a2, 16(a6)               # floor_gas_per_token\n" ++
  "  ld a3, 24(a6)               # token_per_nonzero\n" ++
  "  ld a4, 32(a6)               # base_gas\n" ++
  "  addi a0, a6, 40             # data ptr\n" ++
  "  li a5, 0xa0010008           # floor_cost out\n" ++
  "  jal ra, intrinsic_gas_calldata_floor_eip7623\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ligcf_pdone\n" ++
  intrinsicGasCalldataFloorEip7623Function ++ "\n" ++
  ".Ligcf_pdone:"

def ziskIntrinsicGasCalldataFloorEip7623DataSection : String :=
  ".section .data\n" ++
  "igcf_scratch:\n" ++
  "  .zero 8"

def ziskIntrinsicGasCalldataFloorEip7623ProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskIntrinsicGasCalldataFloorEip7623Prologue
  dataAsm     := ziskIntrinsicGasCalldataFloorEip7623DataSection
}

/-! ## init_code_cost -- PR-K107

    Compute the EIP-3860 init-code gas cost for a contract-creation
    tx's init bytecode:

      init_code_cost = GAS_CODE_INIT_PER_WORD × ceil(len / 32)
                     = 2 × ((len + 31) ÷ 32)        (mainnet)

    Used inside `calculate_intrinsic_cost(tx)` whenever
    `tx.to == empty` (CREATE-shaped tx); pre-EIP-3860 forks
    skip this term.

    The `gas_per_word` constant is passed in so the helper works
    across forks that adjust it.

    Calling convention:
      a0 (input)  : init_code_length (u64)
      a1 (input)  : gas_per_word (u64; 2 on mainnet)
      a2 (input)  : u64 out ptr (init_code_cost)
      ra (input)  : return
      a0 (output) : 0 (always succeeds — total function).

    Pure-leaf semantics: no scratch memory, no transitive calls.
    The arithmetic stays in u64; for any `init_code_length` within
    the EIP-3860 cap (`MAX_INIT_CODE_SIZE = 49_152`) and any
    `gas_per_word ≤ 2^48`, the cost fits in u64. -/
def initCodeCostFunction : String :=
  "init_code_cost:\n" ++
  "  addi t0, a0, 31             # len + 31\n" ++
  "  srli t0, t0, 5              # / 32 → ceil(len/32)\n" ++
  "  mul t0, t0, a1              # × gas_per_word\n" ++
  "  sd t0, 0(a2)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_init_code_cost`: probe BuildUnit. Reads
    (init_code_length, gas_per_word) from host input, writes
    (status, init_code_cost) to OUTPUT (16 bytes total).
    Input layout:
      bytes  0.. 8 : init_code_length
      bytes  8..16 : gas_per_word -/
def ziskInitCodeCostPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # init_code_length\n" ++
  "  ld a1, 16(a3)               # gas_per_word\n" ++
  "  li a2, 0xa0010008           # cost out\n" ++
  "  jal ra, init_code_cost\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Licc_pdone\n" ++
  initCodeCostFunction ++ "\n" ++
  ".Licc_pdone:"

def ziskInitCodeCostDataSection : String :=
  ".section .data\n" ++
  "icc_scratch:\n" ++
  "  .zero 8"

def ziskInitCodeCostProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskInitCodeCostPrologue
  dataAsm     := ziskInitCodeCostDataSection
}

/-! ## intrinsic_gas_amsterdam_counts -- EEST transaction intrinsic gas

    Compute Amsterdam `calculate_intrinsic_cost(tx)` over already-decoded
    transaction shape:

      calldata_tokens = zero_data_bytes + 4 * non_zero_data_bytes
      access_tokens   = 80 * access_list_address_count
                      + 128 * access_list_storage_key_count
      intrinsic       = 21000
                      + 4 * calldata_tokens
                      + creation ? (9000 + 2 * ceil(data_len / 32)) : 0
                      + 2400 * access_list_address_count
                      + 1900 * access_list_storage_key_count
                      + 16 * access_tokens
                      + 7500 * authorization_count
      floor           = 21000 + 16 * (4 * data_len + access_tokens)

    This intentionally returns the regular intrinsic component and calldata
    floor. Amsterdam's EIP-8037 state-gas component is handled by the caller's
    reservoir path. -/
def intrinsicGasAmsterdamCountsFunction : String :=
  "intrinsic_gas_amsterdam_counts:\n" ++
  "  # a0=data ptr, a1=data len, a2=is_creation, a3=access addrs,\n" ++
  "  # a4=access slots, a5=authorization count, a6=intrinsic out, a7=floor out\n" ++
  "  li t0, 0                    # zero_count\n" ++
  "  li t1, 0                    # non_zero_count\n" ++
  "  mv t2, a0                   # cursor\n" ++
  "  mv t3, a1                   # remaining\n" ++
  ".Ligac_loop:\n" ++
  "  beqz t3, .Ligac_count_done\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bnez t4, .Ligac_nz\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Ligac_step\n" ++
  ".Ligac_nz:\n" ++
  "  addi t1, t1, 1\n" ++
  ".Ligac_step:\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Ligac_loop\n" ++
  ".Ligac_count_done:\n" ++
  "  slli t5, t1, 2              # non_zero_count * 4\n" ++
  "  add t5, t5, t0              # tokens\n" ++
  "  slli t6, t5, 2              # data cost = tokens * 4\n" ++
  "  li t4, 21000\n" ++
  "  add t6, t6, t4              # intrinsic = base + data\n" ++
  "  beqz a2, .Ligac_after_creation\n" ++
  "  li t4, 9000\n" ++
  "  add t6, t6, t4\n" ++
  "  addi t4, a1, 31\n" ++
  "  srli t4, t4, 5\n" ++
  "  slli t4, t4, 1              # init code cost = 2 * ceil(len / 32)\n" ++
  "  add t6, t6, t4\n" ++
  ".Ligac_after_creation:\n" ++
  "  li t4, 2400\n" ++
  "  mul t4, a3, t4\n" ++
  "  add t6, t6, t4\n" ++
  "  li t4, 1900\n" ++
  "  mul t4, a4, t4\n" ++
  "  add t6, t6, t4\n" ++
  "  li t4, 80\n" ++
  "  mul t2, a3, t4             # access-list floor tokens: addresses\n" ++
  "  li t4, 128\n" ++
  "  mul t4, a4, t4             # access-list floor tokens: storage keys\n" ++
  "  add t2, t2, t4             # access_tokens\n" ++
  "  slli t4, t2, 4             # access-list floor gas = access_tokens * 16\n" ++
  "  add t6, t6, t4\n" ++
  "  li t4, 7500\n" ++
  "  mul t4, a5, t4\n" ++
  "  add t6, t6, t4\n" ++
  "  sd t6, 0(a6)\n" ++
  "  slli t5, a1, 2             # floor calldata tokens = 4 * data_len\n" ++
  "  add t5, t5, t2             # total floor tokens\n" ++
  "  slli t5, t5, 4             # calldata floor gas = total tokens * 16\n" ++
  "  li t4, 21000\n" ++
  "  add t5, t5, t4\n" ++
  "  sd t5, 0(a7)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- `zisk_intrinsic_gas_amsterdam_counts`: focused probe.
    Input layout:
      bytes  0.. 8 : data length
      bytes  8..16 : is_creation
      bytes 16..24 : tx gas limit
      bytes 24..32 : access-list address count
      bytes 32..40 : access-list storage-key count
      bytes 40..48 : authorization count
      bytes 48..   : data bytes
    Output layout:
      bytes  0.. 8 : status, 0 iff max(intrinsic, floor) <= gas_limit
      bytes  8..16 : intrinsic gas
      bytes 16..24 : calldata floor gas -/
def ziskIntrinsicGasAmsterdamCountsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # data length\n" ++
  "  ld a2, 16(t0)               # is_creation\n" ++
  "  ld s0, 24(t0)               # gas_limit, kept across helper call\n" ++
  "  ld a3, 32(t0)               # access-list address count\n" ++
  "  ld a4, 40(t0)               # access-list storage-key count\n" ++
  "  ld a5, 48(t0)               # authorization count\n" ++
  "  addi a0, t0, 56             # data ptr\n" ++
  "  li a6, 0xa0010008           # intrinsic out\n" ++
  "  li a7, 0xa0010010           # floor out\n" ++
  "  jal ra, intrinsic_gas_amsterdam_counts\n" ++
  "  li t0, 0xa0010008\n" ++
  "  ld t2, 0(t0)                # intrinsic\n" ++
  "  li t0, 0xa0010010\n" ++
  "  ld t3, 0(t0)                # floor\n" ++
  "  bgeu t2, t3, .Ligac_have_required\n" ++
  "  mv t2, t3\n" ++
  ".Ligac_have_required:\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t3, 1\n" ++
  "  bltu s0, t2, .Ligac_write_status\n" ++
  "  li t3, 0\n" ++
  ".Ligac_write_status:\n" ++
  "  sd t3, 0(t0)\n" ++
  "  j .Ligac_pdone\n" ++
  intrinsicGasAmsterdamCountsFunction ++ "\n" ++
  ".Ligac_pdone:"

def ziskIntrinsicGasAmsterdamCountsDataSection : String :=
  ".section .data\n" ++
  "igac_scratch:\n" ++
  "  .zero 8"

def ziskIntrinsicGasAmsterdamCountsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskIntrinsicGasAmsterdamCountsPrologue
  dataAsm     := ziskIntrinsicGasAmsterdamCountsDataSection
}


end EvmAsm.Codegen
