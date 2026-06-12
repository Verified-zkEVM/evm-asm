/-
  EvmAsm.Codegen.Programs.BlockVerdictChainConfig

  Assembly helpers for stateless-input structural validation:
  public_keys_valid and chain_config_valid.
  Carved out of BlockVerdict.lean to stay within the 1500-line file-size cap.
-/

namespace EvmAsm.Codegen

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
def publicKeysValidFunction : String :=
  "public_keys_valid:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # exec_payload\n" ++
  "  # tx_count from the SSZ transactions list.\n" ++
  "  addi a0, s1, 504; jal ra, bgv_u32le\n" ++
  "  mv s2, a0                   # transactions_offset\n" ++
  "  addi a0, s1, 508; jal ra, bgv_u32le\n" ++
  "  mv s3, a0                   # withdrawals_offset\n" ++
  "  li s4, 0                    # tx_count\n" ++
  "  bleu s3, s2, .Lpkv_have_tx_count\n" ++
  "  sub t0, s3, s2\n" ++
  "  li t1, 4; bltu t0, t1, .Lpkv_fail\n" ++
  "  add t2, s1, s2\n" ++
  "  mv a0, t2; jal ra, bgv_u32le\n" ++
  "  andi t1, a0, 3; bnez t1, .Lpkv_fail\n" ++
  "  srli s4, a0, 2\n" ++
  "  slli t1, s4, 2; bgtu t1, t0, .Lpkv_fail\n" ++
  ".Lpkv_have_tx_count:\n" ++
  "  # public_keys start = SSZ_BASE + outer.offsets[3]. End = zisk input\n" ++
  "  # payload start + host length; host length includes schema id + SSZ bytes.\n" ++
  "  addi a0, s0, 12; jal ra, bgv_u32le\n" ++
  "  add s5, s0, a0              # public_keys ptr\n" ++
  "  li a0, 0x40000008; jal ra, bgv_u64le\n" ++
  "  li t0, 0x40000010; add s6, t0, a0     # end of host payload\n" ++
  "  bltu s6, s5, .Lpkv_fail\n" ++
  "  sub s7, s6, s5              # public_keys byte length\n" ++
  "  li t0, 65\n" ++
  "  remu t1, s7, t0; bnez t1, .Lpkv_fail\n" ++
  "  divu s8, s7, t0             # public key count\n" ++
  -- xpz16: EXACT-equality count check, restoring the pre-#8558 `bne`. x04we (#8558) relaxed
  -- this to `bltu` (reject only count < tx_count) on the premise that the spec merely INDEXES
  -- transaction_public_keys[tx_index] for index in [0, tx_count) (fork.py:1044-1046) so surplus
  -- keys are harmless -- but that MISSED execute_block (fork.py:308-312), which raises
  -- InvalidBlock when `transaction_public_keys is not None and len(transaction_public_keys) !=
  -- len(block.transactions)`. In the stateless path public_keys is ALWAYS non-None (stateless.py
  -- :382 passes stateless_input.public_keys), so the exact-equality check is active for every
  -- block: count > tx_count is REJECTED by the reference before any tx runs. The `bltu` therefore
  -- false-ACCEPTED count > tx_count. Soundness-additive (only adds a reject); no false-reject:
  -- public_keys is the LAST SszStatelessInput field (stateless_ssz.py:211), so the guest's byte
  -- length s7 = section_end - public_keys_start is exact and count == tx_count for every valid block.
  "  bne s8, s4, .Lpkv_fail\n" ++
  "  la t0, bv_public_keys_ptr; sd s5, 0(t0)\n" ++
  "  la t0, bv_public_keys_len; sd s7, 0(t0)\n" ++
  "  li s9, 0\n" ++
  ".Lpkv_loop:\n" ++
  "  beq s9, s4, .Lpkv_ok\n" ++   -- xpz16: count == tx_count now (exact-equality above), so [0, tx_count) is every key
  "  li t0, 65; mul t1, s9, t0; add t2, s5, t1\n" ++
  "  lbu t3, 0(t2); li t4, 4; bne t3, t4, .Lpkv_fail\n" ++
  "  li t3, 1; li t4, 0\n" ++
  ".Lpkv_coord_loop:\n" ++
  "  li t5, 65; beq t3, t5, .Lpkv_coord_done\n" ++
  "  add t6, t2, t3; lbu t6, 0(t6); or t4, t4, t6\n" ++
  "  addi t3, t3, 1; j .Lpkv_coord_loop\n" ++
  ".Lpkv_coord_done:\n" ++
  "  beqz t4, .Lpkv_fail\n" ++
  "  addi s9, s9, 1; j .Lpkv_loop\n" ++
  ".Lpkv_ok:\n" ++
  "  li a0, 0; j .Lpkv_ret\n" ++
  ".Lpkv_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpkv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-! ## chain_config_valid -- execution-specs validate_chain_config mirror.
    a0 = SSZ_BASE   a1 = exec_payload ptr
    a0 (output) = 0 ok, 1 unsupported/inactive/malformed chain_config.

    This checks the Amsterdam stateless guest's semantic chain-config contract:
    active_fork.fork is Amsterdam, activation sets block_number or timestamp and
    is active for the target payload, and blob_schedule is exactly the Amsterdam
    schedule compiled into execution-specs. -/
def chainConfigValidFunction : String :=
  "chain_config_valid:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s1, a1                   # exec_payload\n" ++
  "  addi a0, s0, 8; jal ra, bgv_u32le\n" ++
  "  add s2, s0, a0              # chain_config ptr\n" ++
  -- bmvmx.3.2: capture the execution chain_id (SszChainConfig.chain_id is the
  -- fixed field at offset 0, a u64 LE) into the bv_chain_id global so the
  -- per-tx sender-recovery gate (verify_public_keys_match_senders) can feed it
  -- to legacy EIP-155 recovery. chain_config_valid runs early in the verdict
  -- and its caller rejects on a nonzero return, so bv_chain_id is only consumed
  -- on the success path. Soundness-inert here (just records a value).
  "  mv a0, s2; jal ra, bgv_u64le\n" ++
  "  la t0, bv_chain_id; sd a0, 0(t0)\n" ++
  "  addi a0, s0, 12; jal ra, bgv_u32le\n" ++
  "  add s3, s0, a0              # public_keys ptr = chain_config end\n" ++
  "  bltu s3, s2, .Lccv_fail\n" ++
  "  sub t0, s3, s2; li t1, 12; bltu t0, t1, .Lccv_fail\n" ++
  "  addi a0, s2, 8; jal ra, bgv_u32le\n" ++
  "  li t0, 12; bne a0, t0, .Lccv_fail\n" ++
  "  add s4, s2, a0              # active_fork ptr\n" ++
  "  bltu s3, s4, .Lccv_fail\n" ++
  "  sub s10, s3, s4             # active_fork len\n" ++
  "  li t0, 40; bltu s10, t0, .Lccv_fail\n" ++
  "  mv a0, s4; jal ra, bgv_u64le\n" ++
  "  li t0, 24                   # ProtocolFork.Amsterdam enum index\n" ++
  "  bne a0, t0, .Lccv_fail\n" ++
  "  addi a0, s4, 8; jal ra, bgv_u32le\n" ++
  "  li t0, 16; bne a0, t0, .Lccv_fail\n" ++
  "  mv s11, a0                  # activation offset\n" ++
  "  addi a0, s4, 12; jal ra, bgv_u32le\n" ++
  "  mv s8, a0                   # blob_schedule offset\n" ++
  "  bltu s8, s11, .Lccv_fail\n" ++
  "  bgtu s8, s10, .Lccv_fail\n" ++
  "  add s5, s4, s11             # activation ptr\n" ++
  "  sub s6, s8, s11             # activation len\n" ++
  "  li t0, 8; beq s6, t0, .Lccv_fail\n" ++
  "  li t0, 16; beq s6, t0, .Lccv_activation_len16\n" ++
  "  li t0, 24; beq s6, t0, .Lccv_activation_len24\n" ++
  "  j .Lccv_fail\n" ++
  ".Lccv_activation_len16:\n" ++
  "  addi a0, s5, 0; jal ra, bgv_u32le\n" ++
  "  li t0, 8; bne a0, t0, .Lccv_fail\n" ++
  "  addi a0, s5, 4; jal ra, bgv_u32le\n" ++
  "  li t0, 8; beq a0, t0, .Lccv_check_ts_at8\n" ++
  "  li t0, 16; beq a0, t0, .Lccv_check_bn_at8\n" ++
  "  j .Lccv_fail\n" ++
  ".Lccv_activation_len24:\n" ++
  "  addi a0, s5, 0; jal ra, bgv_u32le\n" ++
  "  li t0, 8; bne a0, t0, .Lccv_fail\n" ++
  "  addi a0, s5, 4; jal ra, bgv_u32le\n" ++
  "  li t0, 16; bne a0, t0, .Lccv_fail\n" ++
  "  addi a0, s5, 8; jal ra, bgv_u64le\n" ++
  "  mv s9, a0\n" ++
  "  addi a0, s1, 404; jal ra, bgv_u64le\n" ++
  "  bltu a0, s9, .Lccv_fail\n" ++
  "  addi a0, s5, 16; jal ra, bgv_u64le\n" ++
  "  mv s9, a0\n" ++
  "  addi a0, s1, 428; jal ra, bgv_u64le\n" ++
  "  bltu a0, s9, .Lccv_fail\n" ++
  "  j .Lccv_check_blob\n" ++
  ".Lccv_check_bn_at8:\n" ++
  "  addi a0, s5, 8; jal ra, bgv_u64le\n" ++
  "  mv s9, a0\n" ++
  "  addi a0, s1, 404; jal ra, bgv_u64le\n" ++
  "  bltu a0, s9, .Lccv_fail\n" ++
  "  j .Lccv_check_blob\n" ++
  ".Lccv_check_ts_at8:\n" ++
  "  addi a0, s5, 8; jal ra, bgv_u64le\n" ++
  "  mv s9, a0\n" ++
  "  addi a0, s1, 428; jal ra, bgv_u64le\n" ++
  "  bltu a0, s9, .Lccv_fail\n" ++
  ".Lccv_check_blob:\n" ++
  "  sub s6, s10, s8             # blob_schedule len\n" ++
  "  li t0, 24; bne s6, t0, .Lccv_fail\n" ++
  "  add s5, s4, s8              # blob_schedule ptr\n" ++
  "  mv a0, s5; jal ra, bgv_u64le\n" ++
  "  li t0, 14; bne a0, t0, .Lccv_fail\n" ++
  "  addi a0, s5, 8; jal ra, bgv_u64le\n" ++
  "  li t0, 21; bne a0, t0, .Lccv_fail\n" ++
  "  addi a0, s5, 16; jal ra, bgv_u64le\n" ++
  "  li t0, 11684671; bne a0, t0, .Lccv_fail\n" ++
  "  li a0, 0; j .Lccv_ret\n" ++
  ".Lccv_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lccv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

end EvmAsm.Codegen
