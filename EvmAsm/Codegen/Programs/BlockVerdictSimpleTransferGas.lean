/-
  EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas

  Simple-transfer gas publication helper for block_verdict.
-/

import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! Compute the EIP-2780 top-frame recipient state-gas charge for an
    empty-code top-level value transfer.

    Result:
      t0 = 0 or StateGasCosts.NEW_ACCOUNT

    Clobbers t0-t6/a0-a4. Requires `s0 = block_verdict params`; `ctxLabel`
    names a simple-transfer/multi-tx context with recipient and value. -/
def topLevelValueRecipientStateGasAsm (tag ctxLabel : String) : String :=
  "  li t0, 0\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
  "  ld t2,  96(t1); ld t3, 104(t1); or t2, t2, t3\n" ++
  "  ld t3, 112(t1); or t2, t2, t3\n" ++
  "  ld t3, 120(t1); or t2, t2, t3\n" ++
  "  beqz t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  -- `process_message` evaluates account liveness against the transaction's
  -- current state.  A preceding value transfer can have made this recipient
  -- live even when the immutable header has no account for it.  Consult the
  -- current account-write tiers first.  Status 1/2 means a present account;
  -- Present-None status 3 deliberately falls through to the authenticated
  -- header predicate below.
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72\n" ++
  "  jal ra, account_writes_lookup_current\n" ++
  "  li t2, 1; beq a0, t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  li t2, 2; beq a0, t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  -- GH #11713: lookup_current requires STATE bit (8) and skips component-only
  -- BALANCE/NONCE/TOUCH/CODE rows so they cannot mask lower-tier code.  A prior
  -- top-level value transfer writes BALANCE|TOUCHED only (vm=0x21).  Spec
  -- charges NEW_ACCOUNT only when value>0 and not is_account_alive
  -- (interpreter.py:285-288 at e5a8caf1b).  is_account_alive = exists ∧
  -- ≠ EMPTY_ACCOUNT (state_tracker.py:445-463); EMPTY_ACCOUNT is zero balance
  -- AND zero nonce AND empty code.  So any of {nonzero bal, nonzero nonce,
  -- nonempty code} on the tx-then-block-cumulative map ⇒ alive.  Map helpers
  -- used: latest_balance, latest_nonce_tx, latest_nonce_block.  Code without
  -- STATE is covered below by a dual-tier HAS_CODE/codeLen probe (same maps,
  -- NOT created-set — mark_account_created is sticky on revert).
  "  addi sp, sp, -32\n" ++
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72; mv a1, sp\n" ++
  "  jal ra, account_writes_latest_balance\n" ++
  "  beqz a0, .L" ++ tag ++ "_recipient_nonce\n" ++
  "  ld t2, 0(sp); ld t3, 8(sp); or t2, t2, t3\n" ++
  "  ld t3, 16(sp); or t2, t2, t3\n" ++
  "  ld t3, 24(sp); or t2, t2, t3\n" ++
  "  bnez t2, .L" ++ tag ++ "_recipient_map_alive\n" ++
  ".L" ++ tag ++ "_recipient_nonce:\n" ++
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72; mv a1, sp\n" ++
  "  jal ra, account_writes_latest_nonce_tx\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_nonce_got\n" ++
  "  la t1, " ++ ctxLabel ++ "; addi a0, t1, 72; mv a1, sp\n" ++
  "  jal ra, account_writes_latest_nonce_block\n" ++
  "  beqz a0, .L" ++ tag ++ "_recipient_code\n" ++
  ".L" ++ tag ++ "_recipient_nonce_got:\n" ++
  "  ld t2, 0(sp); bnez t2, .L" ++ tag ++ "_recipient_map_alive\n" ++
  ".L" ++ tag ++ "_recipient_code:\n" ++
  -- Dual-tier HAS_CODE (mask value 4) with codeLen@+88: tx map then block map.
  -- Re-load addr: nonce helpers clobber t0-t6.
  "  la t1, " ++ ctxLabel ++ "; addi t0, t1, 72\n" ++
  "  la t1, tx_account_writes_count; ld t2, 0(t1); li t3, " ++ toString EvmAsm.Stateless.TX_ACCOUNT_WRITES_AREA.toNat ++ "; li t4, 0\n" ++
  ".L" ++ tag ++ "_recipient_code_tx:\n" ++
  "  bgeu t4, t2, .L" ++ tag ++ "_recipient_code_blk_init\n" ++
  "  slli t5, t4, 7; add t5, t3, t5; mv a0, t5; mv a1, t0; li a2, 20\n" ++
  ".L" ++ tag ++ "_recipient_code_tx_cmp:\n" ++
  "  beqz a2, .L" ++ tag ++ "_recipient_code_tx_key\n" ++
  "  lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .L" ++ tag ++ "_recipient_code_tx_next\n" ++
  "  addi a0, a0, 1; addi a1, a1, 1; addi a2, a2, -1; j .L" ++ tag ++ "_recipient_code_tx_cmp\n" ++
  ".L" ++ tag ++ "_recipient_code_tx_next:\n" ++
  "  addi t4, t4, 1; j .L" ++ tag ++ "_recipient_code_tx\n" ++
  ".L" ++ tag ++ "_recipient_code_tx_key:\n" ++
  "  ld t6, 112(t5); andi t6, t6, 4; beqz t6, .L" ++ tag ++ "_recipient_code_tx_next\n" ++
  "  ld t6, 88(t5); bnez t6, .L" ++ tag ++ "_recipient_map_alive\n" ++
  "  j .L" ++ tag ++ "_recipient_code_tx_next\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_init:\n" ++
  "  la t1, account_writes_count; ld t2, 0(t1); li t3, " ++ toString EvmAsm.Stateless.ACCOUNT_WRITES_AREA.toNat ++ "; li t4, 0\n" ++
  ".L" ++ tag ++ "_recipient_code_blk:\n" ++
  "  bgeu t4, t2, .L" ++ tag ++ "_recipient_map_miss\n" ++
  "  slli t5, t4, 7; add t5, t3, t5; mv a0, t5; mv a1, t0; li a2, 20\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_cmp:\n" ++
  "  beqz a2, .L" ++ tag ++ "_recipient_code_blk_key\n" ++
  "  lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .L" ++ tag ++ "_recipient_code_blk_next\n" ++
  "  addi a0, a0, 1; addi a1, a1, 1; addi a2, a2, -1; j .L" ++ tag ++ "_recipient_code_blk_cmp\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_next:\n" ++
  "  addi t4, t4, 1; j .L" ++ tag ++ "_recipient_code_blk\n" ++
  ".L" ++ tag ++ "_recipient_code_blk_key:\n" ++
  "  ld t6, 112(t5); andi t6, t6, 4; beqz t6, .L" ++ tag ++ "_recipient_code_blk_next\n" ++
  "  ld t6, 88(t5); bnez t6, .L" ++ tag ++ "_recipient_map_alive\n" ++
  "  j .L" ++ tag ++ "_recipient_code_blk_next\n" ++
  ".L" ++ tag ++ "_recipient_map_alive:\n" ++
  "  addi sp, sp, 32\n" ++
  "  j .L" ++ tag ++ "_recipient_state_zero\n" ++
  ".L" ++ tag ++ "_recipient_map_miss:\n" ++
  "  addi sp, sp, 32\n" ++
  ".L" ++ tag ++ "_recipient_state_header:\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t1, 72; ld a3, 80(s0); ld a4, 88(s0)\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  la t2, aex_predicate; ld t2, 0(t2)\n" ++
  "  beqz t2, .L" ++ tag ++ "_recipient_state_charge\n" ++
  "  la t1, " ++ ctxLabel ++ "\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); addi a2, t1, 72; ld a3, 80(s0); ld a4, 88(s0)\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  bnez a0, .L" ++ tag ++ "_recipient_state_zero\n" ++
  "  la t2, aie_predicate; ld t2, 0(t2)\n" ++
  "  beqz t2, .L" ++ tag ++ "_recipient_state_zero\n" ++
  ".L" ++ tag ++ "_recipient_state_charge:\n" ++
  -- GH #11398: no supplied-BAL consult.  execution-specs evaluates recipient
  -- liveness from tracked state alone (state_tracker.py); when the overlays
  -- and the authenticated header both miss, the account is dead at this point
  -- and the NEW_ACCOUNT state-gas charge applies.  The declared BAL arm that
  -- used to skip the charge here papered over tracked-state gaps for shapes
  -- the guest runtime does not replay; the provided BAL is hashed, never read
  -- for execution (fork.py:366/:390).
  ".L" ++ tag ++ "_recipient_state_apply_charge:\n" ++
  liAmsterdamNewAccountStateGas "t0" ++
  "  j .L" ++ tag ++ "_recipient_state_done\n" ++
  ".L" ++ tag ++ "_recipient_state_zero:\n" ++
  "  li t0, 0\n" ++
  ".L" ++ tag ++ "_recipient_state_done:\n"

/-! The simple-transfer/precompile publication arm does not pass through the
    callable dispatcher's post-authorization seam.  Capture the state-gas pool
    at its equivalent point, immediately after intrinsic gas has succeeded and
    before the top-level recipient charge is evaluated.  Keep both pool fields
    as baselines: a direct route may enter with a nonzero spill after a shared
    preparation prefix. -/
def directTransferStateGasBaselineAsm (tag : String) : String :=
  "  la t1, evm_state_gas_left; ld t2, 0(t1)\n" ++
  "  la t1, evm_state_gas_spilled; ld t3, 0(t1)\n" ++
  "  la t4, runtime_tx_state_gas_entry_left; sd t2, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_entry_spilled; sd t3, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_message_left; sd t2, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_message_spilled; sd t3, 0(t4)\n" ++
  "  la t4, runtime_tx_state_gas_entry_valid; li t5, 1; sd t5, 0(t4)\n" ++
  ".L" ++ tag ++ "_state_gas_baseline_done:\n"

/-! Charge the direct top-level recipient state amount held in `t0`.  This is
    deliberately the same reservoir-first/spill-second accounting used by the
    runtime SSTORE path.  The surrounding publish code still performs the
    complete transaction-gas check, so this helper only materializes the pool
    transition and the authoritative executed-state accumulator. -/
def directTransferStateGasChargeAsm (tag : String) : String :=
  "  la t1, evm_state_gas_left; ld t2, 0(t1)\n" ++
  "  bltu t2, t0, .L" ++ tag ++ "_state_gas_spill\n" ++
  "  sub t2, t2, t0; sd t2, 0(t1)\n" ++
  "  j .L" ++ tag ++ "_state_gas_used\n" ++
  ".L" ++ tag ++ "_state_gas_spill:\n" ++
  "  sub t3, t0, t2; sd zero, 0(t1)\n" ++
  "  la t1, evm_state_gas_spilled; ld t4, 0(t1); add t4, t4, t3; sd t4, 0(t1)\n" ++
  ".L" ++ tag ++ "_state_gas_used:\n" ++
  "  la t1, evm_state_gas_used; ld t2, 0(t1); add t2, t2, t0; sd t2, 0(t1)\n"

/-! Compute Amsterdam intrinsic regular gas and calldata floor for the non-creation
    simple-transfer shortcut. This mirrors the runtime dispatcher setup path but
    reads calldata/access-list fields from the already extracted simple-transfer
    context, because the shortcut does not call the runtime dispatcher.

    a0 = simple_transfer_tx_context ptr
    returns a0=status, a1=intrinsic_regular, a2=calldata_floor, a3=intrinsic_state. -/
def simpleTransferIntrinsicGas_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .LUI .x9 (3 : BitVec 20),
    .ADDIW .x9 .x9 (-288 : BitVec 12),
    .LUI .x18 (3 : BitVec 20),
    .ADDIW .x18 .x18 (-288 : BitVec 12),
    .LD .x10 .x8 (24 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.bmvmx_sender_addr (GuestAddrs.simple_transfer_intrinsic_gas + 52)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bmvmx_sender_addr (GuestAddrs.simple_transfer_intrinsic_gas + 52)),
    .JAL .x1 (jalOff GuestAddrs.address_from_pubkey (GuestAddrs.simple_transfer_intrinsic_gas + 60)),
    .AUIPC .x5 (laHi GuestAddrs.bmvmx_sender_addr (GuestAddrs.simple_transfer_intrinsic_gas + 64)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bmvmx_sender_addr (GuestAddrs.simple_transfer_intrinsic_gas + 64)),
    .ADDI .x6 .x8 (72 : BitVec 12),
    .LI .x7 (20 : Word),
    .BEQ .x7 .x0 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 176) (GuestAddrs.simple_transfer_intrinsic_gas + 80)),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LUI .x30 (1 : BitVec 20),
    .ADDIW .x30 .x30 (-1096 : BitVec 12),
    .ADD .x9 .x9 .x30,
    .ADD .x18 .x18 .x30,
    .LD .x5 .x8 (96 : BitVec 12),
    .LD .x6 .x8 (104 : BitVec 12),
    .OR .x5 .x5 .x6,
    .LD .x6 .x8 (112 : BitVec 12),
    .OR .x5 .x5 .x6,
    .LD .x6 .x8 (120 : BitVec 12),
    .OR .x5 .x5 .x6,
    .BEQ .x5 .x0 (20 : BitVec 13),
    .LUI .x30 (1 : BitVec 20),
    .ADDIW .x30 .x30 (1904 : BitVec 12),
    .ADD .x9 .x9 .x30,
    .ADD .x18 .x18 .x30,
    .LD .x19 .x8 (56 : BitVec 12),
    .LD .x20 .x8 (64 : BitVec 12),
    .BEQ .x20 .x0 (44 : BitVec 13),
    .LBU .x5 .x19 (0 : BitVec 12),
    .BEQ .x5 .x0 (16 : BitVec 13),
    .ADDI .x9 .x9 (16 : BitVec 12),
    .ADDI .x18 .x18 (64 : BitVec 12),
    .JAL .x0 (12 : BitVec 21),
    .ADDI .x9 .x9 (4 : BitVec 12),
    .ADDI .x18 .x18 (64 : BitVec 12),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .ADDI .x20 .x20 (-1 : BitVec 12),
    .JAL .x0 (-40 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_access_list_address_count (GuestAddrs.simple_transfer_intrinsic_gas + 228)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_access_list_address_count (GuestAddrs.simple_transfer_intrinsic_gas + 228)),
    .SD .x5 .x0 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_access_list_storage_key_count (GuestAddrs.simple_transfer_intrinsic_gas + 240)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_access_list_storage_key_count (GuestAddrs.simple_transfer_intrinsic_gas + 240)),
    .SD .x5 .x0 (0 : BitVec 12),
    .LD .x5 .x8 (160 : BitVec 12),
    .BEQ .x5 .x0 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 484) (GuestAddrs.simple_transfer_intrinsic_gas + 256)),
    .LI .x12 (7 : Word),
    .LI .x6 (1 : Word),
    .BEQ .x5 .x6 (36 : BitVec 13),
    .LI .x12 (8 : Word),
    .LI .x6 (2 : Word),
    .BEQ .x5 .x6 (24 : BitVec 13),
    .LI .x6 (3 : Word),
    .BEQ .x5 .x6 (16 : BitVec 13),
    .LI .x6 (4 : Word),
    .BEQ .x5 .x6 (8 : BitVec 13),
    .JAL .x0 (jalOff (GuestAddrs.simple_transfer_intrinsic_gas + 484) (GuestAddrs.simple_transfer_intrinsic_gas + 300)),
    .LD .x10 .x8 (176 : BitVec 12),
    .LD .x11 .x8 (184 : BitVec 12),
    .AUIPC .x13 (laHi GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 312)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 312)),
    .AUIPC .x14 (laHi GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 320)),
    .ADDI .x14 .x14 (laLo GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 320)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.simple_transfer_intrinsic_gas + 328)),
    .BNE .x10 .x0 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 708) (GuestAddrs.simple_transfer_intrinsic_gas + 332)),
    .LD .x5 .x8 (176 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 340)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 340)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x10 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 356)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 356)),
    .LD .x11 .x6 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.runtime_tx_access_list_address_count (GuestAddrs.simple_transfer_intrinsic_gas + 368)),
    .ADDI .x12 .x12 (laLo GuestAddrs.runtime_tx_access_list_address_count (GuestAddrs.simple_transfer_intrinsic_gas + 368)),
    .AUIPC .x13 (laHi GuestAddrs.runtime_tx_access_list_storage_key_count (GuestAddrs.simple_transfer_intrinsic_gas + 376)),
    .ADDI .x13 .x13 (laLo GuestAddrs.runtime_tx_access_list_storage_key_count (GuestAddrs.simple_transfer_intrinsic_gas + 376)),
    .JAL .x1 (jalOff GuestAddrs.access_list_count (GuestAddrs.simple_transfer_intrinsic_gas + 384)),
    .BNE .x10 .x0 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 708) (GuestAddrs.simple_transfer_intrinsic_gas + 388)),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_access_list_address_count (GuestAddrs.simple_transfer_intrinsic_gas + 392)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_access_list_address_count (GuestAddrs.simple_transfer_intrinsic_gas + 392)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (32 : BitVec 13),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (184 : BitVec 12),
    .ADD .x9 .x9 .x7,
    .LI .x7 (1280 : Word),
    .ADD .x18 .x18 .x7,
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_access_list_storage_key_count (GuestAddrs.simple_transfer_intrinsic_gas + 436)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_access_list_storage_key_count (GuestAddrs.simple_transfer_intrinsic_gas + 436)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (36 : BitVec 13),
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (952 : BitVec 12),
    .ADD .x9 .x9 .x7,
    .LUI .x7 (1 : BitVec 20),
    .ADDIW .x7 .x7 (-2048 : BitVec 12),
    .ADD .x18 .x18 .x7,
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LD .x5 .x8 (160 : BitVec 12),
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 608) (GuestAddrs.simple_transfer_intrinsic_gas + 492)),
    .LD .x10 .x8 (176 : BitVec 12),
    .LD .x11 .x8 (184 : BitVec 12),
    .LI .x12 (9 : Word),
    .AUIPC .x13 (laHi GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 508)),
    .ADDI .x13 .x13 (laLo GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 508)),
    .AUIPC .x14 (laHi GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 516)),
    .ADDI .x14 .x14 (laLo GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 516)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_nth_item (GuestAddrs.simple_transfer_intrinsic_gas + 524)),
    .BNE .x10 .x0 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 708) (GuestAddrs.simple_transfer_intrinsic_gas + 528)),
    .LD .x5 .x8 (176 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 536)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bsg_access_off (GuestAddrs.simple_transfer_intrinsic_gas + 536)),
    .LD .x6 .x6 (0 : BitVec 12),
    .ADD .x10 .x5 .x6,
    .AUIPC .x6 (laHi GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 552)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bsg_access_len (GuestAddrs.simple_transfer_intrinsic_gas + 552)),
    .LD .x11 .x6 (0 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.teer_auth_count (GuestAddrs.simple_transfer_intrinsic_gas + 564)),
    .ADDI .x12 .x12 (laLo GuestAddrs.teer_auth_count (GuestAddrs.simple_transfer_intrinsic_gas + 564)),
    .JAL .x1 (jalOff GuestAddrs.rlp_list_count_items (GuestAddrs.simple_transfer_intrinsic_gas + 572)),
    .BNE .x10 .x0 (brOff (GuestAddrs.simple_transfer_intrinsic_gas + 708) (GuestAddrs.simple_transfer_intrinsic_gas + 576)),
    .AUIPC .x5 (laHi GuestAddrs.teer_auth_count (GuestAddrs.simple_transfer_intrinsic_gas + 580)),
    .ADDI .x5 .x5 (laLo GuestAddrs.teer_auth_count (GuestAddrs.simple_transfer_intrinsic_gas + 580)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LUI .x7 (2 : BitVec 20),
    .ADDIW .x7 .x7 (-376 : BitVec 12),
    .MUL .x6 .x6 .x7,
    .ADD .x9 .x9 .x6,
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_calldata_floor (GuestAddrs.simple_transfer_intrinsic_gas + 608)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_calldata_floor (GuestAddrs.simple_transfer_intrinsic_gas + 608)),
    .SD .x5 .x18 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_intrinsic_regular (GuestAddrs.simple_transfer_intrinsic_gas + 620)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_intrinsic_regular (GuestAddrs.simple_transfer_intrinsic_gas + 620)),
    .SD .x5 .x9 (0 : BitVec 12),
    .SD .x2 .x9 (48 : BitVec 12),
    .SD .x2 .x18 (56 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.bvgr_tx_state_gas (GuestAddrs.simple_transfer_intrinsic_gas + 640)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bvgr_tx_state_gas (GuestAddrs.simple_transfer_intrinsic_gas + 640)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x9 .x2 (48 : BitVec 12),
    .LD .x18 .x2 (56 : BitVec 12),
    .AUIPC .x7 (laHi GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.simple_transfer_intrinsic_gas + 660)),
    .ADDI .x7 .x7 (laLo GuestAddrs.runtime_tx_auth_regular_refund (GuestAddrs.simple_transfer_intrinsic_gas + 660)),
    .LD .x7 .x7 (0 : BitVec 12),
    .ADD .x9 .x9 .x7,
    .AUIPC .x5 (laHi GuestAddrs.runtime_tx_intrinsic_regular (GuestAddrs.simple_transfer_intrinsic_gas + 676)),
    .ADDI .x5 .x5 (laLo GuestAddrs.runtime_tx_intrinsic_regular (GuestAddrs.simple_transfer_intrinsic_gas + 676)),
    .SD .x5 .x9 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .MV .x11 .x9,
    .MV .x12 .x18,
    .MV .x13 .x6,
    .JAL .x0 (20 : BitVec 21),
    .LI .x10 (1 : Word),
    .LI .x11 (0 : Word),
    .LI .x12 (0 : Word),
    .LI .x13 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `simpleTransferIntrinsicGas_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def simpleTransferIntrinsicGas_relocs : RelocTable :=
  [ (13, .la .x11 "bmvmx_sender_addr"),
    (15, .jal .x1 "address_from_pubkey"),
    (16, .la .x5 "bmvmx_sender_addr"),
    (57, .la .x5 "runtime_tx_access_list_address_count"),
    (60, .la .x5 "runtime_tx_access_list_storage_key_count"),
    (78, .la .x13 "bsg_access_off"),
    (80, .la .x14 "bsg_access_len"),
    (82, .jal .x1 "rlp_list_nth_item"),
    (85, .la .x6 "bsg_access_off"),
    (89, .la .x6 "bsg_access_len"),
    (92, .la .x12 "runtime_tx_access_list_address_count"),
    (94, .la .x13 "runtime_tx_access_list_storage_key_count"),
    (96, .jal .x1 "access_list_count"),
    (98, .la .x5 "runtime_tx_access_list_address_count"),
    (109, .la .x5 "runtime_tx_access_list_storage_key_count"),
    (127, .la .x13 "bsg_access_off"),
    (129, .la .x14 "bsg_access_len"),
    (131, .jal .x1 "rlp_list_nth_item"),
    (134, .la .x6 "bsg_access_off"),
    (138, .la .x6 "bsg_access_len"),
    (141, .la .x12 "teer_auth_count"),
    (143, .jal .x1 "rlp_list_count_items"),
    (145, .la .x5 "teer_auth_count"),
    (152, .la .x5 "runtime_tx_calldata_floor"),
    (155, .la .x5 "runtime_tx_intrinsic_regular"),
    (160, .la .x5 "bvgr_tx_state_gas"),
    (165, .la .x7 "runtime_tx_auth_regular_refund"),
    (169, .la .x5 "runtime_tx_intrinsic_regular") ]

def simpleTransferIntrinsicGasFunction : String :=
  "simple_transfer_intrinsic_gas:\n" ++ emitProgramR simpleTransferIntrinsicGas_prog simpleTransferIntrinsicGas_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `simpleTransferIntrinsicGas_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem simpleTransferIntrinsicGasFunction_eq_prog :
    simpleTransferIntrinsicGasFunction = "simple_transfer_intrinsic_gas:\n" ++ emitProgramR simpleTransferIntrinsicGas_prog simpleTransferIntrinsicGas_relocs := rfl

#guard simpleTransferIntrinsicGasFunction.startsWith "simple_transfer_intrinsic_gas:\n"
#guard simpleTransferIntrinsicGas_prog.length = 189
end EvmAsm.Codegen
