/-
  EvmAsm.Codegen.Programs.Selfdestruct

  SELFDESTRUCT runtime assembly helpers split out of `Programs.Noop` to keep
  the halt-handler module under the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.EIP7708Logs
import EvmAsm.Codegen.Programs.AmsterdamSystemTx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def selfdestructNewAccountSurchargeAsm : String :=
  "  ld t0, 584(x20)\n" ++
  "  beqz t0, .L_selfdestruct_surcharge_no_ctx\n" ++
  "  mv t0, x20\n" ++
  "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_origin" "t0" "t1" "t2" "t3" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, bal_output_scratch\n" ++
  "  jal ra, balance_at_header_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
    "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
  -- The spec reads the originator's LIVE balance (system.py selfdestruct:
  -- get_account(current_target).balance != 0). A zero-header-balance contract
  -- funded THIS tx (the tx value credit, or an earlier same-tx transfer) must
  -- still charge; prefer the journaled latest balance over the header value.
  -- The layered AccountState lookup uses the standard caller-saved a0-a3
  -- registers.  Preserve the live EVM stack cursor (x13) as well as the
  -- runtime context registers across the lookup.
  "  addi sp, sp, -24\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  la a0, " ++ runtimeAccessSeedScratchLabel ++ "\n  la a1, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 24\n" ++
    "  beqz t6, .L_selfdestruct_origin_env_bal\n" ++
  "  la t0, evm_selfdestruct_balance_scratch\n  li t2, 4\n" ++
  ".L_selfdestruct_origin_live_scan:\n" ++
  "  ld t1, 0(t0)\n  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  addi t0, t0, 8\n  addi t2, t2, -1\n  bnez t2, .L_selfdestruct_origin_live_scan\n" ++
  "  j .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_origin_env_bal:\n" ++
  -- env+32 is the frame's live SELFBALANCE word (the staging credits the
  -- incoming call value into it), so a nonzero byte there is the spec's live
  -- `get_account(current_target).balance != 0` even when the header-state
  -- balance is zero (contract funded by this very tx).
  "  addi t0, x20, 32\n  li t2, 32\n" ++
  ".L_selfdestruct_origin_env_scan:\n" ++
  "  lbu t1, 0(t0)\n  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .L_selfdestruct_origin_env_scan\n" ++
  "  la t0, bal_output_scratch\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 8(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 16(t0)\n" ++
  "  bnez t1, .L_selfdestruct_origin_nonzero\n" ++
  "  ld t1, 24(t0)\n" ++
  "  beqz t1, .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_origin_nonzero:\n" ++
    "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, evm_selfdestruct_beneficiary\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  jal ra, account_exists_at_header_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, aex_predicate\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_charge_new_account\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, evm_selfdestruct_beneficiary\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  jal ra, account_is_empty_at_header_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
  "  la t0, aie_predicate\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_surcharge_no_ctx:\n" ++
  "  addi t0, x20, 32; li t2, 32\n" ++
  ".L_selfdestruct_no_ctx_bal_loop:\n" ++
  "  lbu t1, 0(t0); bnez t1, .L_selfdestruct_charge_new_account\n" ++
  "  addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_selfdestruct_no_ctx_bal_loop\n" ++
  "  j .L_selfdestruct_surcharge_done\n" ++
  ".L_selfdestruct_charge_new_account:\n" ++
  -- Header-state lookup cannot see a beneficiary created earlier in this
  -- transaction. The per-tx CREATE table is frame-journaled, so a hit proves
  -- live `tx_state.created_accounts` membership while a reverted child is
  -- absent. Check it at the common charge gate (not merely the no-context arm).
  "  addi sp, sp, -16\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  jal ra, create_creator_nonce_contains\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  addi sp, sp, 16\n" ++
  "  bnez t6, .L_selfdestruct_surcharge_done\n" ++
    -- `is_account_alive` reads the live transaction state. A prior committed
  -- value transfer can therefore make a pre-state-empty beneficiary alive even
  -- when it came from a different SELFDESTRUCT origin (CALLCODE/DELEGATECALL).
  -- Consult the frame-journaled nonstorage effect log before the origin-only
  -- repeated-SELFDESTRUCT shortcut below. A nonzero latest balance means the
  -- beneficiary is alive, so ACCOUNT_WRITE and NEW_ACCOUNT are not charged.
  "  addi sp, sp, -16\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n  la a1, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  addi sp, sp, 16\n" ++
  "  beqz t6, .L_selfdestruct_live_beneficiary_done\n" ++
  "  la t0, evm_selfdestruct_balance_scratch\n  li t1, 4\n" ++
  ".L_selfdestruct_live_beneficiary_scan:\n" ++
  "  ld t2, 0(t0)\n  bnez t2, .L_selfdestruct_surcharge_done\n" ++
  "  addi t0, t0, 8\n  addi t1, t1, -1\n  bnez t1, .L_selfdestruct_live_beneficiary_scan\n" ++
  ".L_selfdestruct_live_beneficiary_done:\n" ++
  -- Do not use the transaction's seen-origin set to suppress this charge. The
  -- live-balance check above already handles an origin whose earlier
  -- SELFDESTRUCT drained it to zero. If a later CALL funds that same origin,
  -- its next SELFDESTRUCT is a fresh nonzero transfer and an absent beneficiary
  -- must pay NEW_ACCOUNT again (multi_selfdestruct d2).
  -- coc3g.6 (EIP-6780 self-destruct-to-self / created-in-tx beneficiary): the spec gates the
  -- NEW_ACCOUNT state-gas charge on `not is_account_alive(beneficiary)` (amsterdam
  -- vm/instructions/system.py selfdestruct: needs_state_gas). `is_account_alive` consults the LIVE
  -- state, which includes accounts CREATEd earlier in this same tx (tx_state.created_accounts) --
  -- but `account_exists_at_header_state_root` / `account_is_empty_at_header_state_root` above only
  -- see the BLOCK-PRE witness, where a same-tx-created contract is ABSENT. So a SELFDESTRUCT whose
  -- beneficiary is a same-tx-created contract (e.g. selfdestruct-to-self of a freshly CREATEd child,
  -- bytecode `30ff`) was wrongly classified as new-account and charged STATE_BYTES_PER_NEW_ACCOUNT
  -- state gas. That spurious charge both over-counts state gas AND (when it drains the reservoir +
  -- spills into the frame) derails the SD tail so the created-in-tx deletion was never recorded ->
  -- the exec-vs-BAL non-storage comparator false-rejected (bv_fail=44).
  --
  -- coc3g.6 part 2 (the constructor self-destruct-to-self case, selfdestruct_to_self_same_tx
  -- with_balance bv_fail=41): a contract that SELFDESTRUCTs IN ITS OWN CONSTRUCTOR (initcode
  -- `30ff` = ADDRESS;SELFDESTRUCT) with beneficiary==self deposits NO code, so the
  -- find_code_effect_by_address skip below MISSES and the charge wrongly fires. The
  -- authoritative created_accounts signal here is identical to NoopHalt's constructor-SD detection:
  -- we are executing INSIDE the CREATE child frame (create_frame_descend set
  -- create_frame_flag[current_depth]=1, not yet cleared), so that flag IS the originator's
  -- created_accounts membership. For SELFDESTRUCT the originator == evm.message.current_target ==
  -- env.ADDRESS; the to_self case is beneficiary==env.ADDRESS, so is_account_alive(beneficiary)
  -- is then is_account_alive(originator)=True (just created) -> needs_state_gas=False -> skip.
  -- Soundness: gated on beneficiary==self AND create_frame_flag[depth]=1, so it can only suppress
  -- the charge for a genuinely same-tx-created self-beneficiary (the spec's exact alive case),
  -- never for a witnessed/pre-existing account. Compute self (origin) as a 20B BE from x20 env
  -- ADDRESS into runtimeAccessSeedScratchLabel and compare to evm_selfdestruct_beneficiary.
  "  la t0, create_frame_flag\n" ++
  "  la t1, evm_call_depth; ld t1, 0(t1); slli t1, t1, 3; add t0, t0, t1; ld t0, 0(t0)\n" ++
  "  beqz t0, .L_selfdestruct_csg_not_ctit\n" ++
  "  mv t0, x20\n" ++
  "  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_csg_self" "t0" "t1" "t2" "t3" ++
  "  la t0, " ++ runtimeAccessSeedScratchLabel ++ "\n  la t1, evm_selfdestruct_beneficiary\n  li t2, 20\n" ++
  ".L_selfdestruct_csg_self_cmp:\n" ++
  "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n  bne t3, t4, .L_selfdestruct_csg_not_ctit\n" ++
  "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .L_selfdestruct_csg_self_cmp\n" ++
  "  j .L_selfdestruct_surcharge_done\n" ++   -- beneficiary==self AND created-in-tx (alive) -> no NEW_ACCOUNT state gas
  ".L_selfdestruct_csg_not_ctit:\n" ++
  -- Mirror is_account_alive's created_accounts membership through the shared
  -- current AccountState: a beneficiary created in this transaction is alive,
  -- including an empty-code CREATE, so skip the charge.
  -- The layered AccountState lookup uses the standard caller-saved a0-a3
  -- registers. Preserve the live EVM stack cursor (x13) with the runtime
  -- context registers across the lookup.
  "  addi sp, sp, -24\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  jal ra, code_state_lookup_current\n" ++
  "  mv t1, a0\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 24\n" ++
  -- pin is_account_alive (state_tracker.py:445-463) + system.py:669
  -- selfdestruct NEW_ACCOUNT on beneficiary. Status-2 bal-zero EIP-6780
  -- tombstone is EMPTY (after tombstone writer clears nonce) and must charge;
  -- status-2 with nonzero balance is alive (funded EOA / bal-preserved tombstone).
  -- Mirror ChildFrameHandlers nacc (#11334/#11362); do not use bare
  -- codeStateStatusIsLiveAsm alone.
  "  li t0, 2; bne t1, t0, .L_selfdestruct_csg_std\n" ++
  "  addi sp, sp, -24\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  jal ra, account_state_tombstone_balance_zero\n" ++
  "  mv t0, a0\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 24\n" ++
  "  bnez t0, .L_selfdestruct_csg_not_live\n" ++
  "  li t1, 2\n" ++
  ".L_selfdestruct_csg_std:\n" ++
  codeStateStatusIsLiveAsm "t1" ++
  "  bnez t1, .L_selfdestruct_surcharge_done\n" ++   -- beneficiary alive -> no NEW_ACCOUNT state gas
  ".L_selfdestruct_csg_not_live:\n" ++
  -- SELFDESTRUCT to a new (not-alive) beneficiary with a non-zero originator
  -- balance creates the beneficiary account. Amsterdam execution-specs charges
  -- regular gas first: base(5000, dispatch) + cold access(3000, above) +
  -- ACCOUNT_WRITE(8000), then charges StateGasCosts.NEW_ACCOUNT =
  -- STATE_BYTES_PER_NEW_ACCOUNT(120)*COST_PER_STATE_BYTE(1530) = 183600 in the
  -- state-gas dimension (vm/instructions/system.py selfdestruct). Charge the
  -- ACCOUNT_WRITE regular gas before touching the state-gas reservoir so a
  -- regular-gas OOG does not inflate parent state gas on frame failure.
    "  ld t1, 568(x20)\n" ++
  "  li t2, 8000\n" ++
  "  bltu t1, t2, .exit_outofgas\n" ++
  "  sub t1, t1, t2\n" ++
  "  sd t1, 568(x20)\n" ++
  -- Mirror charge_state_gas (ChildFrameHandlerTails / Storage.lean): drain
  -- evm_state_gas_left, spill the remainder into the frame gas_left (568(x20)), OOG when both
  -- reservoirs are short; state_gas_used += charge. No refund snapshot -- the spec does not
  -- credit_state_gas_refund for SELFDESTRUCT; the frame-entry 624/632 state-gas snapshot already
  -- rolls it back if a parent reverts the frame's effects.
  liStateGasRuntime "t0" amsterdamStateBytesPerNewAccountV2 ++
  "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
  "  bgeu t2, t0, .L_selfdestruct_csg_res\n" ++
  "  sub t3, t0, t2\n  sd x0, 0(t1)\n" ++
  "  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n" ++
  "  sub t2, t2, t3\n  sd t2, 568(x20)\n  j .L_selfdestruct_csg_used\n" ++
  ".L_selfdestruct_csg_res:\n" ++
  "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
  ".L_selfdestruct_csg_used:\n" ++
  "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
  ".L_selfdestruct_surcharge_done:\n"

/-- Append the current origin to the transaction-journaled SELFDESTRUCT set.

    The set models "a prior SELFDESTRUCT of this origin moved its ENTIRE live
    balance away" (the repeated-SELFDESTRUCT no-charge shortcut). A
    SELFDESTRUCT whose beneficiary IS the origin moves the balance to itself
    (system.py move_ether originator -> originator), so the origin's balance
    survives and a LATER selfdestruct to an absent beneficiary still charges
    NEW_ACCOUNT (double_selfdestruct code-self-destruct*): do not record it. -/
def selfdestructRecordSeenOriginAsm : String :=
  "  mv t0, x20\n  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_seen_selfchk" "t0" "t1" "t2" "t4" ++
  "  la t0, " ++ runtimeAccessSeedScratchLabel ++ "\n  la t1, evm_selfdestruct_beneficiary\n  li t2, 20\n" ++
  ".L_selfdestruct_seen_selfcmp:\n" ++
  "  beqz t2, .L_selfdestruct_seen_record_done\n" ++
  "  lbu t3, 0(t0)\n  lbu t4, 0(t1)\n  bne t3, t4, .L_selfdestruct_seen_notself\n" ++
  "  addi t0, t0, 1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  j .L_selfdestruct_seen_selfcmp\n" ++
  ".L_selfdestruct_seen_notself:\n" ++
  "  la t0, evm_selfdestruct_seen_overflow\n  ld t1, 0(t0)\n  bnez t1, .L_selfdestruct_seen_record_done\n" ++
  "  la t0, evm_selfdestruct_seen_count\n  ld t1, 0(t0)\n  li t2, " ++ toString selfdestructSeenOriginCap ++ "\n" ++
  "  bgeu t1, t2, .L_selfdestruct_seen_record_overflow\n" ++
  "  slli t2, t1, 5\n  la t3, evm_selfdestruct_seen_table\n  add t3, t3, t2\n" ++
  "  sd x0, 0(t3)\n  sd x0, 8(t3)\n  sd x0, 16(t3)\n  sd x0, 24(t3)\n" ++
  "  mv t0, x20\n  la t1, " ++ runtimeAccessSeedScratchLabel ++ "\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_seen_record" "t0" "t1" "t2" "t4" ++
  "  la t4, " ++ runtimeAccessSeedScratchLabel ++ "\n  li t5, 20\n" ++
  ".L_selfdestruct_seen_record_copy:\n" ++
  "  lbu t6, 0(t4)\n  sb t6, 0(t3)\n  addi t4, t4, 1\n  addi t3, t3, 1\n  addi t5, t5, -1\n  bnez t5, .L_selfdestruct_seen_record_copy\n" ++
  "  la t0, evm_selfdestruct_seen_count\n  ld t1, 0(t0)\n  addi t1, t1, 1\n  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_seen_record_done\n" ++
  ".L_selfdestruct_seen_record_overflow:\n" ++
  "  la t0, evm_selfdestruct_seen_overflow\n  li t1, 1\n  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_seen_record_done:\n"

/--
Load the origin and beneficiary account RLP payloads needed by the later
SELFDESTRUCT balance-transfer/rewrite step.

The helper runs only when the runtime input carried the account-witness
context. It keeps today's no-witness runtime behavior unchanged by recording a
status and continuing the opcode tail.

Scratch outputs:
  `sdai_status`          : 0 success, 1 no context, 2 header root failure,
                           3 origin lookup failure, 4 beneficiary lookup failure
  `sdai_origin_len`      : raw origin account RLP length on success
  `sdai_beneficiary_len` : raw beneficiary account RLP length on success
  `sdai_origin_rlp` / `sdai_beneficiary_rlp` hold the raw account RLP bytes.
-/
def selfdestructLoadAccountInputsAsm : String :=
  "  la t0, sdai_status\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t0, sdai_origin_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, sdai_beneficiary_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  mv t0, x20\n" ++
  "  la t1, sdai_origin_address\n" ++
  runtimeAccessWordToBe20Asm "selfdestruct_account_origin" "t0" "t1" "t2" "t3" ++
  "  ld t0, 584(x20)\n" ++
  "  beqz t0, .L_selfdestruct_accounts_done\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  ld a0, 576(x20)\n" ++
  "  ld a1, 584(x20)\n" ++
  "  la a2, sdai_state_root\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_accounts_header_fail\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sdai_origin_address\n" ++
  "  li a1, 20\n" ++
  "  la a2, sdai_state_root\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, sdai_origin_rlp\n" ++
  "  la a6, sdai_origin_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_accounts_origin_fail\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  li a1, 20\n" ++
  "  la a2, sdai_state_root\n" ++
  "  ld a3, 592(x20)\n" ++
  "  ld a4, 600(x20)\n" ++
  "  la a5, sdai_beneficiary_rlp\n" ++
  "  la a6, sdai_beneficiary_len\n" ++
  "  jal ra, mpt_lookup_by_key\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_accounts_beneficiary_fail\n" ++
  "  la t0, sdai_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_accounts_done\n" ++
  ".L_selfdestruct_accounts_header_fail:\n" ++
  "  la t0, sdai_status\n" ++
  "  li t1, 2\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_accounts_done\n" ++
  ".L_selfdestruct_accounts_origin_fail:\n" ++
  "  la t0, sdai_status\n" ++
  "  li t1, 3\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_accounts_done\n" ++
  ".L_selfdestruct_accounts_beneficiary_fail:\n" ++
  "  la t0, sdai_status\n" ++
  "  li t1, 4\n" ++
  "  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_accounts_done:\n"

/--
Apply the loaded SELFDESTRUCT account RLPs through
`selfdestruct_balance_transfer` when account inputs are available.

This stages the rewritten account RLPs in `sdai_transfer_output` for the
post-state descriptor integration step. It deliberately records a precise
status and continues the existing runtime exit path so no-witness opcode tests
keep their current behavior.

Scratch outputs:
  `sdai_transfer_status`          : 0 success, 1 skipped/no loaded inputs,
                                    2 helper failure
  `sdai_transfer_origin_len`      : rewritten origin account RLP length
  `sdai_transfer_beneficiary_len` : rewritten beneficiary account RLP length
  `sdai_transfer_output`          : helper output buffer
-/
def selfdestructBalanceTransferRuntimeAsm : String :=
  "  la t0, sdai_transfer_status\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  la t0, sdai_transfer_origin_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, sdai_transfer_beneficiary_len\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, sdai_status\n" ++
  "  ld t1, 0(t0)\n" ++
  "  beqz t1, .L_selfdestruct_transfer_full\n" ++
  -- status 4 = beneficiary lookup missed because it is a NEW account. The balance
  -- move to the new beneficiary is already applied (recomputed state root matches),
  -- but the spec still emits the EIP-7708 Transfer log to it. The full transfer
  -- staging below needs the beneficiary RLP (absent for a new account), so instead
  -- just clear sdai_transfer_status to let selfdestructEip7708LogRuntimeAsm emit the
  -- log: it reads the transferred amount from the (valid) origin RLP and no-ops on a
  -- zero balance, so this is correct for both funded and empty new-beneficiary cases.
  -- status 1/2/3 (no context / header / origin failure) keep skipping (status stays 1).
  "  li t2, 4\n" ++
  "  bne t1, t2, .L_selfdestruct_transfer_done\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_transfer_done\n" ++
  ".L_selfdestruct_transfer_full:\n" ++
  "  la t0, sdai_origin_len\n" ++
  "  ld a1, 0(t0)\n" ++
  "  la t0, sdai_beneficiary_len\n" ++
  "  ld a3, 0(t0)\n" ++
  "  la t0, sdai_origin_address\n" ++
  "  la t1, evm_selfdestruct_beneficiary\n" ++
  "  li t2, 20\n" ++
  "  li t3, 1\n" ++
  ".L_selfdestruct_same_address_loop:\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  bne t4, t5, .L_selfdestruct_same_address_no\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_selfdestruct_same_address_loop\n" ++
  "  j .L_selfdestruct_same_address_done\n" ++
  ".L_selfdestruct_same_address_no:\n" ++
  "  li t3, 0\n" ++
  ".L_selfdestruct_same_address_done:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sdai_origin_rlp\n" ++
  "  la a2, sdai_beneficiary_rlp\n" ++
  "  mv a4, t3\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  ld a5, 0(t0)\n" ++
  "  la a6, sdai_transfer_output\n" ++
  "  jal ra, selfdestruct_balance_transfer\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_transfer_fail\n" ++
  "  la t0, sdai_transfer_output\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t2, sdai_transfer_origin_len\n" ++
  "  sd t1, 0(t2)\n" ++
  "  ld t1, 8(t0)\n" ++
  "  la t2, sdai_transfer_beneficiary_len\n" ++
  "  sd t1, 0(t2)\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_transfer_done\n" ++
  ".L_selfdestruct_transfer_fail:\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  li t1, 2\n" ++
  "  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_transfer_done:\n"

/--
Append the EIP-7708 synthetic Transfer log for a successful SELFDESTRUCT balance
transfer.

The runtime already has the pre-transfer origin account RLP, beneficiary,
same-address relation, and created-in-transaction marker. This mirrors
execution-specs `selfdestruct`: emit a Transfer only when beneficiary differs
from originator; zero balance and selfdestruct-to-self emit no log.

`evm_selfdestruct_log_status` records 0 success/no-log, 1 skipped because the
account-transfer stage did not run, 2 origin balance parse failure, 3 synthetic
log append failure. -/
def selfdestructEip7708LogRuntimeAsm : String :=
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  -- coc3g.6 CAUSE 1: a contract CREATEd-in-this-tx is absent from the block-pre witness, so the
  -- account-transfer stage never ran (sdai_transfer_status=3) and account_extract_balance(origin_rlp)
  -- would parse the wrong/empty RLP. EIP-7708 still requires the synthetic Transfer log when the
  -- live balance moves to a different beneficiary. Branch here: read the child's LIVE balance (its
  -- latest recorded non-storage post_balance, BE) via nonstorage_effect_latest_balance keyed on
  -- sdai_origin_address, bypassing the transfer-status gate. Runs BEFORE selfdestructBeneficiaryNonstorageAsm
  -- records the child's deletion (which resets the latest to 0), so the live balance is present.
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  ld t0, 0(t0)\n" ++
  "  bnez t0, .L_selfdestruct_eip7708_created\n" ++
  "  la t0, sdai_transfer_status\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .L_selfdestruct_eip7708_done\n" ++
  -- Prefer the live non-storage post-balance when this account already received/sent
  -- value in the current transaction; the block-pre account RLP is stale in that case.
  "  addi sp, sp, -96\n" ++
  "  sd x10, 64(sp)\n" ++
  "  sd x12, 72(sp)\n" ++
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  "  la t0, sdai_origin_address; mv t1, sp; li t2, 20\n" ++
  ".L_sd7708_live_key:\n" ++
  "  beqz t2, .L_sd7708_live_lookup\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sd7708_live_key\n" ++
  ".L_sd7708_live_lookup:\n" ++
  "  mv a0, sp\n" ++
  "  la a1, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  bnez a0, .L_sd7708_live_found\n" ++
  "  la a0, sdai_origin_rlp\n" ++
  "  la t0, sdai_origin_len\n" ++
  "  ld a1, 0(t0)\n" ++
  "  la a2, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 64(sp)\n" ++
  "  ld x12, 72(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  bnez t6, .L_selfdestruct_eip7708_balance_fail\n" ++
  "  j .L_selfdestruct_eip7708_have_balance\n" ++
  ".L_sd7708_live_found:\n" ++
  "  ld x10, 64(sp)\n" ++
  "  ld x12, 72(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  j .L_selfdestruct_eip7708_have_balance\n" ++
  ".L_selfdestruct_eip7708_created:\n" ++
  -- A same-tx-created SELFDESTRUCT moves the current child's live balance. Prefer the
  -- most-recent non-storage effect: this includes a non-zero CREATE endowment and any
  -- later value credit. A zero-endowment CREATE may nevertheless target a PRE-FUNDED
  -- address which is absent from the final BAL (the account is deleted at tx end), so
  -- its balance is not in the callee table and env+32 remains zero. On a live-log miss,
  -- read that authenticated block-pre balance from the header-state witness before the
  -- conservative env fallback. This matches Amsterdam selfdestruct's
  -- get_account(tx_state, current_target).balance at the transfer point.
  "  addi sp, sp, -160\n  sd x10, 144(sp)\n  sd x12, 152(sp)\n" ++
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  "  la t0, sdai_origin_address; mv t1, sp; li t2, 20\n" ++
  ".L_sd7708_created_key:\n" ++
  "  beqz t2, .L_sd7708_created_live\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sd7708_created_key\n" ++
  ".L_sd7708_created_live:\n" ++
  "  mv a0, sp; la a1, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  bnez a0, .L_sd7708_created_have_live\n" ++
  -- Account struct at sp+32: nonce@0, balance@8..40 BE, storage root, code hash.
  "  ld a0, 576(x20); ld a1, 584(x20); la a2, sdai_origin_address; li a3, 20\n" ++
  "  ld a4, 592(x20); ld a5, 600(x20); addi a6, sp, 32\n" ++
  "  jal ra, account_at_header_state_root_tracked\n" ++
  "  bnez a0, .L_sd7708_created_env\n" ++
  "  ld t0, 40(sp); la t1, evm_selfdestruct_balance_scratch; sd t0, 0(t1)\n" ++
  "  ld t0, 48(sp); sd t0, 8(t1); ld t0, 56(sp); sd t0, 16(t1); ld t0, 64(sp); sd t0, 24(t1)\n" ++
  "  j .L_sd7708_created_restore\n" ++
  ".L_sd7708_created_have_live:\n" ++
  "  j .L_sd7708_created_restore\n" ++
  ".L_sd7708_created_env:\n" ++
  -- The header lookup can legitimately miss for a freshly-created address; preserve
  -- the existing frame-local fallback for that case.
  "  la t0, evm_selfdestruct_balance_scratch; addi t1, x20, 63; li t2, 32\n" ++
  ".L_sd7708_envbal_rev:\n" ++
  "  lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_sd7708_envbal_rev\n" ++
  ".L_sd7708_created_restore:\n" ++
  "  ld x10, 144(sp); ld x12, 152(sp); addi sp, sp, 160\n" ++
  ".L_selfdestruct_eip7708_have_balance:\n" ++
  "  la t0, evm_selfdestruct_balance_scratch\n" ++
  "  addi t1, t0, 31\n" ++
  "  li t2, 16\n" ++
  ".L_selfdestruct_eip7708_balance_rev:\n" ++
  "  lbu t3, 0(t0)\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  sb t4, 0(t0)\n" ++
  "  sb t3, 0(t1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_selfdestruct_eip7708_balance_rev\n" ++
  -- Build stack-word LE forms of the from/to addresses for the EIP-7708 log topics.
  -- sdai_origin_address / evm_selfdestruct_beneficiary are canonical 20-byte BE, but
  -- the receipt log encoder byte-reverses each 32B topic slot (like the CALL value-
  -- transfer log, which passes env.ADDRESS / stack words), so the address must enter
  -- as [20-byte LE][12 zero] to come out canonical right-aligned BE.
  "  la t0, sd_eip7708_from_sw\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, sdai_origin_address; addi t1, t1, 19; li t2, 20\n" ++
  ".L_sd7708_from_le:\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_sd7708_from_le\n" ++
  "  la t0, sd_eip7708_to_sw\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, evm_selfdestruct_beneficiary; addi t1, t1, 19; li t2, 20\n" ++
  ".L_sd7708_to_le:\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_sd7708_to_le\n" ++
  "  la t0, sdai_origin_address\n" ++
  "  la t1, evm_selfdestruct_beneficiary\n" ++
  "  li t2, 20\n" ++
  "  li t3, 1\n" ++
  ".L_selfdestruct_eip7708_same_loop:\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  bne t4, t5, .L_selfdestruct_eip7708_not_same\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_selfdestruct_eip7708_same_loop\n" ++
  "  j .L_selfdestruct_eip7708_same_ready\n" ++
  ".L_selfdestruct_eip7708_not_same:\n" ++
  "  li t3, 0\n" ++
  ".L_selfdestruct_eip7708_same_ready:\n" ++
  "  bnez t3, .L_selfdestruct_eip7708_success\n" ++
  ".L_selfdestruct_eip7708_transfer:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, sd_eip7708_from_sw\n" ++
  "  la a1, sd_eip7708_to_sw\n" ++
  "  la a2, evm_selfdestruct_balance_scratch\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  mv t6, a0\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  bnez t6, .L_selfdestruct_eip7708_append_fail\n" ++
  ".L_selfdestruct_eip7708_success:\n" ++
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  sd x0, 0(t0)\n" ++
  "  j .L_selfdestruct_eip7708_done\n" ++
  ".L_selfdestruct_eip7708_balance_fail:\n" ++
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  li t1, 2\n" ++
  "  sd t1, 0(t0)\n" ++
  "  j .L_selfdestruct_eip7708_done\n" ++
  ".L_selfdestruct_eip7708_append_fail:\n" ++
  "  la t0, evm_selfdestruct_log_status\n" ++
  "  li t1, 3\n" ++
  "  sd t1, 0(t0)\n" ++
  ".L_selfdestruct_eip7708_done:\n"

/--
ednoc / i3djw.3: record the SELFDESTRUCT beneficiary's non-storage balance effect so the
all-accounts non-storage FORWARD check (`bal_all_accounts_nonstorage_consistent`, bv_fail=44)
reproduces the BAL's declared beneficiary balance change.

Hooks off `evm_selfdestruct_staged` (NOT `sdai_transfer_status==0`) so it also covers a NEW
beneficiary, whose account lookup fails (`sdai_status=4`) and skips the runtime transfer staging
-- yet the post-state recompute still creates it. transferred = origin pre-balance
(`sdai_origin_rlp`, BE, valid for status 0 or 4); beneficiary pre = its balance if it existed
(`sdai_status==0`) else 0; post = pre + transferred; nonce unchanged (0/0). Zero transfer or
self-destruct-to-self records nothing (the balance-0 self-destruct rows that pass via
conservative-accept stay unaffected). The all-accounts wrapper skips {sender,recipient,coinbase};
`record_nonstorage_effect`/`account_extract_balance`/`u256_add_be` are dispatcher-linked. Saves/
restores the dispatcher's x10/x12 around each helper call (mirrors the eip7708 fragment). -/
def selfdestructBeneficiaryNonstorageAsm : String :=
  "  la t0, evm_selfdestruct_staged; ld t0, 0(t0); beqz t0, .L_sdbn_done\n" ++
  -- A created-in-this-tx contract that SELFDESTRUCTs is cleared at transaction end (EIP-6780). The CREATE deposit
  -- recorded it (nonce 1, balance = endowment); record the clear with nonce 0 and the balance selected below.
  -- Pinned execution-specs v0.5.0 uses `clear_account_preserving_balance`, so self-destruct-to-self retains
  -- the live balance; a transfer to a different beneficiary leaves the origin balance at zero. The origin is NOT
  -- in the block-pre witness (created this tx), so the witness-present origin-debit path below skips it; this
  -- record fires on the created_in_tx flag regardless of sdai_status. sdai_origin_address = the
  -- selfdestructing contract's env ADDRESS (set from env, not the lookup), i.e. the created contract.
  -- Enables no new behavior (records the deletion that already happens) -> no cascade. a0/a2 alias x10/x12.
  "  la t0, evm_selfdestruct_created_in_tx; ld t0, 0(t0); beqz t0, .L_sdbn_chk_witness\n" ++
  -- Created-in-tx SELFDESTRUCT. The child's whole LIVE balance moves to a distinct beneficiary;
  -- self-transfer is a no-op. Two exec records are needed in the distinct-beneficiary case:
  --   (1) the child's clear (balance 0, nonce 0); and
  --   (2) the beneficiary's CREDIT (+ the child's live balance) so the BAL's +balance has a match
  --       (bv_fail=44 disc=2 NOTFOUND; selfdestruct_same_tx_via_call to_other).
  -- The child is absent from the block-pre witness, so its live balance = its LATEST recorded
  -- non-storage post_balance (the CREATE endowment + any CALL credit), read via
  -- nonstorage_effect_latest_balance before we append the child's clear record.
  -- transferred==0 or beneficiary==origin -> no beneficiary record. The
  -- beneficiary's pre = its latest live balance (other in-tx credits) if present, else its block-pre
  -- balance (account_at_header_state_root), else 0; post = pre + transferred; nonce unchanged.
  -- Stack frame (256B): sp+0 key(32B), sp+32 transferred(32B), sp+64 benef pre(32B),
  -- sp+96 benef post(32B), sp+128 account struct(104B), sp+240/248 = x10/x12 save. a0..a6 alias
  -- x10/x12/x13 -> saved/restored across the frame.
  "  addi sp, sp, -256\n  sd x10, 240(sp)\n  sd x12, 248(sp)\n" ++
  -- child addr key = sdai_origin_address (20B BE) + 12B zero -> sp+0
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  "  la t0, sdai_origin_address; addi t1, sp, 0; li t2, 20\n" ++
  ".L_sdbn_ctk:\n" ++
  "  beqz t2, .L_sdbn_ctk_d\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_ctk\n" ++
  ".L_sdbn_ctk_d:\n" ++
  -- transferred = child's latest live balance (sp+32); miss -> 0.
  "  sd zero, 32(sp); sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp)\n" ++
  "  mv a0, sp; addi a1, sp, 32\n" ++
  "  jal ra, account_state_latest_balance\n" ++   -- a0 = 1 found / 0 miss (out left 0 on miss)
  -- coc3g.6.2: a constructor-SELFDESTRUCT child has no recorded nonstorage effect (no RETURN deposit),
  -- so the latest-balance lookup misses; its live balance is env+32 (the endowment, LE), and x20 is the
  -- child env here. On a miss read env+32 (LE) -> sp+32 (BE) so `transferred` = the moved balance and
  -- the beneficiary credit below records the BAL's declared +balance (else bv_fail=44 NOTFOUND).
  "  bnez a0, .L_sdbn_ci_have_transferred\n" ++
  "  addi t0, sp, 32; addi t1, x20, 63; li t2, 32\n" ++
  ".L_sdbn_envbal_rev:\n" ++
  "  lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .L_sdbn_envbal_rev\n" ++
  ".L_sdbn_ci_have_transferred:\n" ++
  -- Build the child's post-clear balance. For a distinct beneficiary it is zero; for
  -- self-destruct-to-self it remains the live balance in sp+32, matching
  -- `clear_account_preserving_balance`.
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  "  sd zero, 224(sp); la t0, sdai_origin_address; la t1, evm_selfdestruct_beneficiary; li t2, 20\n" ++
  ".L_sdbn_clear_self_cmp:\n" ++
  "  beqz t2, .L_sdbn_clear_self\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L_sdbn_clear_distinct\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_clear_self_cmp\n" ++
  ".L_sdbn_clear_self:\n" ++
  -- Existing destroyed-table readers consume only the first 20 bytes.  Keep
  -- byte 20 as metadata so the BAL consumer can preserve self-transfer
  -- balance while suppressing stale CREATE fields for a distinct beneficiary.
  "  li t0, 1; sd t0, 224(sp)\n" ++
  "  addi a1, sp, 32; mv a2, a1; j .L_sdbn_record_clear\n" ++
  ".L_sdbn_clear_distinct:\n" ++
  -- A distinct beneficiary receives the child's full live balance, so the
  -- origin clear must publish transferred -> 0. `sp` is the zero scratch
  -- prepared above; `sp+32` is the child's transferred balance. Passing the
  -- same zero buffer for both operands suppresses the balance component and
  -- leaves the endowment as a phantom non-empty account after the deferred
  -- EIP-6780 clear.
  "  addi a1, sp, 32; mv a2, sp\n" ++
  ".L_sdbn_record_clear:\n" ++
  "  la a0, sdai_origin_address\n  li a3, 0\n  li a4, 0\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  -- Remember same-tx-created accounts queued for EIP-6780 clearing. Later CALLs use this table to
  -- suppress resurrected code and duplicate new-account gas; their credited balance remains intact.
  "  la t0, evm_selfdestruct_destroyed_count; ld t1, 0(t0)\n" ++
  "  li t2, " ++ toString selfdestructDestroyedAddressCap ++ "\n" ++
  "  bgeu t1, t2, .L_sdbn_destroyed_overflow\n" ++
  "  slli t2, t1, 5; la t3, evm_selfdestruct_destroyed_table; add t3, t3, t2\n" ++
  "  la t4, sdai_origin_address; li t5, 20\n" ++
  ".L_sdbn_destroyed_copy:\n" ++
  "  beqz t5, .L_sdbn_destroyed_copied\n" ++
  "  lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .L_sdbn_destroyed_copy\n" ++
  ".L_sdbn_destroyed_copied:\n" ++
  "  ld t5, 224(sp); sb t5, 0(t3)\n" ++
  "  addi t1, t1, 1; sd t1, 0(t0); j .L_sdbn_destroyed_done\n" ++
  ".L_sdbn_destroyed_overflow:\n" ++
  "  la t0, evm_selfdestruct_destroyed_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".L_sdbn_destroyed_done:\n" ++
  -- transferred != 0 ?  (sp+32..63 BE)
  "  ld t0, 32(sp); ld t1, 40(sp); or t0, t0, t1; ld t1, 48(sp); or t0, t0, t1; ld t1, 56(sp); or t0, t0, t1\n" ++
  "  beqz t0, .L_sdbn_ci_restore\n" ++
  -- beneficiary == origin (self) ? -> move_ether is a no-op, no beneficiary credit
  "  la t0, sdai_origin_address; la t1, evm_selfdestruct_beneficiary; li t2, 20\n" ++
  ".L_sdbn_ci_self:\n" ++
  "  beqz t2, .L_sdbn_ci_restore\n" ++                  -- all equal -> self -> no credit
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L_sdbn_ci_diff\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_ci_self\n" ++
  ".L_sdbn_ci_diff:\n" ++
  -- beneficiary pre balance (sp+64): latest live balance if present, else block-pre, else 0.
  "  sd zero, 64(sp); sd zero, 72(sp); sd zero, 80(sp); sd zero, 88(sp)\n" ++
  -- key = beneficiary (20B BE) + 12B zero -> sp+0 (transferred preserved at sp+32, benef pre at sp+64)
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  "  la t0, evm_selfdestruct_beneficiary; addi t1, sp, 0; li t2, 20\n" ++
  ".L_sdbn_ci_bk:\n" ++
  "  beqz t2, .L_sdbn_ci_bk_d\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_ci_bk\n" ++
  ".L_sdbn_ci_bk_d:\n" ++
  "  mv a0, sp; addi a1, sp, 64\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  bnez a0, .L_sdbn_ci_have_pre\n" ++                 -- found a live balance -> sp+64 has it
  -- no live record: look up block-pre balance via account_at_header_state_root(beneficiary).
  -- args: header_ptr=576(x20), header_len=584(x20), addr=evm_selfdestruct_beneficiary(20B),
  -- state_ptr=592(x20), state_len=600(x20), out=acct@sp+128 (nonce@0, balance@8..40). status!=0 -> pre 0.
  "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, evm_selfdestruct_beneficiary\n  li a3, 20\n  ld a4, 592(x20)\n  ld a5, 600(x20)\n  addi a6, sp, 128\n" ++
  "  jal ra, account_at_header_state_root_tracked\n" ++
  "  beqz a0, .L_sdbn_ci_pre_from_acct\n" ++
  "  sd zero, 64(sp); sd zero, 72(sp); sd zero, 80(sp); sd zero, 88(sp)\n" ++   -- not found -> pre 0
  "  j .L_sdbn_ci_have_pre\n" ++
  ".L_sdbn_ci_pre_from_acct:\n" ++
  -- acct.balance is at (sp+128)+8 = sp+136 (32B BE); copy into sp+64.
  "  ld t0, 136(sp); sd t0, 64(sp); ld t0, 144(sp); sd t0, 72(sp); ld t0, 152(sp); sd t0, 80(sp); ld t0, 160(sp); sd t0, 88(sp)\n" ++
  ".L_sdbn_ci_have_pre:\n" ++
  -- post = pre (sp+64) + transferred (sp+32) -> sp+96 (32B BE).
  "  addi a0, sp, 64\n  addi a1, sp, 32\n  addi a2, sp, 96\n" ++
  "  jal ra, u256_add_be\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n  addi a1, sp, 64\n  addi a2, sp, 96\n  li a3, 0\n  li a4, 0\n" ++  -- pre, post, nonce unchanged
  "  jal ra, record_nonstorage_effect\n" ++
  ".L_sdbn_ci_restore:\n" ++
  "  ld x10, 240(sp)\n  ld x12, 248(sp)\n  addi sp, sp, 256\n" ++
  "  j .L_sdbn_done\n" ++
  ".L_sdbn_chk_witness:\n" ++
  "  la t0, sdai_status; ld t0, 0(t0); beqz t0, .L_sdbn_origin_ok\n" ++
  "  li t1, 4; bne t0, t1, .L_sdbn_done\n" ++
  ".L_sdbn_origin_ok:\n" ++
  "  addi sp, sp, -144\n" ++
  "  sd x10, 128(sp); sd x12, 136(sp)\n" ++
  "  la a0, sdai_origin_rlp; la t0, sdai_origin_len; ld a1, 0(t0); addi a2, sp, 64\n" ++
  "  jal ra, account_extract_balance\n" ++
  -- The witness is block-pre state.  On a later transaction in the same block,
  -- a prior SELFDESTRUCT may already have recorded this origin's balance as
  -- zero; use that last committed effect before deciding whether there is a
  -- transfer.  Without this overlay, the stale witness balance is transferred
  -- a second time (selfdestruct_then_transfer_same_block).
  "  sd zero, 96(sp); sd zero, 104(sp); sd zero, 112(sp); sd zero, 120(sp)\n" ++
  "  la t0, sdai_origin_address; addi t1, sp, 96; li t2, 20\n" ++
  ".L_sdbn_origin_key:\n" ++
  "  beqz t2, .L_sdbn_origin_key_done\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_origin_key\n" ++
  ".L_sdbn_origin_key_done:\n" ++
  "  addi a0, sp, 96; addi a1, sp, 64\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  ld t0, 64(sp); ld t1, 72(sp); or t0, t0, t1; ld t1, 80(sp); or t0, t0, t1; ld t1, 88(sp); or t0, t0, t1\n" ++
  "  beqz t0, .L_sdbn_restore\n" ++
  "  la t0, sdai_origin_address; la t1, evm_selfdestruct_beneficiary; li t2, 20\n" ++
  ".L_sdbn_cmp:\n" ++
  "  beqz t2, .L_sdbn_restore\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .L_sdbn_diff\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_cmp\n" ++
  ".L_sdbn_diff:\n" ++
  "  la t0, sdai_status; ld t0, 0(t0); bnez t0, .L_sdbn_pre_zero\n" ++
  "  la a0, sdai_beneficiary_rlp; la t0, sdai_beneficiary_len; ld a1, 0(t0); mv a2, sp\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  j .L_sdbn_have_pre\n" ++
  ".L_sdbn_pre_zero:\n" ++
  "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
  ".L_sdbn_have_pre:\n" ++
  -- sr5m3.2: pre-existing SELFDESTRUCT can credit the same beneficiary multiple times
  -- in one transaction. Header/pre-witness balance is stale after the first credit, so
  -- prefer the latest non-storage post_balance for the beneficiary when present. This
  -- keeps the second SELFDESTRUCT credit's post balance at live_pre + origin_balance.
  -- Stack use: sp+0 beneficiary pre, sp+32 post, sp+64 origin balance, sp+96 key.
  "  sd zero, 96(sp); sd zero, 104(sp); sd zero, 112(sp); sd zero, 120(sp)\n" ++
  "  la t0, evm_selfdestruct_beneficiary; addi t1, sp, 96; li t2, 20\n" ++
  ".L_sdbn_live_bk:\n" ++
  "  beqz t2, .L_sdbn_live_bk_d\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .L_sdbn_live_bk\n" ++
  ".L_sdbn_live_bk_d:\n" ++
  "  addi a0, sp, 96; mv a1, sp\n" ++
  "  jal ra, account_state_latest_balance\n" ++
  "  mv a0, sp; addi a1, sp, 64; addi a2, sp, 32\n" ++
  "  jal ra, u256_add_be\n" ++
  "  la a0, evm_selfdestruct_beneficiary; mv a1, sp; addi a2, sp, 32; li a3, 0; li a4, 0\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  -- drj99.1 part 5c: record the ORIGIN's debit (balance -> 0, nonce preserved). SELFDESTRUCT moves the
  -- origin's whole balance to the (different) beneficiary, so the origin's final balance is 0; without a
  -- matching exec effect the BAL declares the origin's balance->0 with nothing to match -> bv_fail=44 (the
  -- selfdestruct_* families). We are inside the witness-present (sdai_status 0/4) + origin!=beneficiary +
  -- origin-balance!=0 path: the origin EXISTED at block-pre (created-in-THIS-tx accounts are absent from the
  -- block-pre witness and never reach here), so EIP-6780 does NOT delete it -> nonce is PRESERVED. pre_bal =
  -- origin balance (sp+64, extracted above); post_bal = 0 (sp+8..39); pre_nonce = post_nonce = origin nonce.
  -- sp+0..63 is free scratch now (beneficiary pre/post already consumed). x10/x12 stay saved at sp+96/104.
  "  la a0, sdai_origin_rlp; la t0, sdai_origin_len; ld a1, 0(t0); addi a2, sp, 0\n" ++   -- origin nonce -> sp+0
  "  jal ra, account_extract_nonce\n" ++
  "  sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp); sd zero, 32(sp)\n" ++             -- post_balance = 0 (sp+8..39)
  -- SELFDESTRUCT preserves the origin nonce, but a successful CREATE earlier
  -- in this transaction may already have advanced it.  Keep the witness nonce
  -- as the block-pre value and take the latest recorded nonce as the final.
  "  ld t0, 0(sp); sd t0, 40(sp)\n" ++
  "  la a0, sdai_origin_address; addi a1, sp, 40; jal ra, account_state_latest_nonce\n" ++
  "  ld a3, 0(sp); ld a4, 40(sp)\n" ++
  "  la a0, sdai_origin_address; addi a1, sp, 64; addi a2, sp, 8\n" ++                    -- a1 = pre_bal (origin), a2 = post_bal (0)
  "  jal ra, record_nonstorage_effect\n" ++
  ".L_sdbn_restore:\n" ++
  "  ld x10, 128(sp); ld x12, 136(sp); addi sp, sp, 144\n" ++
  ".L_sdbn_done:\n"

/--
Runtime-layout probe for `selfdestructLoadAccountInputsAsm`.

Input is the normal `scripts/pack-bytecode.py` runtime payload. The bytecode
segment is interpreted as a 20-byte SELFDESTRUCT beneficiary address; the
origin address comes from `evm_env`, matching the real runtime opcode path.

Output:
  bytes   0..  8 : load status
  bytes   8.. 16 : origin account RLP length
  bytes  16.. 24 : beneficiary account RLP length
  bytes  24.. 32 : decoded header state-root field length
  bytes  32.. 40 : transfer status
  bytes  40.. 48 : transfer origin result RLP length
  bytes  48.. 56 : transfer beneficiary result RLP length
  bytes  56.. 64 : EIP-7708 log status
  bytes  64..160 : origin account RLP bytes, zero-padded/truncated
  bytes 160..256 : beneficiary account RLP bytes, zero-padded/truncated
-/
def runtimeSelfdestructAccountInputsPrologue : String :=
  emitRuntimeDispatcherSetup ++ "\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, evm_selfdestruct_beneficiary\n" ++
  "  li t1, 20\n" ++
  "  mv t2, x21\n" ++
  ".L_rsda_copy_beneficiary:\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .L_rsda_copy_beneficiary\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd t3, 0(t0)\n" ++
  selfdestructLoadAccountInputsAsm ++
  selfdestructBalanceTransferRuntimeAsm ++
  selfdestructEip7708LogRuntimeAsm ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, sdai_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t1, sdai_origin_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  la t1, sdai_beneficiary_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  la t1, hesr_length\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 24(t0)\n" ++
  "  la t1, sdai_transfer_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 32(t0)\n" ++
  "  la t1, sdai_transfer_origin_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 40(t0)\n" ++
  "  la t1, sdai_transfer_beneficiary_len\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 48(t0)\n" ++
  "  la t1, evm_selfdestruct_log_status\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 56(t0)\n" ++
  "  la t1, sdai_transfer_output\n" ++
  "  ld t2, 0(t1)\n" ++
  "  addi t1, t1, 16\n" ++
  "  bnez t2, .L_rsda_use_transfer_origin\n" ++
  "  la t1, sdai_origin_rlp\n" ++
  ".L_rsda_use_transfer_origin:\n" ++
  "  addi t0, t0, 64\n" ++
  "  li t2, 96\n" ++
  ".L_rsda_copy_origin_rlp:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_rsda_copy_origin_rlp\n" ++
  "  la t1, sdai_transfer_output\n" ++
  "  ld t2, 8(t1)\n" ++
  "  addi t1, t1, 128\n" ++
  "  bnez t2, .L_rsda_use_transfer_beneficiary\n" ++
  "  la t1, sdai_beneficiary_rlp\n" ++
  ".L_rsda_use_transfer_beneficiary:\n" ++
  "  li t2, 96\n" ++
  ".L_rsda_copy_beneficiary_rlp:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_rsda_copy_beneficiary_rlp\n" ++
  "  j .L_rsda_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  -- cursor-walk helpers (account_extract_balance decodes via RlpWalk)
  rlpWalkHelpersClosure ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  eip7708SyntheticLogFunctions ++ "\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  j .L_rsda_done\n" ++
  ".L_rsda_done:"

/-- Minimal `.data` section for the SELFDESTRUCT account-input probe. -/
def runtimeSelfdestructAccountInputsDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 624\n" ++
  ".balign 8\n" ++
  "evm_blob_hashes:\n" ++
  "  .zero 512\n" ++
  ".balign 8\n" ++
  "evm_block_hashes:\n" ++
  "  .zero 8192\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 262144\n" ++   -- 6c7v9: 1024 × 256-byte LOG event descriptors (was 4096 = 16×256)
  eip7708SyntheticLogTopicData ++
  emitPrecompileFrameData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  emitRuntimeAccountWitnessData ++
  ".balign 8\n" ++
  runtimeAccessAccountCountLabel ++ ":\n" ++
  "  .zero 8\n" ++
  ".balign 32\n" ++
  runtimeAccessAccountTableLabel ++ ":\n" ++
  "  .zero " ++ toString (runtimeAccessAccountCapacity * runtimeAccessAccountRecordSize) ++ "\n" ++
  runtimeAccessSeedScratchLabel ++ ":\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_beneficiary:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "evm_selfdestruct_balance_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sd_eip7708_from_sw:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "sd_eip7708_to_sw:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_created_in_tx:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_log_status:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "evm_selfdestruct_staged:\n" ++
  "  .zero 8\n" ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++
  "lp64_sp_top:\n"

def runtimeSelfdestructAccountInputsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeSelfdestructAccountInputsPrologue
  dataAsm     := runtimeSelfdestructAccountInputsDataSection
}

/-- Runtime-layout probe for SELFDESTRUCT EIP-7708 log bridging.

Input matches `runtime_selfdestruct_account_inputs`; output is the first
256-byte captured log descriptor, or all zeros when no log is emitted. -/
def runtimeSelfdestructEip7708LogsPrologue : String :=
  emitRuntimeDispatcherSetup ++ "\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd x0, 0(t0)\n" ++
  "  la t0, evm_event_logs\n" ++
  "  li t1, 512\n" ++
  ".L_rsdl_zero_logs:\n" ++
  "  sd x0, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .L_rsdl_zero_logs\n" ++
  "  sd x0, 472(x20)\n" ++
  "  la t0, evm_selfdestruct_beneficiary\n" ++
  "  li t1, 20\n" ++
  "  mv t2, x21\n" ++
  ".L_rsdl_copy_beneficiary:\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  sb t3, 0(t0)\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .L_rsdl_copy_beneficiary\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n" ++
  "  sd t3, 0(t0)\n" ++
  selfdestructLoadAccountInputsAsm ++
  selfdestructBalanceTransferRuntimeAsm ++
  selfdestructEip7708LogRuntimeAsm ++
  "  li t0, 0xa0010000\n" ++
  "  la t1, evm_event_logs\n" ++
  "  li t2, 32\n" ++
  ".L_rsdl_copy_desc:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .L_rsdl_copy_desc\n" ++
  "  j .L_rsdl_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  -- cursor-walk helpers (account_extract_balance decodes via RlpWalk)
  rlpWalkHelpersClosure ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  eip7708SyntheticLogFunctions ++ "\n" ++
  runtimeAccessAccountSeedFunction ++ "\n" ++
  runtimeAccessSeedInitialAccountsFunction ++ "\n" ++
  ".exit_outofgas:\n" ++
  "  j .L_rsdl_done\n" ++
  ".L_rsdl_done:"

def runtimeSelfdestructEip7708LogsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeSelfdestructEip7708LogsPrologue
  dataAsm     := runtimeSelfdestructAccountInputsDataSection
}

end EvmAsm.Codegen
