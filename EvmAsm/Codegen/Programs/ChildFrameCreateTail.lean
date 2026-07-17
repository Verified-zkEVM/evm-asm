/-
  EvmAsm.Codegen.Programs.ChildFrameCreateTail

  CREATE-family child-frame tail builder, split out of
  `ChildFrameHandlerTails.lean` to keep Codegen/Programs files under the
  FileSizeGuard cap.
-/

import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.CreateRuntime
import EvmAsm.Codegen.Programs.CreateSameTxCollision
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Rv64.Program
namespace EvmAsm.Codegen
open EvmAsm.Rv64

def createUnsupportedTail (netPopBytes : Nat) (hasSalt : Bool) : String :=
    -- Decode CREATE-family operands, derive the would-be target address using
    -- the shared CREATE/CREATE2 address helpers, and enforce the currently
    -- runtime-visible prechecks before later child/deposit execution slices.
    "  la x15, evm_precompile_frame\n" ++
    "  sd x0, 0(x15)\n" ++
    "  sd x0, 8(x15)\n" ++
    "  ld x14, 0(x12)\n" ++    -- value low limb
    "  ld x15, 32(x12)\n" ++   -- offset low limb
    "  ld x16, 64(x12)\n" ++   -- size low limb
    "  la x18, create_init_offset\n" ++
    "  sd x15, 0(x18)\n" ++
    "  la x18, create_init_size\n" ++
    "  sd x16, 0(x18)\n" ++
    (if hasSalt then
      "  ld x17, 96(x12)\n"   -- salt low limb; full salt is converted below
     else
      "") ++
    -- A nonzero high limb in size is outside the current static memory
    -- envelope. Offset high limbs matter only for nonempty initcode.
    "  ld x18, 72(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 80(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 88(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    -- fhsxz.2.4.2.61.8.3.6 / EIP-3860 + EIP-7907: init-code size > MAX_INIT_CODE_SIZE is an
    -- exceptional abort consuming all gas (execution-specs amsterdam system.py:85-86 raises
    -- OutOfGasError; MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE = 2 * 0x10000 = 0x20000 = 131072, per
    -- vm/interpreter.py — EIP-7907 doubled MAX_CODE_SIZE 0x6000->0x10000, so the bound is 131072,
    -- NOT the pre-Amsterdam 49152: init-code in (49152, 131072] is VALID and must execute, not
    -- be rejected). x16 is the full size (high limbs confirmed 0 above). The bound equals
    -- create_child_initcode's size (.zero 0x20000 = 131072), so a valid init-code (<= 131072) fits
    -- the staging buffer exactly while any larger (invalid) one is OOG-rejected before the copy,
    -- preventing the overflow into adjacent .data (create_child_returndata / create_child_code).
    "  li x18, 131072; bgtu x16, x18, .exit_outofgas\n" ++
    "  beqz x16, 1f\n" ++
    "  ld x18, 40(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 48(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  ld x18, 56(x12)\n" ++
    "  bnez x18, .exit_outofgas\n" ++
    "  add x18, x15, x16\n" ++
    "  bltu x18, x15, .exit_outofgas\n" ++
    "  li x19, 0x20000\n" ++
    "  bltu x19, x18, .exit_outofgas\n" ++
    "1:\n" ++
    createInitcodeGasAsm
      (if hasSalt then "create2" else "create")
      "x16" "x18" "x19" "x23" hasSalt ++
    updateActiveMemorySizeAsm
      (if hasSalt then "create2_init" else "create_init")
      "x15" "x16" "x18" "x19" "x23" "x6" true ++
    -- The dispatcher precharge already includes Amsterdam execution-specs'
    -- CREATE_ACCESS = ACCOUNT_WRITE(8000) + COLD_STORAGE_ACCESS(3000).
    -- Do not debit an additional cold-access delta here; generic_create's
    -- insufficient-balance branch refunds only child-call/state reservoirs, not
    -- any duplicate pre-execution CREATE_ACCESS charge.
    -- Convert env.ADDRESS from stack-word representation to the canonical
    -- 20-byte big-endian input expected by address_compute_create*.
    "  la x18, create_sender_be\n" ++
    "  addi x19, x20, 19\n" ++
    "  li x23, 20\n" ++
    "2:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x18)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 2b\n" ++
    -- v0.6.0 (C11): the NEW_ACCOUNT charge is CONDITIONAL (target not
    -- alive) and moves to the gated site below (after address
    -- derivation); the v0.5.0 unconditional pay-before-execute abort is
    -- gone -- an alive target charges nothing and cannot OOG here.
    "  la t1, create_state_gas_charged_current\n  sd x0, 0(t1)\n" ++
    -- With account-witness context, enforce the executable-spec
    -- insufficient-balance zero-result branch before deriving success.
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 9f\n" ++
    "  la x18, create_value_be\n" ++
    "  addi x19, x12, 31\n" ++
    "  li x23, 32\n" ++
    "10:\n" ++
    "  lbu x24, 0(x19)\n" ++
    "  sb x24, 0(x18)\n" ++
    "  addi x19, x19, -1\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 10b\n" ++
    -- coc3g.6 / coc3g.7: value-sufficiency gate uses the creator's LIVE balance, NOT the
    -- witness pre-state balance. The spec's generic_create checks
    -- `get_account(tx_state, sender).balance < endowment` against the LIVE mutable tx state
    -- (amsterdam vm/instructions/system.py:108-119), and the endowment DEBIT below
    -- (.Lcr_deb_done, lines ~256-276) already debits the LIVE balance env+32 (.selfBalance).
    -- The previous gate compared the witness pre-state balance (balance_at_header_state_root)
    -- against the endowment, which falsely bailed when the creator is funded THIS tx (e.g. the
    -- tx.to recipient does CREATE(value): witness balance = 0 but live balance = pre + tx.value).
    -- That false bail skipped the entire CREATE descend, so a failing initcode (OOG / invalid
    -- opcode) never burned its child-frame gas allotment -> parent gas_used under-charged
    -- (create_out_of_gas: recomputed 30111 vs spec 311927, bv_fail=41).
    -- env+32 (.selfBalance) is LITTLE-ENDIAN (byte 0 = LSB); reverse env[32..63] -> create_balance_be
    -- (BE, byte 31 = LSB) so the byte-wise compare below (BE vs create_value_be BE) is correct.
    "  addi x18, x20, 63\n" ++
    "  la x19, create_balance_be\n" ++
    "  li x23, 32\n" ++
    "12:\n" ++
    "  lbu x24, 0(x18)\n" ++
    "  sb x24, 0(x19)\n" ++
    "  addi x18, x18, -1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 12b\n" ++
    "  la x18, create_balance_be\n" ++
    "  la x19, create_value_be\n" ++
    "  li x23, 32\n" ++
    "11:\n" ++
    "  lbu x24, 0(x18)\n" ++
    "  lbu x25, 0(x19)\n" ++
    "  bltu x24, x25, 7f\n" ++
    "  bltu x25, x24, 9f\n" ++
    "  addi x18, x18, 1\n" ++
    "  addi x19, x19, 1\n" ++
    "  addi x23, x23, -1\n" ++
    "  bnez x23, 11b\n" ++
    "9:\n" ++
    -- Default to nonce 0 when no account-witness context is attached.
    "  la x18, create_nonce\n" ++
    "  sd x0, 0(x18)\n" ++
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 3f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  la a2, create_sender_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  la a5, create_nonce\n" ++
    "  jal x1, nonce_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    "  beqz t0, 3f\n" ++
    "  la x18, create_nonce\n" ++
    "  sd x0, 0(x18)\n" ++
    "3:\n" ++
    "  la x18, create_nonce\n" ++
    "  ld x18, 0(x18)\n" ++
    "  li x19, -1\n" ++
    "  beq x18, x19, 7f\n" ++
    -- bmvmx.5.5.10: cross-tx CREATE-nonce threading (sequential mtx lane).
    -- create_creator_nonce_table resets PER TX (.61.8a) and the witness seed
    -- above reads the PRE-state nonce, so a contract that CREATEs in tx i and
    -- again in tx j would re-derive with the stale pre-state nonce. The
    -- non-storage effect log records every creator bump (drj99.1 5a) and
    -- created-account record (post_nonce=1) and persists across txs
    -- (truncated only for FAILED txs, whose nonce bumps revert). Consult it:
    -- hit -> override the seed with the latest post_nonce; miss -> witness
    -- seed (today's behavior). Same case analysis as the SELFBALANCE live
    -- overlay (DispatchTx:769-789). Must run BEFORE create_creator_nonce_use
    -- (it reads create_nonce for the seed-and-bump on table miss).
    "  sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
    "  la a0, create_sender_be; la a1, create_nonce_latest\n" ++
    "  jal ra, nonstorage_effect_latest_nonce\n" ++
    "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp)\n" ++
    "  beqz a0, 13f\n" ++
    "  la x19, create_nonce_latest; ld x18, 0(x19)\n" ++
    "  la x19, create_nonce; sd x18, 0(x19)\n" ++
    "13:\n" ++
    -- .61.8c-1: replace the bare pre-state nonce with the per-creator RUNNING nonce, so a SECOND
    -- CREATE by the same creator in this tx uses a distinct nonce (-> distinct address) -- the EVM
    -- increments the creator's nonce on each CREATE/CREATE2. x18 holds the witness pre-state nonce;
    -- create_creator_nonce_use seeds the per-creator table with it on the first CREATE and returns the
    -- running value (advancing the table; both CREATE and CREATE2 bump it). a0==x10 (the dispatcher
    -- PC) is clobbered by the call, so save/restore x10; the result (a0) is stored to create_nonce
    -- BEFORE restoring x10 (the #8608 lesson). create_creator_nonce_use preserves x12/x13/x20/x21.
    "  mv s10, x10\n" ++
    "  la a0, create_sender_be\n" ++
    "  mv a1, x18\n" ++
    "  jal x1, create_creator_nonce_use\n" ++
    "  la x18, create_nonce\n" ++
    "  sd a0, 0(x18)\n" ++
    "  mv x10, s10\n" ++
    "  la x18, create_nonce; ld x19, 0(x18); li x18, -1; beq x19, x18, 7f\n" ++
    (if hasSalt then
      -- Convert the CREATE2 salt stack word to canonical 32-byte big-endian.
      "  la x18, create_salt_be\n" ++
      "  addi x19, x12, 127\n" ++
      "  li x23, 32\n" ++
      "4:\n" ++
      "  lbu x24, 0(x19)\n" ++
      "  sb x24, 0(x18)\n" ++
      "  addi x19, x19, -1\n" ++
      "  addi x18, x18, 1\n" ++
      "  addi x23, x23, -1\n" ++
      "  bnez x23, 4b\n" ++
      "  mv s9, x13\n" ++
      "  mv s10, x10\n" ++
      "  mv s11, x12\n" ++
      "  la a0, create_sender_be\n" ++
      "  la a1, create_salt_be\n" ++
      "  ld a2, create_init_offset\n" ++
      "  add a2, x13, a2\n" ++
      "  ld a3, create_init_size\n" ++
      "  la a4, create_address_be\n" ++
      "  jal x1, address_compute_create2\n" ++
      "  mv x13, s9\n" ++
      "  mv x10, s10\n" ++
      "  mv x12, s11\n"
     else
      "  mv s9, x13\n" ++
      "  mv s10, x10\n" ++
      "  mv s11, x12\n" ++
      "  la a0, create_sender_be\n" ++
      "  ld a1, create_nonce\n" ++
      "  la a2, create_address_be\n" ++
      "  jal x1, address_compute_create\n" ++
      "  mv x13, s9\n" ++
      "  mv x10, s10\n" ++
      "  mv x12, s11\n") ++
    -- If an account-witness context is attached, apply the EIP-684
    -- code-or-nonce collision check to the derived target address.
    "  ld a1, 584(x20)\n" ++
    "  beqz a1, 6f\n" ++
    "  mv s9, x13\n" ++
    "  mv s10, x10\n" ++
    "  mv s11, x12\n" ++
    "  ld a0, 576(x20)\n" ++
    "  la a2, create_address_be\n" ++
    "  ld a3, 592(x20)\n" ++
    "  ld a4, 600(x20)\n" ++
    "  jal x1, has_code_or_nonce_at_header_state_root\n" ++
    "  mv t0, a0\n" ++
    "  mv x13, s9\n" ++
    "  mv x10, s10\n" ++
    "  mv x12, s11\n" ++
    -- A nonzero helper status means the header-state witness lookup could not
    -- classify the derived address. Execution-specs has the live tx state here;
    -- for a missing/unknown header account the closest faithful behavior is to
    -- treat the header predicate as false (the helper initializes it to 0),
    -- still run the same-tx collision scan below, and otherwise take the normal
    -- CREATE descend path. A cheap push-0 skipped child execution gas.
    "  la x18, hcon_predicate\n" ++
    "  ld x18, 0(x18)\n" ++
    "  bnez x18, .Lcr_collision_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    createSameTxCollisionScanAsm hasSalt ++
    "6:\n" ++
    -- coc3g.6 CAUSE 2: mirror spec generic_create (amsterdam vm/instructions/system.py:122
    -- `evm.accessed_addresses.add(contract_address)`). On the committing CREATE path the derived
    -- contract address is WARM for the rest of the tx, so a later CALL/SELFDESTRUCT to it pays the
    -- WARM floor (100), not COLD_ACCOUNT_ACCESS (3000). Without this, a same-tx value-CALL to the
    -- just-created child charged the 2500 cold delta (verified: selfdestruct_same_tx_via_call
    -- to_other receipt cumulativeGasUsed over-counted by exactly 2500 -> bv_fail=53). The warm
    -- table is a single global (evm_access_account_table, capacity 100000, reset only at tx setup),
    -- so the seed persists across create_frame_descend into the parent's subsequent CALL.
    -- runtime_access_account_seed inserts WITHOUT charging gas and ignores duplicates; it clobbers
    -- the a-regs that alias x10/x12/x13, so save/restore them. create_address_be is the canonical
    -- 20-byte BE address (a0 expects exactly that).
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, create_address_be\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_seed\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    -- 5em02.2: debit the creator's LIVE balance (env+32 = .selfBalance, big-endian) by the
    -- endowment, so SELFBALANCE reads B-endowment after a CREATE (the transfer was inert ->
    -- false-reject for value-creating contracts). Reached only on the committing path (value
    -- gate passed, no address collision). ctx-gated (create_value_be valid, populated BE by
    -- the gate above) + borrow-guarded (the gate checked PRE-state balance; the live env+32 may
    -- be lower from an earlier same-frame value-op -> conservative skip on underflow). Same
    -- single-tx failure-rollback caveat as 5em02.1 (a CREATE that later reverts is not undone
    -- here). The created account's env+32 credit (init-code SELFBALANCE) is a follow-up.
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_deb_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    -- env+32 (.selfBalance) is LITTLE-ENDIAN (byte 0 = LSB), same convention as CALLVALUE@96;
    -- u256_sub_be is big-endian (byte 31 = LSB). The prior code fed env+32 STRAIGHT to u256_sub_be
    -- -> byte-scrambled selfBalance debit (drj99.1 part 4). Reverse env[32..63] (LE) ->
    -- create_creator_newbal (BE), subtract in place (a0==a2 byte-safe), reverse the result back.
    "  addi t0, x20, 63\n  la t1, create_creator_newbal\n  li t2, 32\n" ++
    ".Lcr_sbrev_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .Lcr_sbrev_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  la a0, create_creator_newbal\n" ++               -- a0 = creator LIVE balance, now BE
    "  la a1, create_value_be\n" ++                      -- a1 = endowment (BE)
    "  la a2, create_creator_newbal\n" ++                -- a2 = out (in place = balance - endowment, BE)
    "  jal ra, u256_sub_be\n" ++
    "  mv t0, a0\n" ++                                   -- t0 = borrow flag (before x10=a0 restore)
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t0, .Lcr_deb_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++   -- underflow -> skip
    -- reverse create_creator_newbal (BE) back into env+32 (LE)
    "  la t0, create_creator_newbal\n  addi t1, x20, 63\n  li t2, 32\n" ++
    ".Lcr_sbwb_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, 1\n  addi t1, t1, -1\n  addi t2, t2, -1\n  bnez t2, .Lcr_sbwb_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    ".Lcr_deb_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    -- bbow4.2.5.1: a zero-endowment CREATE still increments the creator's
    -- nonce even when the child later REVERTs / exceptionally halts. The
    -- deposit-time creator record only runs on successful CREATE, and records
    -- appended after create_frame_descend are rolled back by frame_return on
    -- child failure. Emit the zero-value nonce-only effect in the parent before
    -- descent so the all-accounts non-storage check can match the BAL.
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_creator_nonce_effect_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  la t0, create_value_be\n  ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
    "  bnez t1, .Lcr_creator_nonce_effect_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  la t0, nse_create_pre_bal\n  addi t1, x20, 63\n  li t2, 32\n" ++
    ".Lcr_creator_nonce_bal_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .Lcr_creator_nonce_bal_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la t0, create_nonce\n  ld a3, 0(t0)\n  addi a4, a3, 1\n" ++
    "  la a0, create_sender_be\n  la a1, nse_create_pre_bal\n  la a2, nse_create_pre_bal\n" ++
    "  jal ra, record_nonstorage_effect\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    ".Lcr_creator_nonce_effect_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    createStageInitcodeFrameCallAsm (if hasSalt then 1 else 0) ++
    -- .61.8.3.5.3 (.5c): execute the staged init code in a REAL child frame via the full
    -- dispatch loop (create_frame_descend, .5a, reusing call_frame_descend), REPLACING the
    -- bounded mini-interpreter (create_execute_initcode_frame: STOP/MSTORE/MSTORE8/PUSH/RETURN/
    -- REVERT/INVALID only). The child now runs the full opcode set (SSTORE/arithmetic/CODECOPY/
    -- JUMP/...), so real constructors execute. On the child's RETURN the depth-aware
    -- returnRevertTail CREATE branch (.5b) validity-gates + deposits the returned bytes as the
    -- deployed code + pushes the DERIVED ADDRESS back to this frame (0 on invalid deploy / REVERT).
    -- create_frame_descend reads the endowment from x12 (stack top) itself; do NOT pass it in
    -- a0 (== x10 the PC) -- that would clobber the parent return PC the descent saves (#8608).
    -- a1 = netPopBytes (frame_return pops the CREATE args: 64 for CREATE / 96 for CREATE2).
    -- nxio8.8: charge create_account_state_gas = STATE_BYTES_PER_NEW_ACCOUNT(120)*COST_PER_STATE_BYTE(1530)
    -- = 183600 (spec amsterdam vm/instructions/system.py:89, pay-before-execute, BEFORE the init child).
    -- Mirror charge_state_gas (Storage.lean): drain evm_state_gas_left; spill the remainder into the
    -- PARENT gas_left (568(x20), still the parent env here, before the descend); OOG-fail the CREATE
    -- (push 0 via 7f) when both reservoirs are short. evm_state_gas_used += charge. Preserves the
    -- dispatcher state x10/x12/x13/x20/x21 (only t0-t3 + the parent gas_left). The charge is REFUNDED
    -- on child failure by the snapshot rewrite after create_frame_descend below. The descent snapshots
    -- POST-charge into child_env+624/632, so we preserve the pre-charge reservoir and subtract 183600
    -- from the used snapshot; incorporate_child_on_error then restores the exact pre-charge state and
    -- frame_return can also restore any regular-gas spill.
    -- v0.6.0 (C11): charge iff the target is NOT alive (balance == 0 and
    -- no prior same-tx creation; code/nonce holders took the collision
    -- branch). Computed here -- the debit staging above populated
    -- nse_create_pre_bal -- and recorded in create_target_alive_current_tx
    -- for the by-depth snapshot below. Ctx-gated: without the
    -- account-witness context aliveness is unknown and the charge stays
    -- unconditional (alive := 0).
    "  la t0, create_target_alive_current_tx\n  sd x0, 0(t0)\n" ++
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_alive_known_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    -- spec is_account_alive(target): the TARGET's header-state balance
    -- (code/nonce holders already took the collision branch) plus any
    -- prior same-tx creation effect.
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  ld a0, 576(x20)\n  ld a1, 584(x20)\n  la a2, create_address_be\n  ld a3, 592(x20)\n  ld a4, 600(x20)\n  la a5, cr_alive_bal\n" ++
    "  jal ra, balance_at_header_state_root\n" ++
    "  mv t2, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  bnez t2, .Lcr_alive_known_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  la t0, cr_alive_bal\n" ++
    "  ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
    "  bnez t1, .Lcr_alive_set_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, exec_code_effect_log\n  la t0, exec_code_effect_count\n  ld a1, 0(t0)\n  la a2, create_address_be\n" ++
    "  jal ra, find_code_effect_by_address\n" ++
    "  mv t1, a0\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  beqz t1, .Lcr_alive_known_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    ".Lcr_alive_set_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  la t0, create_target_alive_current_tx\n  li t1, 1\n  sd t1, 0(t0)\n" ++
    ".Lcr_alive_known_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  la t0, create_target_alive_current_tx\n  ld t0, 0(t0)\n" ++
    "  bnez t0, .Lcr_csg_skip_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    liStateGasRuntime "t0" amsterdamStateBytesPerNewAccountV2 ++   -- create_account state gas = 120 * 1530 = 183600
    "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n  mv t4, t2\n" ++
    "  bgeu t2, t0, .Lcr_csg_res_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    -- v0.6.0: charge_state_gas OOG is an exceptional halt burning all
    -- regular gas (was a cheap push-0).
    "  sub t3, t0, t2\n  ld t2, 568(x20)\n  bltu t2, t3, .exit_outofgas\n  sd x0, 0(t1)\n" ++
    "  sub t2, t2, t3\n  sd t2, 568(x20)\n" ++
    "  la t1, evm_state_gas_spilled\n  ld t2, 0(t1)\n  add t2, t2, t3\n  sd t2, 0(t1)\n" ++
    "  j .Lcr_csg_used_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    ".Lcr_csg_res_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++
    ".Lcr_csg_used_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
    "  la t1, create_state_gas_charged_current\n  li t2, 1\n  sd t2, 0(t1)\n" ++
    ".Lcr_csg_skip_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    -- CREATE uses the same call-frame arena as CALL. Mirror CALL's depth gate before
    -- create_frame_descend so recursive constructors at depth 1024 push zero instead of
    -- attempting to enter a non-protocol child frame.
    "  la t1, evm_call_depth\n  ld t2, 0(t1)\n  li t3, 1024\n  bgeu t2, t3, 7f\n" ++
    "  li a1, " ++ toString netPopBytes ++ "\n" ++
    "  jal x1, create_frame_descend\n" ++
    -- coc3g.9.3.4: the descent snapshotted state-gas POST-charge into child_env+624/632.
    -- We do NOT rewrite the snapshot to PRE-charge values. Previously the rewrite made
    -- frame_return compute used_delta = full CREATE charge (183600), inflating s7 (child
    -- leftover gas) by 183600 → gas_left got the CREATE spill back via EIP-150 (double
    -- refund: gas_left AND state_gas_left). With POST-charge values, used_delta excludes
    -- the CREATE charge (s7 not inflated). The failed-create credit paths (NoopHalt
    -- REVERT/invalid-deposit, Dispatch exceptional exits) credit 183600 back on child
    -- failure IFF the conditional charge above actually fired (target not alive,
    -- create_target_alive_flag[depth] == 0; evm-asm-0w05f.17.2), matching
    -- execution-specs `if new_account_charged: credit_state_gas_refund`.

    -- drj99.1 part 2: credit child C's env+32 selfBalance with the endowment so the initcode's
    -- SELFBALANCE and its outgoing value-CALL debits operate on the real balance. call_frame_descend
    -- step 8c staged env+32 = C's PRE-state balance (0 for a fresh address; non-zero only if the
    -- address was pre-funded), so add the endowment on top = the EVM "new account balance". x20 = the
    -- CHILD env (switched by the descend). env+32 is LE; reverse to BE, u256_add_be the BE endowment
    -- (create_value_be, still valid — the initcode has not run yet), reverse back. create_creator_newbal
    -- is the BE scratch (free after the gate's creator-debit). a0-a2 alias x10/x12/x13 -> save/restore.
    -- drj99.1 (initcode_calls_with_value bv_fail=44): FIRST capture the child's staged PRE-state
    -- balance (env+32 BEFORE the endowment credit, = block-pre balance: 0 for a fresh address) into
    -- nse_create_pre_bal (BE), so the created-account endowment-credit nonstorage record below carries
    -- the spec-correct pre_balance. env+32 is LE -> reverse to BE. nse_create_pre_bal is free here.
    "  la t0, nse_create_pre_bal\n  addi t1, x20, 63\n  li t2, 32\n" ++
    ".Lcr_prebal_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .Lcr_prebal_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    -- v0.6.0 (C11): target_alive was computed at the charge site above;
    -- persist it into the by-depth slot for the RETURN-path snapshot.
    "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
    "  la t0, create_target_alive_flag; slli t1, t1, 3; add t0, t0, t1\n" ++
    "  la t2, create_target_alive_current_tx; ld t2, 0(t2); sd t2, 0(t0)\n" ++
    "  addi t0, x20, 63\n  la t1, create_creator_newbal\n  li t2, 32\n" ++
    ".Lcr_sbc_rev_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .Lcr_sbc_rev_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, create_creator_newbal\n  la a1, create_value_be\n  la a2, create_creator_newbal\n" ++
    "  jal ra, u256_add_be\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  la t0, create_creator_newbal\n  addi t1, x20, 63\n  li t2, 32\n" ++
    ".Lcr_sbc_wb_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, 1\n  addi t1, t1, -1\n  addi t2, t2, -1\n  bnez t2, .Lcr_sbc_wb_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    -- coc3g.6 CAUSE 3: EIP-7708 transfer log for the CREATE endowment value move. Spec
    -- interpreter.py:307-316 emits Transfer(caller, current_target, value) at EVERY message-call
    -- frame entry with should_transfer_value and value!=0 and caller!=current_target, AFTER the
    -- tx-state snapshot and BEFORE the initcode runs. The CREATE child frame moves `endowment` from
    -- the creator (caller) to the created child (current_target). Without it, the
    -- selfdestruct_same_tx_via_call transfer_during_create / create_opcode_emits_log receipts were
    -- missing this log -> bv_fail=53 receipts-root mismatch. Emitted HERE -- after create_frame_descend
    -- switched x20 to the CHILD env (post-snapshot: descend set the child eventLogCheckpoint@480 to
    -- the current count) and BEFORE `j .dispatch_loop` runs the initcode -- so the log (a) lands in
    -- the correct order (before any initcode logs) and (b) is ROLLED BACK by frame_return when the
    -- child reverts/fails (failed_create_with_value_no_log expects NO log). caller != child always
    -- (a freshly-derived address), so the only guard is value!=0. The appender reads from=topic1 (a0,
    -- stack-word LE), to=topic2 (a1, stack-word LE), amount (a2, stack-word LE -> reversed to BE).
    -- The create_sender_be/create_address_be (canonical 20B BE) + create_value_be (32B BE) globals are
    -- still valid (descend doesn't clobber them; the initcode hasn't run). Gated on the account-witness
    -- ctx (env+584) so create_value_be is the valid endowment the gate populated. Stack frame (96B):
    -- sp+0 from_sw(32), sp+32 to_sw(32), sp+64 val_sw(32 partial)/x10/x12/x13 -- use a 128B frame.
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_tl_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  la t0, create_value_be\n  ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
    "  beqz t1, .Lcr_tl_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++   -- value == 0: no log
    "  addi sp, sp, -128\n  sd x10, 96(sp)\n  sd x12, 104(sp)\n  sd x13, 112(sp)\n" ++
    -- from_sw = [reverse(create_sender_be) low 20][12 zero] (sp+0)
    "  sd zero, 0(sp); sd zero, 8(sp); sd zero, 16(sp); sd zero, 24(sp)\n" ++
    "  la t0, create_sender_be; addi t0, t0, 19; addi t1, sp, 0; li t2, 20\n" ++
    ".Lcr_tl_from_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lcr_tl_from_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    -- to_sw = [reverse(create_address_be) low 20][12 zero] (sp+32)
    "  sd zero, 32(sp); sd zero, 40(sp); sd zero, 48(sp); sd zero, 56(sp)\n" ++
    "  la t0, create_address_be; addi t0, t0, 19; addi t1, sp, 32; li t2, 20\n" ++
    ".Lcr_tl_to_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lcr_tl_to_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    -- val_sw = reverse(create_value_be) = LE 32 bytes (sp+64)
    "  la t0, create_value_be; addi t0, t0, 31; addi t1, sp, 64; li t2, 32\n" ++
    ".Lcr_tl_val_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lcr_tl_val_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  addi a0, sp, 0\n  addi a1, sp, 32\n  addi a2, sp, 64\n" ++   -- from = from_sw, to = to_sw, amount = val_sw
    "  jal ra, eip7708_append_transfer_log\n" ++
    "  ld x10, 96(sp)\n  ld x12, 104(sp)\n  ld x13, 112(sp)\n  addi sp, sp, 128\n" ++
    ".Lcr_tl_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    -- drj99.1 (initcode_calls_with_value bv_fail=44): record the created account's endowment-credit
    -- as its FIRST non-storage effect, so the all-accounts comparator's first-pre = block-pre. The
    -- existing created-account record fires only at the CREATE deposit (RETURN handler, NoopHalt),
    -- which runs AFTER the initcode. When the initcode itself makes an outgoing value-CALL, that CALL's
    -- caller-debit record (ChildFrameHandlers .Lcd_deb_done: pre = endowment, post = endowment-out)
    -- lands BEFORE the deposit record, so nonstorage_effect_aggregate's first-pre for the created
    -- account = the MID-execution balance (endowment) instead of its block-pre (0). The BAL records
    -- the created-then-spent account as net-zero (balanceChanges:[]), so the agg first-pre=endowment vs
    -- BAL block-pre=0 mismatched -> bv_fail=44. Appending (create_address_be, pre=block-pre balance,
    -- post=endowment, pre_nonce=0, post_nonce=1) HERE -- after create_frame_descend switched x20 to the
    -- CHILD env (post-snapshot: env+656 already captured the pre-descend count, so frame_return ROLLS
    -- THIS BACK when the child reverts/fails) and BEFORE the initcode runs -- makes it the first record
    -- for the created address. pre = nse_create_pre_bal (the staged block-pre balance captured above);
    -- post = endowment (create_value_be, BE); nonce 0->1 (EIP-161 new-account nonce, matching the
    -- deposit record and the BAL's postNonce). Gated on the account-witness ctx (env+584, so
    -- create_value_be is valid) + value!=0 (a zero-endowment CREATE has no caller-debit to precede the
    -- deposit, and the deposit's pre=0 already gives first-pre=0). On the common CREATE-with-value path
    -- (initcode does NOT spend the endowment) this record has the same pre(0)/post(endowment) as the
    -- deposit, so first-pre/last-post are unchanged -- no regression. a0/a2/a3 alias x10/x12/x13 ->
    -- save/restore around record_nonstorage_effect.
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_nse_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  la t0, create_value_be\n  ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
    "  beqz t1, .Lcr_nse_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++   -- endowment == 0: deposit record suffices
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, create_address_be\n  la a1, nse_create_pre_bal\n  la a2, create_value_be\n  li a3, 0\n  li a4, 1\n" ++
    "  jal ra, record_nonstorage_effect\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    ".Lcr_nse_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    dispatchContinueRet ++ "\n" ++
    -- bbow4.4: EIP-684 CREATE/CREATE2 address collision consumes the child
    -- create-message gas allocation, while the pre-execute NEW_ACCOUNT state-gas
    -- charge is immediately refunded. The shared `7f` zero-result path kept all
    -- parent gas except CREATE static/base costs, so exact block gas under-counted
    -- the burned 63/64 child allotment. Compute:
    --   spill = max(0, NEW_ACCOUNT - state_gas_left)
    --   gas_after_state = gas_left - spill
    --   final_parent_gas = floor(gas_after_state / 64) + spill.
    -- The +spill term is execution-specs credit_state_gas_refund: because this
    -- synthetic collision branch leaves the state-gas globals unchanged, the
    -- spill refund must be included directly in the final gas_left value.
    -- Collision has net-zero state gas.
    ".Lcr_collision_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    -- Amsterdam generic_create warms contract_address before account_deployable; the
    -- successful path seeds at label 6 above, while collision jumps bypass that label.
    "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la a0, create_address_be\n" ++
    "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
    "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
    "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
    "  jal ra, runtime_access_account_seed\n" ++
    "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
    "  ld t3, 584(x20)\n  beqz t3, .Lcr_collision_nonce_done_" ++ (if hasSalt then "f5" else "f0") ++ "\n  la t0, nse_create_pre_bal\n  addi t1, x20, 63\n  li t2, 32\n.Lcr_collision_nonce_bal_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .Lcr_collision_nonce_bal_" ++ (if hasSalt then "f5" else "f0") ++ "\n  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
    "  la t0, create_nonce\n  ld a3, 0(t0)\n  addi a4, a3, 1\n  la a0, create_sender_be\n  la a1, nse_create_pre_bal\n  la a2, nse_create_pre_bal\n  jal ra, record_nonstorage_effect\n  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n.Lcr_collision_nonce_done_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    -- v0.6.0 (C11): an EIP-684 collision target holds code or a nonce, so
    -- is_account_alive is true and generic_create charges NO NEW_ACCOUNT
    -- state gas -- the burned child allowance is a plain 63/64 of the
    -- unreduced gas_left (system.py: create_message_gas computed from
    -- gas_left with no prior state charge; regular_gas_used +=
    -- create_message_gas). The v0.5.0 charge-spill-refill model is gone.
    "  ld t3, 568(x20)\n" ++
    "  srli t3, t3, 6\n" ++
    "  sd t3, 568(x20)\n" ++
    "7:\n" ++
    "  la t0, create_state_gas_charged_current\n  ld t1, 0(t0)\n  beqz t1, .Lcr_no_state_refund_" ++ (if hasSalt then "f5" else "f0") ++ "\n  sd x0, 0(t0)\n" ++
    "  li t2, 183600\n  la t0, evm_state_gas_spilled\n  ld t1, 0(t0)\n  li t3, 0\n  beqz t1, .Lcr_no_spill_refund_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  mv t3, t1\n  bleu t1, t2, .Lcr_spill_refund_le_" ++ (if hasSalt then "f5" else "f0") ++ "\n  mv t3, t2\n.Lcr_spill_refund_le_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  sub t1, t1, t3\n  sd t1, 0(t0)\n  ld t4, 568(x20)\n  add t4, t4, t3\n  sd t4, 568(x20)\n  sub t2, t2, t3\n" ++
    ".Lcr_no_spill_refund_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  beqz t2, .Lcr_refund_used_" ++ (if hasSalt then "f5" else "f0") ++ "\n  la t0, evm_state_gas_left\n  ld t1, 0(t0)\n  add t1, t1, t2\n  sd t1, 0(t0)\n" ++
    ".Lcr_refund_used_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  la t0, evm_state_gas_used\n  ld t1, 0(t0)\n  li t2, 183600\n  bltu t1, t2, .Lcr_no_state_refund_" ++ (if hasSalt then "f5" else "f0") ++ "\n" ++
    "  sub t1, t1, t2\n  sd t1, 0(t0)\n" ++
    ".Lcr_no_state_refund_" ++ (if hasSalt then "f5" else "f0") ++ ":\n" ++
    "  addi x12, x12, " ++ toString netPopBytes ++ "\n" ++
    "  sd x0, 0(x12)\n" ++
    "  sd x0, 8(x12)\n" ++
    "  sd x0, 16(x12)\n" ++
    "  sd x0, 24(x12)\n" ++
    "8:\n" ++
    "  addi x10, x10, 1\n" ++
    dispatchContinueRet

end EvmAsm.Codegen
