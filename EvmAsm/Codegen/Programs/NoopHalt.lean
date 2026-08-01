/-
  EvmAsm.Codegen.Programs.NoopHalt

  Terminating runtime opcode handlers split out of `Programs.Noop` to keep the
  mixed no-op/child-frame surface below the file-size guardrail.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.BodyStateSnapshot
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.Programs.Selfdestruct
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SpecRef.Gas
import EvmAsm.Codegen.ArenaCapacities
import EvmAsm.Codegen.GasConstants

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- v0.6 (evm-asm-0w05f.17.2): `generic_create` credits NEW_ACCOUNT state gas on
    child error ONLY when it charged it (`if new_account_charged:
    credit_state_gas_refund`, system.py:157-159) — an alive target skipped the
    conditional charge site, so its failed create must not credit anything.
    Stash the by-depth alive flag (recorded by the CREATE tail after
    `create_frame_descend`) into `create_failed_refund_skip` BEFORE
    `frame_return` pops the depth; `createFailedStateGasRefundAsm` tests it. -/
private def createFailedStateGasRefundStashAsm : String :=
  "  la t0, evm_call_depth\n  ld t1, 0(t0)\n" ++
  "  la t0, create_target_alive_flag\n  slli t1, t1, 3\n  add t0, t0, t1\n  ld t1, 0(t0)\n" ++
  "  la t0, create_failed_refund_skip\n  sd t1, 0(t0)\n"

private def createFailedStateGasRefundAsm (site : String) : String :=
  -- execution-specs `generic_create` credits NEW_ACCOUNT state gas on child error.
  -- `credit_state_gas_refund` is LIFO: refund gas_left spill first, then the
  -- state-gas reservoir. Gated on the charge having actually been made (target
  -- NOT alive): `create_failed_refund_skip` was stashed pre-`frame_return`.
  "  la t0, create_failed_refund_skip\n  ld t1, 0(t0)\n" ++
  "  bnez t1, .Lcr_failed_refund_done_" ++ site ++ "\n" ++
  "  li t2, 183600\n" ++
  "  la t0, evm_state_gas_spilled\n  ld t1, 0(t0)\n  li t3, 0\n" ++
  "  beqz t1, .Lcr_failed_refund_no_spill_" ++ site ++ "\n" ++
  "  mv t3, t1\n" ++
  "  bleu t1, t2, .Lcr_failed_refund_spill_le_" ++ site ++ "\n" ++
  "  mv t3, t2\n" ++
  ".Lcr_failed_refund_spill_le_" ++ site ++ ":\n" ++
  "  sub t1, t1, t3\n  sd t1, 0(t0)\n" ++
  "  ld t4, 568(x20)\n  add t4, t4, t3\n  sd t4, 568(x20)\n" ++
  "  sub t2, t2, t3\n" ++
  ".Lcr_failed_refund_no_spill_" ++ site ++ ":\n" ++
  "  beqz t2, .Lcr_failed_refund_used_" ++ site ++ "\n" ++
  "  la t0, evm_state_gas_left\n  ld t1, 0(t0)\n" ++
  "  add t1, t1, t2\n  sd t1, 0(t0)\n" ++
  ".Lcr_failed_refund_used_" ++ site ++ ":\n" ++
  "  la t0, evm_state_gas_used\n  ld t1, 0(t0)\n" ++
  "  li t2, 183600\n" ++
  "  bltu t1, t2, .Lcr_failed_refund_done_" ++ site ++ "\n" ++
  "  sub t1, t1, t2\n  sd t1, 0(t0)\n" ++
  ".Lcr_failed_refund_done_" ++ site ++ ":\n"

/-- RETURN/REVERT output tail. Both read `offset_low` / `size_low` from the
    stack, keep the legacy `OUTPUT_ADDR[0..32]` return-data prefix and
    `halt_kind` at `OUTPUT_ADDR+32`, and expose a wider diagnostic return-data
    surface at `OUTPUT_ADDR+64/+72/+248`.

    `sparseWindows` (guest only, evm-asm-0w05f.13): a depth-1+ CALL frame
    whose returndata window extends past the dense arena materializes it via
    `sparse_window_read` into `evm_precompile_frame+16` before `frame_return`
    (pairs with the depth-1+ arena-bail relaxation in
    `returnRevertMemoryGasAsm`). CREATE frames are unaffected (their windows
    are still dense-bounded by the preBody guard). -/
private def returnRevertTail (kind : Nat) (rollbackAsm : String := "")
    (depthAware : Bool := false) (sparseWindows : Bool := false) : String :=
  "  ld x14, 0(x12)\n" ++
  "  ld x15, 32(x12)\n" ++
  -- Depth-aware (guest only): a child frame's RETURN/REVERT returns to the parent
  -- via frame_return (success 1/0, returndata = child mem[offset..offset+size])
  -- instead of halting the guest. At depth 0 this is byte-identical (falls through
  -- to the original halt). REVERT rolls back the child's state before returning.
  (if depthAware then
    "  la t0, evm_call_depth\n" ++
    "  ld t0, 0(t0)\n" ++
    -- GH #10938: depth 0 normally halts here.  A depth-0 CREATE-frame RETURN does NOT:
    -- execution-specs `process_create_message` DEPOSITS UNCONDITIONALLY (`interpreter.py:215-241`)
    -- and only the CALLER pushes a result, so "no caller" must mean "no result to push", not
    -- "no deposit".  The guest encoded it as the latter, which is why the top-level route had to
    -- capture the returndata and run a SECOND deposit epilogue of its own.
    --
    -- `create_frame_flag[0]` is set by the top-level creation route, so it distinguishes a
    -- depth-0 creation RETURN from an ordinary depth-0 halt.  The deposit work below is
    -- depth-agnostic — it reads the code from `x13 + x14` / `x15`, which is exactly what the
    -- capture block copies FROM, so the data is live here.  The depth-0 exit therefore moves to
    -- just before `frame_return`, which is the only part that needs a parent.
    -- NOTE: kind 1 is RETURN and kind 2 is REVERT — the `.Lrr_createcap_1` / `.Lrr_halt_1`
    -- suffixes in the emitted stream are this `kind`, not an index.
    --
    -- ⛔ AND THE TRIPLE MUST BE STASHED BEFORE THE DEPOSIT RUNS.  `x13`/`x14`/`x15` are
    -- `a3`/`a4`/`a5`, and the deposit block calls `create_record_code_effect` (which loads
    -- `a4`/`a5` as `account_write_record` arguments) and `record_nonstorage_effect`.  At depth
    -- 1+ the clobber is invisible: the exit is `frame_return` with an explicit `a1`/`a2`, so
    -- the triple is dead.  At depth 0 it is NOT dead — `.Lrr_createcap_*` and the halt output
    -- tail both read `x13 + x14` / `x15` — so the depth-0 exit restores it from `rr_halt_ret_save`.
    -- Measured, not assumed: without the restore the halt wrote size 1 instead of 2484 on
    -- `stWalletTest/day_limit_construction`, and only output byte 248 changed, which is past
    -- the 105 bytes the fixture comparator reads.
    (if kind == 1 then
      "  bnez t0, .Lrr_depth_ok_" ++ toString kind ++ "\n" ++
      "  la t1, create_frame_flag; ld t1, 0(t1)\n" ++
      "  beqz t1, .Lrr_halt_" ++ toString kind ++ "\n" ++
      ".Lrr_depth_ok_" ++ toString kind ++ ":\n" ++
      "  la t1, rr_halt_ret_save; sd x13, 0(t1); sd x14, 8(t1); sd x15, 16(t1)\n" ++
      -- GH #11057: give depth 0 the state-gas snapshot every nested depth already has.
      -- `create_frame_descend` (`CallFrameDescend.lean:485-486`) writes the pair into the
      -- CHILD env on descend; nothing descends at depth 0, so `632`/`760` there hold a
      -- generic env-trailer word (zeroed by `Dispatch.lean:1195`, copied from the stateless
      -- INPUT by `:2670`) and `760(x20)` is never written at all. The spec's analogue is
      -- `message.state_gas_reservoir` — a field of the MESSAGE, constructed at every depth
      -- (`vm/__init__.py:240-256`), which is why this is a missing construction rather than a
      -- missing mechanism.
      --
      -- ⛔ GATED ON DEPTH 0. At depth 1+ the descend already wrote this pair as the frame's
      -- ENTRY values; rewriting it here with the CURRENT accumulators would make the refill in
      -- `.Lrr_crinv_*` a no-op and silently disable nested-CREATE state-gas rollback.
      "  bnez t0, .Lrr_sgsnap_done_" ++ toString kind ++ "\n" ++
      "  la t1, evm_state_gas_used; ld t2, 0(t1); sd t2, 632(x20)\n" ++
      "  la t1, evm_state_gas_spilled; ld t2, 0(t1); sd t2, 760(x20)\n" ++
      ".Lrr_sgsnap_done_" ++ toString kind ++ ":\n"
     else
      "  beqz t0, .Lrr_halt_" ++ toString kind ++ "\n") ++
    rollbackAsm ++
    -- .61.8.3.5.2 (.5b): a CREATE child frame (create_frame_flag[depth]=1, set by
    -- create_frame_descend) does NOT return a CALL result — on RETURN it deposits the
    -- returned bytes as the deployed code and pushes the DERIVED ADDRESS to the parent;
    -- on REVERT it pushes 0 (CREATE failed). A CALL frame uses frame_return (success +
    -- returndata). Clear the flag (frame-slot reuse). Inert until .5c wires the descent.
    "  la t1, create_frame_flag\n" ++
    "  slli t2, t0, 3\n" ++
    "  add t1, t1, t2\n" ++
    "  ld t3, 0(t1)\n" ++
    "  beqz t3, .Lrr_call_" ++ toString kind ++ "\n" ++
    "  sd x0, 0(t1)\n" ++
    "  la t1, create_address_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
    "  la t2, create_address_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
    "  la t1, create_sender_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
    "  la t2, create_sender_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
    "  la t1, create_value_by_depth; slli t2, t0, 5; add t1, t1, t2\n" ++
    "  la t2, create_value_be; ld t3, 0(t1); sd t3, 0(t2); ld t3, 8(t1); sd t3, 8(t2); ld t3, 16(t1); sd t3, 16(t2); ld t3, 24(t1); sd t3, 24(t2)\n" ++
    "  la t1, create_nonce_by_depth; slli t2, t0, 3; add t1, t1, t2\n" ++
    "  la t2, create_nonce; ld t3, 0(t1); sd t3, 0(t2)\n" ++
    (if kind == 2 then
      -- REVERT: CREATE failed -> push 0 (rollback already ran above).
      createFailedStateGasRefundStashAsm ++
      "  li a0, 0\n  add a1, x13, x14\n  mv a2, x15\n" ++
      "  jal ra, frame_return\n" ++
      createFailedStateGasRefundAsm ("revert_" ++ toString kind) ++
      ".Lrr_crrev_cr_" ++ toString kind ++ ":\n" ++
      dispatchContinueRet ++ "\n"
     else
      -- RETURN: validity-gate child mem[x14..x14+x15] (the deployed code), record the
      -- code-effect (copies it into the log BEFORE the frame pop), pop via frame_return
      -- (push 0 placeholder), then overwrite the parent result slot (x12) with the
      -- derived address. create_deployed_code_valid/create_record_code_effect preserve
      -- x13 (a3 mem base) and x14/x15 (per #8629); the validity result (a0) is consumed
      -- by bnez before create_record_code_effect clobbers a0.
      -- drj99.1.7: shared deposit entry. The depth-aware STOP handler (stopHandlerCF) routes a
      -- CREATE child frame that halts via STOP (initcode runs off the end / explicit 0x00) here
      -- with x14=x15=0 (STOP = RETURN with empty data -> 0-byte deployed code). Without this, a
      -- STOP-terminated create deposited nothing -> the created account's nonstorage effect was
      -- never recorded (bv_fail=44 notfound) and the parent got success=1 instead of the address.
      (if depthAware then ".Lcreate_deposit_from_halt_" ++ toString kind ++ ":\n" else "") ++
      "  add a0, x13, x14\n  mv a1, x15\n" ++
      "  jal ra, create_deployed_code_valid\n" ++
      "  bnez a0, .Lrr_crinv_" ++ toString kind ++ "\n" ++
      -- nxio8.7: charge code_hash_gas (keccak-per-word, REGULAR/GAS dim) = OPCODE_KECCACK256_PER_WORD(6)
      -- * ceil32(deployed_code_len)/32 = 6 * ((x15+31)>>5) words, spec amsterdam vm/interpreter.py:236-240
      -- charge_gas, BEFORE the state-gas charge ('regular before state' ordering). Simple charge_gas
      -- (no reservoir/spill): drain the child frame gas_left (568(x20)); OOG-fail the CREATE
      -- (-> .Lrr_crinv) if short. A valid block never OOGs at deposit -> no false-reject. x15 preserved.
      "  addi t0, x15, 31\n  srli t0, t0, 5\n" ++                  -- words = ceil32(len)/32
      "  li t1, " ++ toString amsterdamKeccak256PerWord ++ "\n  mul t0, t0, t1\n" ++   -- code_hash_gas = 6 * words
      "  ld t1, 568(x20)\n  bltu t1, t0, .Lrr_crinv_" ++ toString kind ++ "\n" ++   -- gas_left < code_hash_gas -> OOG, CREATE fails
      "  sub t1, t1, t0\n  sd t1, 568(x20)\n" ++                   -- gas_left -= code_hash_gas
      -- nxio8.6: charge code-deposit STATE gas = deployed_code_len(x15) * COST_PER_STATE_BYTE(1530)
      -- (spec amsterdam vm/interpreter.py:241-242 charge_state_gas(evm, ulen(code)*1530), AFTER the
      -- 0xEF/MAX_CODE_SIZE validity gate just above, BEFORE the deposit). Mirrors the SSTORE
      -- charge_state_gas pattern (Storage.lean): drain the global evm_state_gas_left reservoir; spill
      -- the remainder into the child frame gas_left (568(x20) = child env, before frame_return); if
      -- both are short, OOG-FAIL the CREATE (consume all child gas, push 0 via .Lrr_crinv) -- a valid
      -- block never OOGs at deposit, so no false-reject. evm_state_gas_used += charge on the non-OOG
      -- paths (spec raises BEFORE state_gas_used += amount; gas.py:302-311). Previously DROPPED ->
      -- state gas under-counted -> EIP-7778/8037 state budget too lenient (false-accept on state-heavy
      -- creation blocks); this makes the exec state gas (bvgr_tx_exec_state_gas) spec-accurate.
      -- x13/x14/x15 preserved by create_deployed_code_valid (#8629) and untouched here (only t0-t3 +
      -- the child gas_left). x15 <= MAX_CODE_SIZE (0x10000) so x15*1530 cannot overflow u64.
      "  li t0, " ++ toString amsterdamCostPerStateByte ++ "\n  mul t0, x15, t0\n" ++  -- code-deposit state gas = code_len * COST_PER_STATE_BYTE
      "  la t1, evm_state_gas_left\n  ld t2, 0(t1)\n" ++
      "  bgeu t2, t0, .Lrr_csg_res_" ++ toString kind ++ "\n" ++
      "  sub t3, t0, t2\n" ++                                             -- reservoir short: spill = charge - reservoir
      "  ld t4, 568(x20)\n  bgeu t4, t3, .Lrr_csg_spill_" ++ toString kind ++ "\n" ++  -- child gas_left >= spill -> ok
      "  sd x0, 568(x20)\n  j .Lrr_crinv_" ++ toString kind ++ "\n" ++         -- OOG: charge_state_gas raises before mutating reservoir/used
      ".Lrr_csg_spill_" ++ toString kind ++ ":\n" ++
      "  sd x0, 0(t1)\n" ++                                                -- reservoir = 0 only after sufficiency is known
      "  sub t4, t4, t3\n  sd t4, 568(x20)\n" ++
      "  la t1, evm_state_gas_spilled\n  ld t2, 0(t1)\n  add t2, t2, t3\n  sd t2, 0(t1)\n" ++
      "  j .Lrr_csg_used_" ++ toString kind ++ "\n" ++
      ".Lrr_csg_res_" ++ toString kind ++ ":\n" ++
      "  sub t2, t2, t0\n  sd t2, 0(t1)\n" ++                                  -- reservoir covers it
      ".Lrr_csg_used_" ++ toString kind ++ ":\n" ++
      "  la t1, evm_state_gas_used\n  ld t2, 0(t1)\n  add t2, t2, t0\n  sd t2, 0(t1)\n" ++
      -- Capture execution-specs generic_create target_alive current-tx evidence
      -- before publishing this CREATE.  This is a transaction-local CodeState
      -- membership query, not an append-only code-effect scan.
      "  la t0, create_target_alive_current_tx
  sd x0, 0(t0)
" ++
      -- `account_state_created_contains` uses a1..a3 for its bounded table
      -- scan.  x13/a3 is the CREATE return-data base below, so preserve it.
      "  addi sp, sp, -24
  sd x10, 0(sp)
  sd x12, 8(sp)
  sd x13, 16(sp)
" ++
      "  la a0, create_address_be
  jal ra, account_state_created_contains
" ++
      "  beqz a0, .Lrr_cralive_scan_done_" ++ toString kind ++ "
" ++
      "  la t0, create_target_alive_current_tx
  li t1, 1
  sd t1, 0(t0)
" ++
      ".Lrr_cralive_scan_done_" ++ toString kind ++ ":
" ++
      "  ld x10, 0(sp)
  ld x12, 8(sp)
  ld x13, 16(sp)
  addi sp, sp, 24
" ++
      "  la a0, create_address_be\n  add a1, x13, x14\n  mv a2, x15\n" ++
      "  jal ra, create_record_code_effect\n" ++
      -- i3djw.2 / drj99.1 part 3: record the created account's NON-STORAGE effect (pre balance captured
      -- before the CREATE frame; post nonce is the initcode's final nonce, balance = C's FINAL balance). The target may already be
      -- present with a nonzero balance, so its pre balance is nse_create_pre_bal rather than a fabricated
      -- zero: updateBuilderFromTx records a balance change only when the actual block pre/post differ.
      -- The final balance is C's LIVE selfBalance (env+32),
      -- NOT the CALLVALUE endowment: the initcode may CALL value out, so the created account ends at
      -- E - net_out. env+32 was credited the endowment at create_frame_descend (drj99.1 part 2) and
      -- debited by each byte-order-correct outgoing value-CALL (drj99.1 part 4), so it holds the true
      -- final. env+32 is LE (byte 32 = LSB, like CALLVALUE@96), so reverse x20+63..32 into
      -- nse_create_post_bal (BE) for the effect-log convention (matching i3djw.1).
      -- x20 = child env here (before frame_return restores the parent). a0/a2/a3 alias
      -- x10/x12/x13 -> saved/restored around record_nonstorage_effect.
      "  la t0, nse_create_post_bal\n  addi t1, x20, 63\n  li t2, 32\n" ++
      ".Lrr_crendow_" ++ toString kind ++ ":\n" ++
      "  lbu t3, 0(t1)\n  sb t3, 0(t0)\n  addi t1, t1, -1\n  addi t0, t0, 1\n  addi t2, t2, -1\n  bnez t2, .Lrr_crendow_" ++ toString kind ++ "\n" ++
      "  addi sp, sp, -48\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n  sd x14, 24(sp)\n  sd x15, 32(sp)\n" ++
      -- The per-creator nonce table is seeded to 1 for this child and advances
      -- for every inner CREATE. Do not use the generic effect log here: a later
      -- value-transfer record can carry a header-derived nonce for a newly-created
      -- account and is not the account's running CREATE nonce.
      "  la a0, create_address_be\n  jal ra, create_creator_nonce_current\n  mv a4, a0\n" ++
      "  la a0, create_address_be\n  la a1, nse_create_pre_bal\n  la a2, nse_create_post_bal\n  li a3, 0\n" ++
      "  jal ra, record_nonstorage_effect\n" ++
      "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  ld x14, 24(sp)\n  ld x15, 32(sp)\n  addi sp, sp, 48\n" ++
      -- drj99.1 part 1: a SUCCESSFUL CREATE deposit must pass success=1 to frame_return so the child
      -- frame's recorded effects (the created-account nonstorage record just appended, plus state-gas /
      -- refund / warmth / bloom) are KEPT. a0=0 is frame_return's REVERT signal: it truncated
      -- exec_nonstorage_effect_count back to the pre-child snapshot, ERASING the created-account record
      -- (record fired but log_count dropped to 0). The pushed success word is overwritten by the derived
      -- address below, so a0=1 here is purely the keep-effects signal (not the CREATE result).
      -- A successful CREATE exposes empty returndata to the parent (execution-specs
      -- generic_create sets return_data = b"" after incorporate_child_on_success);
      -- the returned constructor bytes were already consumed as deployed code above.
      "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
      "  la t0, create_target_alive_flag; slli t1, t1, 3; add t0, t0, t1\n" ++
      "  ld t1, 0(t0); la t0, create_target_alive_current_tx; sd t1, 0(t0)\n" ++
      -- GH #10938: THIS is the depth-0 exit.  Everything above is depth-agnostic deposit work;
      -- `frame_return` and the parent-slot write below are the only parts that need a caller,
      -- and at depth 0 there is none.  Matches the spec's division: the processor deposits, the
      -- caller pushes the result.  The restore of the RETURN triple is on the depth-0 side of
      -- the test only, so the depth-1+ path emits and executes exactly what it did before.
      "  la t0, evm_call_depth; ld t0, 0(t0); bnez t0, .Lrr_nottop_" ++ toString kind ++ "\n" ++
      "  la t1, rr_halt_ret_save; ld x13, 0(t1); ld x14, 8(t1); ld x15, 16(t1)\n" ++
      "  j .Lrr_halt_" ++ toString kind ++ "\n" ++
      ".Lrr_nottop_" ++ toString kind ++ ":\n" ++
      "  li a0, 1\n  li a1, 0\n  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      -- v0.6.0 (C11): no target-alive success refund -- an alive target
      -- was never charged (the conditional charge site skipped it).

      "  la t1, create_address_be\n  addi t1, t1, 19\n  mv t2, x12\n  li t3, 20\n" ++
      ".Lrr_craddr_" ++ toString kind ++ ":\n" ++
      "  beqz t3, .Lrr_craddr_d_" ++ toString kind ++ "\n" ++
      "  lbu t4, 0(t1)\n  sb t4, 0(t2)\n  addi t1, t1, -1\n  addi t2, t2, 1\n  addi t3, t3, -1\n  j .Lrr_craddr_" ++ toString kind ++ "\n" ++
      ".Lrr_craddr_d_" ++ toString kind ++ ":\n" ++
      -- drj99.1 part 5a: record the CREATOR's nonstorage effect (balance -endowment, nonce +1) on the
      -- SUCCESS path. This deposit is reached only when the CREATE succeeded (RETURN of a create_frame); a
      -- failed CREATE goes through .Lrr_crinv / the REVERT branch and never here, so no failure-rollback is
      -- needed (unlike recording at the pre-descend creator-debit). frame_return above restored the PARENT
      -- registers, so x20 = parent (creator) env and env+32 = the creator's selfBalance AFTER the pre-descend
      -- creator-debit = post_balance (LE). pre = post + endowment (create_value_be, BE). The creator's nonce
      -- bumps +1 on CREATE/CREATE2 (create_nonce = the per-creator running pre-nonce). create_sender_be =
      -- creator addr (BE). env+32 is LE -> reverse to BE into nse_create_post_bal (free after C's record);
      -- pre via u256_add_be into create_creator_newbal (free after the pre-descend debit). a0/a2/a3 alias
      -- x10/x12/x13 -> save/restore around both helper calls.
      "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
      "  addi t0, x20, 63\n  la t1, nse_create_post_bal\n  li t2, 32\n" ++
      ".Lrr_crp_rev_" ++ toString kind ++ ":\n" ++
      "  lbu t3, 0(t0)\n  sb t3, 0(t1)\n  addi t0, t0, -1\n  addi t1, t1, 1\n  addi t2, t2, -1\n  bnez t2, .Lrr_crp_rev_" ++ toString kind ++ "\n" ++
      "  la a0, nse_create_post_bal\n  la a1, create_value_be\n  la a2, create_creator_newbal\n" ++   -- pre = post + endowment
      "  jal ra, u256_add_be\n" ++
      "  la t0, create_nonce\n  ld t0, 0(t0)\n  mv a3, t0\n  addi a4, t0, 1\n" ++                       -- pre_nonce, post_nonce = pre+1
      "  la a0, create_sender_be\n  la a1, create_creator_newbal\n  la a2, nse_create_post_bal\n" ++   -- a1=pre_bal, a2=post_bal
      "  jal ra, record_nonstorage_effect\n" ++
      "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
      dispatchContinueRet ++ "\n" ++
      ".Lrr_crinv_" ++ toString kind ++ ":\n" ++
      -- ⛔ GH #10938 / #11057: THE REFILL BELOW NOW RUNS AT DEPTH 0 TOO, AND ONLY BECAUSE THE
      -- DEPTH-0 SNAPSHOT EXISTS. It reads `632(x20)`/`760(x20)`; at depth 0 those are written by
      -- the gated snapshot at `.Lrr_depth_ok_*` above. Before that snapshot existed, reading them
      -- here was a WIPE in the `.data`-baked variant and an INPUT-DERIVED SEED in the other, and
      -- neither faults — so this arm could not be enabled at depth 0 until the pair was written.
      -- The spec refills at every depth (`vm/interpreter.py:234`, and `refill_frame_state_gas`
      -- credits `state_gas_spilled` back to the frame's OWN `gas_left`, which at depth 0 is the
      -- transaction's), so running it here is the spec's shape rather than an extension of it.
      --
      -- What depth 0 still cannot do is `frame_return`: that is "the caller pushes the result",
      -- and there is no caller. It reads the PARENT env (`ld t0, 568(s4)`, `frame_return+0x49c`),
      -- so the depth-0 exit sits immediately before it — the same split as the success path.
      -- Witnessed, not predicted: with the exit any later,
      -- `eip7954_increase_max_contract_size/eip_mainnet/over_max_code_size_mainnet.json` — a
      -- `to == null` creation whose deployed code exceeds the limit, oracle succ bit 1, so the
      -- block is VALID — faults with `mcause=0x5 mtval=0x238 mepc=0x80048870`, i.e. `s4 = 0`.
      -- bbow4.2.5.1: invalid deployed code / code-deposit OOG is an
      -- exceptional CREATE failure. execution-specs process_create_message
      -- restores the child state snapshot and sets child gas_left = 0 before
      -- incorporate_child_on_error, so the parent does not get the forwarded
      -- gas back through frame_return. Refill the child frame's state gas
      -- into the global reservoir in LIFO order, but burn the gas-left portion
      -- by keeping env+568 at zero before frame_return observes it.
      "  ld t0, 632(x20)                 # used0\n" ++
      "  la t1, evm_state_gas_used; ld t2, 0(t1)\n" ++
      "  la t1, evm_state_gas_left; ld t3, 0(t1)\n" ++
      "  la t1, evm_state_gas_spilled; ld t4, 0(t1)\n" ++
      "  ld t5, 760(x20)                 # spilled0\n" ++
      "  bleu t4, t5, .Lrr_crinv_no_spill_delta_" ++ toString kind ++ "\n" ++
      "  sub t4, t4, t5\n" ++
      "  j .Lrr_crinv_have_spill_delta_" ++ toString kind ++ "\n" ++
      ".Lrr_crinv_no_spill_delta_" ++ toString kind ++ ":\n" ++
      "  li t4, 0\n" ++
      ".Lrr_crinv_have_spill_delta_" ++ toString kind ++ ":\n" ++
      "  bleu t2, t0, .Lrr_crinv_refill_done_" ++ toString kind ++ "\n" ++
      "  sub t2, t2, t0\n" ++
      "  bleu t2, t4, .Lrr_crinv_refill_done_" ++ toString kind ++ "\n" ++
      "  sub t2, t2, t4\n" ++
      "  add t3, t3, t2\n" ++
      ".Lrr_crinv_refill_done_" ++ toString kind ++ ":\n" ++
      "  la t1, evm_state_gas_left; sd t3, 0(t1)\n" ++
      "  ld t0, 632(x20); la t1, evm_state_gas_used; sd t0, 0(t1)\n" ++
      "  ld t0, 760(x20); la t1, evm_state_gas_spilled; sd t0, 0(t1)\n" ++
      "  sd x0, 568(x20)\n" ++
      createFailedStateGasRefundStashAsm ++
      -- GH #10938: the depth-0 exit, immediately before `frame_return` and after every
      -- depth-agnostic part of the failure handling has run. The triple is restored because
      -- `.Lrr_halt_*` and `.Lrr_createcap_*` read `x13 + x14` / `x15`, and the recorder calls
      -- above clobber `a3`/`a4`/`a5`. ⚠️ `createFailedStateGasRefundAsm` below is deliberately
      -- NOT reached at depth 0: it credits `generic_create`'s NEW_ACCOUNT charge back on CHILD
      -- error and is gated on the by-depth alive flag stashed just above, so it has no depth-0
      -- counterpart — the transaction-level settle path owns that gas.
      (if kind == 1 then
        "  la t0, evm_call_depth; ld t0, 0(t0); bnez t0, .Lrr_crinv_nottop_" ++ toString kind ++ "\n" ++
        -- GH #10938: PUBLISH the depth-0 deposit failure so the creation stage still reaches its
        -- own exception/settle arm.  The stage used to learn this by running the validator
        -- itself; with that removed it has to be told.  ⛔ The channel is
        -- `top_level_creation_returndata_status`, NOT output byte 32: the halt tail below writes
        -- `li x17, kind` / `sd x17, 32(x16)` at its end, so any halt-kind stamp set here would be
        -- overwritten before the stage could read it.  ⛔ NOR can it be
        -- `top_level_creation_returndata_status`: `.Lrr_createcap_*` also runs AFTER the halt
        -- label and writes that cell unconditionally — 1 when the return fits the capture buffer,
        -- 2 when it does not — so a failure published there is clobbered, and in the
        -- fits-the-buffer case clobbered with 1, which the stage reads as SUCCESS.  Measured:
        -- 0x800517ac wrote 3, 0x80051a44 then wrote 2, and the stage read 2.  So this needs a
        -- cell nothing on the halt path writes.
        "  la t1, create_deposit_failed_flag; li t2, 1; sd t2, 0(t1)\n" ++
        "  la t1, rr_halt_ret_save; ld x13, 0(t1); ld x14, 8(t1); ld x15, 16(t1)\n" ++
        "  j .Lrr_halt_" ++ toString kind ++ "\n" ++
        ".Lrr_crinv_nottop_" ++ toString kind ++ ":\n"
       else "") ++
      "  li a0, 0\n  li a1, 0\n  li a2, 0\n" ++
      "  jal ra, frame_return\n" ++
      createFailedStateGasRefundAsm ("invalid_" ++ toString kind) ++
      ".Lrr_crinv_cr_" ++ toString kind ++ ":\n" ++
      dispatchContinueRet ++ "\n") ++
    ".Lrr_call_" ++ toString kind ++ ":\n" ++
    (if sparseWindows then
      -- evm-asm-0w05f.13: materialize only a window that ends beyond this
      -- frame's actual dense capacity. Under the shared pool that capacity is
      -- frame-relative (`pool_end - x13`), not the retired 128 KiB slot size.
      -- Using the old constant routed affordable pool windows through the
      -- sparse store and returned zeros (ck36u). The staging-cap guard remains
      -- defense-in-depth. x10/x12/ra are dead here (frame_return restores the
      -- parent's); the retdata src/len are carried in x18/x19 across helpers.
      "  mv x19, x15                    # retlen (survives the helper calls)\n" ++
      -- A ZERO-SIZE window never touches memory (the preBody skipped all
      -- guards/charges for it, matching the spec), so the offset may be any
      -- huge in-u64 value (stMemoryStressTest return_bounds: RETURN with a
      -- 2^35..2^255-shaped offset and size 0). Route it to the dense path —
      -- frame_return copies and stages min(outsize, 0) = 0 bytes, never
      -- dereferencing the pointer — instead of tripping the staging-cap
      -- guard on offset+0.
      "  beqz x15, .Lrr_call_dense_" ++ toString kind ++ "\n" ++
      "  add t0, x14, x15\n" ++
      "  la t1, evm_memory_pool_end\n" ++
      "  sub t1, t1, x13                # frame-relative pool capacity\n" ++
      "  bgeu t1, t0, .Lrr_call_dense_" ++ toString kind ++ "\n" ++
      "  li t1, " ++ toString precompileFrameReturndataCapBytes ++ "\n" ++
      "  bltu t1, t0, .exit_outofgas\n" ++
      "  la a0, evm_precompile_frame\n" ++
      "  addi a0, a0, 16\n" ++
      "  mv a1, x14\n" ++
      "  mv a2, x15\n" ++
      -- a3 IS x13 (the dense memory base) already; no move needed.
      "  jal ra, sparse_window_read\n" ++
      "  mv x18, a0                     # retdata src = staging\n" ++
      "  j .Lrr_call_havesrc_" ++ toString kind ++ "\n" ++
      ".Lrr_call_dense_" ++ toString kind ++ ":\n" ++
      "  add x18, x13, x14              # retdata src = dense child memory\n" ++
      ".Lrr_call_havesrc_" ++ toString kind ++ ":\n" ++
      -- 0w05f.13 surface 2: when the PARENT's saved out-window
      -- (frame_call_ctx[d]: outoff_abs/outsize) ends past the PARENT's
      -- frame-relative pool capacity, frame_return's raw copy would write
      -- outside the pool. Perform the write-back here instead via
      -- sparse_window_write (dense prefix raw + word entries keyed to the
      -- parent depth d-1), then zero ctx.outsize so frame_return skips its
      -- copy. A depth-1 child's parent is the root frame (4 MiB dense,
      -- affordability-bounded) — skip. The spec copies
      -- output[:memory_output_size] for RETURN and REVERT alike, so this
      -- runs for both kinds.
      "  la t0, evm_call_depth\n" ++
      "  ld t0, 0(t0)\n" ++
      "  li t1, 1\n" ++
      "  bgeu t1, t0, .Lrr_call_wb_done_" ++ toString kind ++ "\n" ++
      "  la t3, frame_call_ctx\n" ++
      "  slli t4, t0, 5\n" ++
      "  add t3, t3, t4                 # ctx ptr (child depth d)\n" ++
      "  ld t4, 16(t3)                  # outsize\n" ++
      "  beqz t4, .Lrr_call_wb_done_" ++ toString kind ++ "\n" ++
      "  bgeu x19, t4, .Lrr_call_wb_n_" ++ toString kind ++ "\n" ++
      "  mv t4, x19                     # n = min(outsize, retlen)\n" ++
      ".Lrr_call_wb_n_" ++ toString kind ++ ":\n" ++
      "  beqz t4, .Lrr_call_wb_done_" ++ toString kind ++ "\n" ++
      "  la t5, frame_parent_bases\n" ++
      "  slli t6, t0, 4\n" ++
      "  add t5, t5, t6\n" ++
      "  ld t5, 0(t5)                   # parent memory base\n" ++
      "  ld t6, 8(t3)                   # outoff_abs\n" ++
      "  sub t6, t6, t5                 # raw parent out offset\n" ++
      "  add t0, t6, t4\n" ++
      "  la t1, evm_memory_pool_end\n" ++
      "  sub t1, t1, t5                 # parent-relative pool capacity\n" ++
      "  bgeu t1, t0, .Lrr_call_wb_done_" ++ toString kind ++ "\n" ++   -- in-frame: frame_return's raw copy is exact
      "  mv a0, x18                     # src = retdata bytes\n" ++
      "  mv a1, t6                      # raw parent offset\n" ++
      "  mv a2, t4                      # n\n" ++
      "  mv a3, t5                      # parent memory base\n" ++
      "  la a4, evm_call_depth\n" ++
      "  ld a4, 0(a4)\n" ++
      "  addi a4, a4, -1                # target = parent depth\n" ++
      "  jal ra, sparse_window_write\n" ++
      "  la t0, evm_call_depth\n" ++
      "  ld t0, 0(t0)\n" ++
      "  la t3, frame_call_ctx\n" ++
      "  slli t4, t0, 5\n" ++
      "  add t3, t3, t4\n" ++
      "  sd x0, 16(t3)                  # ctx.outsize = 0: frame_return skips its raw copy\n" ++
      ".Lrr_call_wb_done_" ++ toString kind ++ ":\n" ++
      "  li a0, " ++ (if kind == 2 then "0" else "1") ++ "\n" ++
      "  mv a1, x18\n" ++
      "  mv a2, x19\n" ++
      "  jal ra, frame_return\n" ++
      dispatchContinueRet ++ "\n"
     else
      "  li a0, " ++ (if kind == 2 then "0" else "1") ++ "\n" ++
      "  add a1, x13, x14\n" ++
      "  mv a2, x15\n" ++
      "  jal ra, frame_return\n" ++
      dispatchContinueRet ++ "\n") ++
    ".Lrr_halt_" ++ toString kind ++ ":\n"
   else "") ++
  -- A capture is valid only for the outermost RETURN: an inner call's data must never
  -- overwrite the top-level system-call/creation result.  Mode 1 is the bounded
  -- EIP-7002/7251 capture; mode 2 is top-level CREATE and has the EIP-170-sized
  -- buffer plus an explicit oversized status.  x13=mem base, x14=offset, x15=size.
  (if kind == 1 then
    "  la t0, system_call_mode\n  ld t0, 0(t0)\n  beqz t0, .Lrr_nocap_" ++ toString kind ++ "\n" ++
    "  la t1, evm_call_depth\n  ld t1, 0(t1)\n  bnez t1, .Lrr_nocap_" ++ toString kind ++ "\n" ++
    "  li t1, 2\n  beq t0, t1, .Lrr_createcap_" ++ toString kind ++ "\n" ++
    "  li t1, " ++ toString systemCallReturndataMaxBytes ++ "\n  bltu t1, x15, .Lrr_nocap_" ++ toString kind ++ "\n" ++   -- oversized system result -> unsupported
    "  la t1, system_call_returndata_len\n  sd x15, 0(t1)\n" ++
    "  add t2, x13, x14\n  la t3, system_call_returndata\n  mv t4, x15\n" ++
    ".Lrr_capz_" ++ toString kind ++ ":\n" ++
    "  beqz t4, .Lrr_nocap_" ++ toString kind ++ "\n" ++
    "  lbu t5, 0(t2)\n  sb t5, 0(t3)\n  addi t2, t2, 1\n  addi t3, t3, 1\n  addi t4, t4, -1\n  j .Lrr_capz_" ++ toString kind ++ "\n" ++
    ".Lrr_createcap_" ++ toString kind ++ ":\n" ++
    -- GH #10938 piece 3: the captured BYTES and their LENGTH are gone.  Piece 2 moved the deposit
    -- into the survivor and deleted the creation stage's deposit block, which was the only reader
    -- of `top_level_creation_returndata` and `..._len`; the capture outlived its consumer.  What
    -- survives is the STATUS, which `BlockVerdictCreationStage` still loads to route the depth-0
    -- creation RETURN (1 -> settle, 2 -> exception).  Three cells shared one prefix and had three
    -- fates: the buffer had a writer and no reader, the length had a writer AND A CLEAR and no
    -- load — ⚠️ a clear is a write, so four references read as "live" and were not — and only the
    -- status has a real consumer.
    --
    -- ⚠️ `topLevelCreationReturndataMaxBytes` therefore remains as a THRESHOLD WITH NO BUFFER
    -- BEHIND IT.  It is deliberately NOT folded into the deposit validator's limit even though
    -- both are currently 65536: the validator enforces the EIP-7907 deployed-code limit
    -- (`CreateDeployedCodeValid`'s own probe pins 65536 valid / 65537 invalid), and this is a
    -- capture bound.  They are EQUAL BY COINCIDENCE, not by construction, so status 2 and
    -- `create_deposit_failed_flag` fire together today and would separate the moment either
    -- constant moved.  Collapsing them is GH #10938 piece 4 and needs that equality promoted to a
    -- stated invariant or removed — not assumed.
    "  li t1, " ++ toString topLevelCreationReturndataMaxBytes ++ "\n  bltu t1, x15, .Lrr_createcap_over_" ++ toString kind ++ "\n" ++
    "  la t1, top_level_creation_returndata_status\n  li t5, 1\n  sd t5, 0(t1)\n" ++
    "  j .Lrr_nocap_" ++ toString kind ++ "\n" ++
    ".Lrr_createcap_over_" ++ toString kind ++ ":\n" ++
    "  la t1, top_level_creation_returndata_status\n  li t5, 2\n  sd t5, 0(t1)\n" ++
    ".Lrr_nocap_" ++ toString kind ++ ":\n"
   else "") ++
  "  li x16, 0xa0010000\n" ++
  "  sd x0, 0(x16)\n" ++
  "  sd x0, 8(x16)\n" ++
  "  sd x0, 16(x16)\n" ++
  "  sd x0, 24(x16)\n" ++
  "  addi x19, x16, 72\n" ++
  "  li x21, 22\n" ++
  "1:\n" ++
  "  beqz x21, 2f\n" ++
  "  sd x0, 0(x19)\n" ++
  "  addi x19, x19, 8\n" ++
  "  addi x21, x21, -1\n" ++
  "  j 1b\n" ++
  "2:\n" ++
  "  mv x21, x15\n" ++
  "  li x22, 176\n" ++
  "  bgeu x22, x21, 3f\n" ++
  "  mv x21, x22\n" ++
  "3:\n" ++
  "  sd x15, 64(x16)\n" ++
  "  sd x21, 248(x16)\n" ++
  "  la x17, evm_memory\n" ++
  "  add x17, x17, x14\n" ++
  "  addi x19, x16, 72\n" ++
  "  mv x22, x21\n" ++
  "4:\n" ++
  "  beqz x22, 5f\n" ++
  "  lbu x23, 0(x17)\n" ++
  "  sb x23, 0(x19)\n" ++
  "  addi x17, x17, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j 4b\n" ++
  "5:\n" ++
  "  la x17, evm_memory\n" ++
  "  add x17, x17, x14\n" ++
  "  mv x22, x15\n" ++
  "  li x21, 32\n" ++
  "  bgeu x21, x22, 6f\n" ++
  "  mv x22, x21\n" ++
  "6:\n" ++
  "  mv x19, x16\n" ++
  "7:\n" ++
  "  beqz x22, 8f\n" ++
  "  lbu x23, 0(x17)\n" ++
  "  sb x23, 0(x19)\n" ++
  "  addi x17, x17, 1\n" ++
  "  addi x19, x19, 1\n" ++
  "  addi x22, x22, -1\n" ++
  "  j 7b\n" ++
  "8:\n" ++
  s!"  li x17, {kind}\n" ++
  "  sd x17, 32(x16)\n" ++
  rollbackAsm ++
  -- 4ch8f.10.3: depth-0 RETURN/REVERT halt via flag+ret (routes to .exit_no_epilogue).
  dispatchHaltRet 2

/-- Stage the popped SELFDESTRUCT beneficiary for later EIP-6780 state work. -/
private def selfdestructTailAsm : String :=
  -- coc3g.6.5: reset the created-in-tx marker at the start of every SELFDESTRUCT (it is set
  -- below only when the selfdestructing account has a code-effect record from a CREATE earlier
  -- in THIS tx execution; a stale 1 from a previous selfdestruct would mis-route this one).
  "  la x14, evm_selfdestruct_created_in_tx\n  sd x0, 0(x14)\n" ++
  "  la x14, evm_selfdestruct_beneficiary\n" ++
  "  mv x15, x14\n" ++
  "  li x16, 4\n" ++
  ".L_selfdestruct_zero_scratch:\n" ++
  "  sd x0, 0(x15)\n" ++
  "  addi x15, x15, 8\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, .L_selfdestruct_zero_scratch\n" ++
  "  addi x15, x12, 19\n" ++
  "  li x16, 20\n" ++
  ".L_selfdestruct_copy_beneficiary:\n" ++
  "  lbu x17, 0(x15)\n" ++
  "  sb x17, 0(x14)\n" ++
  "  addi x15, x15, -1\n" ++
  "  addi x14, x14, 1\n" ++
  "  addi x16, x16, -1\n" ++
  "  bnez x16, .L_selfdestruct_copy_beneficiary\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd x10, 0(sp)\n" ++
  "  sd x12, 8(sp)\n" ++
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  la a1, " ++ runtimeAccessAccountTableLabel ++ "\n" ++
  "  la a2, " ++ runtimeAccessAccountCountLabel ++ "\n" ++
  "  li a3, " ++ toString runtimeAccessAccountCapacity ++ "\n" ++
  "  jal ra, runtime_access_account_charge\n" ++
  -- SELFDESTRUCT charges COLD_ACCOUNT_ACCESS (3000) for a COLD beneficiary and 0

  -- when warm (spec amsterdam vm/instructions/system.py:646-650; unlike CALL, it
  -- adds NO warm-access cost). runtime_access_account_charge only debited the

  -- 2900 cold delta (its 100 floor presumes a dispatcher account-opcode floor that
  -- SELFDESTRUCT's 5000 base lacks), so add the missing 100 ONLY on the cold path
  -- (helper a0==1) to reach the full 3000; a warm beneficiary stays at 0. Without
  -- this the cold-beneficiary SELFDESTRUCT under-charged regular gas by 100,
  -- corrupting the type-4 receipt cumulative (bv_fail=53). Check a0 before the
  -- x10 restore clobbers it.
  "  beqz a0, .L_selfdestruct_access_floor_done\n" ++
  "  ld t0, 568(x20)\n" ++
  s!"  li t1, {EvmAsm.Stateless.SpecRef.GasCosts.WARM_ACCESS}\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
  ".L_selfdestruct_access_floor_done:\n" ++
  -- `selfdestruct` unconditionally performs the tracked beneficiary read after
  -- the access-gas check (`system.py:654-669`).  The warm/cold table above is
  -- separate from the BAL `account_reads` set, so record precompile and other
  -- all-empty beneficiaries even when the access charge was already warm.
  "  la a0, evm_selfdestruct_beneficiary\n" ++
  "  jal ra, account_read_record\n" ++
  "  ld x10, 0(sp)\n" ++
  "  ld x12, 8(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  selfdestructNewAccountSurchargeAsm ++
  selfdestructLoadAccountInputsAsm ++
  -- coc3g.6.5: a contract CREATEd earlier in THIS tx that SELFDESTRUCTs is DELETED (EIP-6780).
  -- Detect that by looking up the selfdestructing account (env.ADDRESS, canonical BE) in
  -- exec_code_effect_log (the CREATE deposit recorded the deployed code there); on a hit set
  -- evm_selfdestruct_created_in_tx=1 so the downstream balance-transfer / EIP-7708 log / beneficiary
  -- nonstorage record (Selfdestruct.lean) take the created-in-tx paths (emit a Burn for self-destruct
  -- to-self; record the child deletion to 0/0 + the beneficiary credit). selfdestructLoadAccountInputsAsm
  -- now always builds sdai_origin_address = env.ADDRESS (BE), even when the header witness ctx
  -- is absent, so the same-tx code-effect cleanup can still run on unsupported runtime rows.
  -- find_code_effect_by_address clobbers t0-t6 + a0(=x10) -> save x10/x12.

  -- coc3g.6.2: a contract whose constructor SELFDESTRUCTs (initcode `..ff`) NEVER deposits code,
  -- so exec_code_effect_log has NO record for it and find_code_effect_by_address below would MISS
  -- -> created_in_tx stays 0 -> the SD took the witness-present path which BAILS (the child is
  -- absent from the block-pre witness) -> the beneficiary credit / child deletion were never
  -- recorded -> bv_fail=44 (selfdestruct_to_*_same_tx with_balance). The spec's authoritative
  -- created-in-tx signal is `originator in tx_state.created_accounts` (system.py selfdestruct:687),
  -- which is set at generic_create (account creation), BEFORE the initcode runs -- independent of
  -- any code deposit. We are running INSIDE the CREATE child frame here (the SD halts the
  -- constructor), and create_frame_descend set create_frame_flag[current_depth]=1 (cleared only by
  -- the RETURN/REVERT deposit, NOT this SD path), so the flag at the current depth IS exactly that
  -- created_accounts membership for the originator. Detect it directly -- this is the precise spec
  -- signal and needs no code deposit. (The code-effect-log check below still covers a created child
  -- that DEPLOYED code and is later SELFDESTRUCTed by a CALL from a parent frame, where this flag's
  -- depth no longer matches.) Soundness: this can only mark the genuinely-created originator as
  -- created-in-tx (recording MORE exec effects the BAL declares), never a witnessed account.
  "  la t0, evm_call_depth\n  ld t0, 0(t0)\n" ++
  "  la t1, create_frame_flag\n  slli t2, t0, 3\n  add t1, t1, t2\n  ld t1, 0(t1)\n" ++
  "  beqz t1, .L_selfdestruct_ctit_codecheck\n" ++
  "  la t0, evm_selfdestruct_created_in_tx\n  li t2, 1\n  sd t2, 0(t0)\n" ++
  "  j .L_selfdestruct_created_in_tx_mark\n" ++
  ".L_selfdestruct_ctit_codecheck:\n" ++
  -- AccountState's transaction-local created set follows the normal caller-saved ABI and
  -- clobbers a0-a3.  x13 is the live EVM stack cursor on this halt path, so
  -- preserve it with the other runtime cursors before asking the CodeState.
  "  addi sp, sp, -24\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  la a0, sdai_origin_address\n" ++
  "  jal ra, account_state_created_contains\n" ++
  "  mv t1, a0\n" ++                                  -- current-tx creation membership
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 24\n" ++
  "  beqz t1, .L_selfdestruct_created_in_tx_done\n" ++
  "  j .L_selfdestruct_created_in_tx_mark\n" ++
  ".L_selfdestruct_created_in_tx_mark:\n" ++
  -- Deletion is deferred until transaction finalization.  Queue the address
  -- in AccountState; the current entry stays executable for later same-tx
  -- CALLs.  Keep the live runtime cursors intact across the set helpers.
  "  addi sp, sp, -24; sd x10, 0(sp); sd x12, 8(sp); sd x13, 16(sp)\n" ++
  "  la a0, sdai_origin_address; la a1, account_state_delete; la a2, account_state_delete_count; li a3, " ++ toString accountStateDeleteCapacity ++ "; jal ra, code_state_address_set_insert; bnez a0, .L_selfdestruct_created_delete_restore_overflow\n" ++
  "  la a0, sdai_origin_address; la a1, account_state_delete; la a2, account_state_delete_count; li a3, " ++ toString accountStateDeleteCapacity ++ "; li a4, 1; jal ra, code_state_address_set_flag; mv t3, a0\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 24; beqz t3, .L_selfdestruct_created_legacy_clear\n" ++
  ".L_selfdestruct_created_delete_restore_overflow:\n" ++
  "  ld x10, 0(sp); ld x12, 8(sp); ld x13, 16(sp); addi sp, sp, 24\n" ++
  ".L_selfdestruct_created_delete_overflow:\n" ++
  "  la t0, account_state_overflow; li t1, 1; sd t1, 0(t0); j .L_selfdestruct_created_in_tx_done\n" ++
  ".L_selfdestruct_created_legacy_clear:\n" ++
  -- coc3g.6.5: EIP-6780 DELETES the created-in-tx contract, so its deployed code is removed --
  -- a created-then-destroyed-same-tx account has NET-ZERO code change and the BAL declares no
  -- codeChange. The CREATE deposit appended a code-effect record (has_code_change=1) to
  -- exec_code_effect_log; without removing it the code comparator (bv_fail=46) sees an exec code
  -- change with no matching BAL codeChange. Zero the record's has_code_change field (record+32) so
  -- both the forward (bal_account_code_consistent: has_code_change=0 + BAL silent -> consistent) and
  -- the reverse (_covers: has_code_change=0 -> no obligation) treat it as no code change. KEEP code_len
  -- (record+40) so both comparators' variable-stride walk stays aligned.
  "  addi sp, sp, -16; sd x10, 0(sp); sd x12, 8(sp); la a0, exec_code_effect_log; la t0, exec_code_effect_count; ld a1, 0(t0); la a2, sdai_origin_address; jal ra, find_code_effect_by_address; mv t1, a0; ld x10, 0(sp); ld x12, 8(sp); addi sp, sp, 16; beqz t1, .L_selfdestruct_created_in_tx_finish; sd x0, 32(t1)\n" ++
  ".L_selfdestruct_created_in_tx_finish:\n" ++
  "  la t0, evm_selfdestruct_created_in_tx; li t1, 1; sd t1, 0(t0); j .L_selfdestruct_created_in_tx_done\n" ++
  ".L_selfdestruct_created_in_tx_done:\n" ++
  selfdestructBalanceTransferRuntimeAsm ++
  selfdestructEip7708LogRuntimeAsm ++
  "  la x14, evm_selfdestruct_staged\n" ++
  "  li x15, 1\n" ++
  "  sd x15, 0(x14)\n" ++
  selfdestructBeneficiaryNonstorageAsm ++
  selfdestructRecordSeenOriginAsm ++
  -- coc3g.6.2: a CREATE child frame that halts via SELFDESTRUCT (constructor `..ff`) goes to
  -- .exit_selfdestruct, which (unlike RETURN/REVERT/STOP) does NOT clear create_frame_flag[depth].
  -- Now that the created-in-tx detection above CONSUMES this flag, a stale 1 left in this depth's
  -- slot would be inherited by a later CALL frame descending into the same (reused) depth slot --
  -- if that CALL frame then SELFDESTRUCTs, the stale flag would falsely mark a witnessed account as
  -- created-in-tx (a potential false-ACCEPT). Clear it here (depth>0 only; the flag table is depth-
  -- indexed and depth 0 is the top frame, never a CREATE child) to mirror the other halt exits and
  -- keep the slot clean for reuse. Guarded on depth>0 so a top-level SELFDESTRUCT is untouched.
  "  la t0, evm_call_depth\n  ld t0, 0(t0)\n  beqz t0, .L_sd_flag_clear_done\n" ++
  "  la t1, create_frame_flag\n  slli t2, t0, 3\n  add t1, t1, t2\n  ld t3, 0(t1)\n  sd x0, 0(t1)\n" ++
  "  bnez t3, .L_sd_create_return\n" ++
  ".L_sd_flag_clear_done:\n" ++
  "  addi x12, x12, 32\n" ++
  -- 4ch8f.10.3: SELFDESTRUCT halt via flag+ret (routes to .exit_selfdestruct,
  -- which is itself depth-aware).
  dispatchHaltRet 4 ++ "\n" ++
  ".L_sd_create_return:\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
  "  la t0, create_target_alive_flag; slli t1, t1, 3; add t0, t0, t1\n" ++
  "  ld t1, 0(t0); la t0, create_target_alive_current_tx; sd t1, 0(t0)\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
  "  la t0, create_address_by_depth; slli t1, t1, 5; add t0, t0, t1\n" ++
  "  la t1, create_address_be; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
  "  la t0, create_sender_by_depth; slli t1, t1, 5; add t0, t0, t1\n" ++
  "  la t1, create_sender_be; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
  "  la t0, create_value_by_depth; slli t1, t1, 5; add t0, t0, t1\n" ++
  "  la t1, create_value_be; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0)\n" ++
  "  la t0, create_nonce_by_depth; slli t1, t1, 3; add t0, t0, t1\n" ++
  "  la t1, create_nonce; ld t2, 0(t0); sd t2, 0(t1)\n" ++
  "  li a0, 1\n  li a1, 0\n  li a2, 0\n" ++
  "  jal ra, frame_return\n" ++
  -- v0.6.0 (C11): no target-alive success refund (alive targets are not
  -- charged at the conditional charge site).

  "  la t1, create_address_be\n  addi t1, t1, 19\n  mv t2, x12\n  li t3, 20\n" ++
  ".L_sd_create_addr_loop:\n" ++
  "  beqz t3, .L_sd_create_addr_done\n" ++
  "  lbu t4, 0(t1)\n  sb t4, 0(t2)\n  addi t1, t1, -1\n  addi t2, t2, 1\n  addi t3, t3, -1\n  j .L_sd_create_addr_loop\n" ++
  ".L_sd_create_addr_done:\n" ++
  -- A CREATE init frame which halts through SELFDESTRUCT is still a successful
  -- CREATE: its creator's nonce advances and its endowment remains moved into
  -- the (then EIP-6780-cleared) child.  The normal CREATE RETURN/STOP deposit
  -- arm appends this final creator effect after frame_return; this special arm
  -- used to return the address without that record, leaving the BAL's creator
  -- balance/nonce change unmatched (bv_fail=44).
  -- frame_return has restored the creator env in x20 and the per-depth globals
  -- above restored create_sender_be/create_value_be/create_nonce.
  "  addi sp, sp, -32\n  sd x10, 0(sp)\n  sd x12, 8(sp)\n  sd x13, 16(sp)\n" ++
  "  addi t0, x20, 63\n  la t1, nse_create_post_bal\n  li t2, 32\n" ++
  ".L_sd_create_creator_post_rev:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .L_sd_create_creator_post_rev\n" ++
  "  la a0, nse_create_post_bal\n  la a1, create_value_be\n  la a2, create_creator_newbal\n" ++
  "  jal ra, u256_add_be\n" ++
  "  la t0, create_nonce\n  ld a3, 0(t0)\n  addi a4, a3, 1\n" ++
  "  la a0, create_sender_be\n  la a1, create_creator_newbal\n  la a2, nse_create_post_bal\n" ++
  "  jal ra, record_nonstorage_effect\n" ++
  "  ld x10, 0(sp)\n  ld x12, 8(sp)\n  ld x13, 16(sp)\n  addi sp, sp, 32\n" ++
  dispatchContinueRet

/-- M18 / M23 / M31 EVM-terminating opcodes. `depthAware` makes RETURN/REVERT
    return to the parent frame (via `frame_return`) when `evm_call_depth > 0`
    instead of halting — used by the call-frame guest registry; the standalone
    dispatch probes pass `false` (byte-identical halt, no `frame_return` link). -/
def haltHandlers (depthAware : Bool) (sparseWindows : Bool := false) : List OpcodeHandlerSpec :=
  [ { label   := "h_RETURN"
    , opcodes := [0xf3]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 returnRevertMemoryGasAsm "return" sparseWindows
    , body    := []
    , tail    := .custom (returnRevertTail 1 "" depthAware sparseWindows) }
  , { label   := "h_REVERT"
    , opcodes := [0xfd]
    , preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 returnRevertMemoryGasAsm "revert" sparseWindows
    , body    := []
    , tail    := .custom <|
        -- GH #10981: REVERT restores log cursors from the per-depth body slab
        -- (offsets +40 persistent, +56 event — bodyStateCaptureCursorsAsm), not
        -- from env+456/+480. Those cells duplicated the slab; CallFrameReturn
        -- already reads the slab. Transient zero at 464 is unchanged (prior
        -- behaviour). Depth d = evm_call_depth (still the reverting frame).
        returnRevertTail 2
          ("  la t0, evm_call_depth; ld t0, 0(t0); " ++
           bodyStateSlabStrideOps "t0" "t1" "t2" ++
           "; la t2, body_state_snapshot_by_depth; add t2, t2, t1\n" ++
           "  ld x17, 40(t2)\n" ++
           "  sd x17, 448(x20)\n" ++
           "  sd x0, 464(x20)\n" ++
           "  ld x17, 56(t2)\n" ++
           "  sd x17, 472(x20)\n") depthAware sparseWindows }
  , { label := "h_INVALID", opcodes := [0xfe]
    , body := []
    , tail := .custom (dispatchHaltRet 3) }
  , { label := "h_SELFDESTRUCT", opcodes := [0xff]
    , preBody := stackUnderflowGuardAsm 1 ++ "\n" ++ staticContextWriteGuardAsm
    , body := []
    , tail := .custom selfdestructTailAsm } ]

end EvmAsm.Codegen
