/-
  EvmAsm.Codegen.Programs.CreateFrameDescend

  `create_frame_descend` (bead fhsxz.2.4.2.61.8.3.5.1, the .5a slice) — enter a REAL
  child frame to execute CREATE/CREATE2 init code through the full dispatch loop,
  replacing the bounded mini-interpreter (`create_execute_initcode_frame`, which only
  supports STOP/MSTORE/MSTORE8/PUSH/RETURN/REVERT/INVALID and cannot run real
  constructors that SSTORE / do arithmetic / CODECOPY).

  It REUSES the proven CALL descent primitive `call_frame_descend` (CallFrameDescend.lean):
  that already does frame_depth_push + call_frame_enter (register rebase + fresh-zero
  child memory) + call_frame_set_call_env + gas forwarding + witness/log-state copy +
  the live-register switch, all driven by a 96-byte `cd_desc`. For CREATE the env is
  exactly `call_frame_set_call_env` mode 0 (CALL): the child's ADDRESS = the derived
  CREATE address (so init-code SSTOREs key on the created account), CALLER = the creator
  (parent.ADDRESS), CALLVALUE = the endowment. The child's code = the staged init code
  (`create_child_initcode` / `create_init_size`); there is no calldata (argsLen = 0).

  After the descent it marks the child frame as a CREATE-frame in `create_frame_flag`
  (indexed by depth) so the depth-aware RETURN/STOP/REVERT handler (.5b) can deposit the
  returned bytes as the deployed code + push the derived address, instead of CALL's
  copy-returndata + push-success.

  Calling convention (from the CREATE tail at .5c, after the address is derived and the
  init code is staged):
    a1 = netPopBytes (64 for CREATE / 96 for CREATE2) for frame_return's arg pop.
  The endowment value is the stack top (x12+0), read from x12 directly -- NOT passed in a0,
  because a0 == x10 (the dispatcher PC) which call_frame_descend saves as the parent return PC.
  Reads `create_address_be` (20-byte BE derived address) and `create_child_initcode` /
  `create_init_size`. Switches the live dispatcher registers to the child frame and
  returns; the caller then `j .dispatch_loop` to run the init code. Clobbers t0-t4, a0-a7.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Per-depth CREATE-frame flag capacity (one u64 per call-frame depth). -/
def createFrameFlagDepths : Nat := 1025

/-! ## create_frame_descend -/
def createFrameDescendFunction : String :=
  "create_frame_descend:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  -- drj99.1 (failed-inner rollback): disarm the value-CALL non-storage pre-snapshot so this CREATE
  -- descent uses the LIVE effect count for the child env snapshot (its endowment/creator effects are
  -- recorded INSIDE the child at the RETURN deposit, after the snapshot). Clears a stale arm left by
  -- a prior value-CALL that armed then routed to .Lcd_empty/.Lcd_fail without descending.
  "  la t0, cd_nse_presnap_armed; sd x0, 0(t0)\n" ++
  -- NB: do NOT take the endowment ptr in a0 -- a0 == x10 (the dispatcher PC), and
  -- call_frame_descend below saves x10 as the parent return PC (#8608/#8629 lesson).
  -- The CREATE value operand is the stack top (x12+0), so read it from x12 directly.
  -- 1. derived address create_address_be (20B BE, bytes 0..19) -> create_address_word
  --    (32B EVM-stack word, LE): reverse the 20 big-endian bytes, low-aligned.
  "  la t0, create_address_word\n" ++
  "  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, create_address_be; addi t1, t1, 19\n" ++
  "  mv t2, t0; li t3, 20\n" ++
  ".Lcfd_revaddr:\n" ++
  "  beqz t3, .Lcfd_revaddr_d\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lcfd_revaddr\n" ++
  ".Lcfd_revaddr_d:\n" ++
  -- 2. build the CREATE cd_desc (same 96-byte layout call_frame_descend reads).
  "  la t2, create_cd_desc\n" ++
  "  la t3, create_address_word; sd t3, 0(t2)      # to_ptr = derived address (child ADDRESS)\n" ++
  "  sd x12, 8(t2)                                  # value_ptr = x12 (CREATE value operand at stack top) -> child CALLVALUE\n" ++
  "  sd x0, 16(t2)                                  # mode 0 (CALL env: ADDRESS=to, CALLER=parent, CALLVALUE=value)\n" ++
  "  sd x0, 24(t2); sd x0, 32(t2)                   # argsOff / argsLen = 0 (CREATE child has no calldata)\n" ++
  "  sd x0, 40(t2); sd x0, 48(t2)                   # outOff / outSize = 0 (deposit handles RETURN, not frame_return)\n" ++
  "  sd a1, 56(t2)                                  # netPopBytes (from a1: 64 for CREATE / 96 for CREATE2) -- frame_return pops the args\n" ++
  "  la t3, create_child_initcode; sd t3, 64(t2)    # code_ptr = staged init code\n" ++
  "  la t3, create_init_size; ld t3, 0(t3); sd t3, 72(t2)   # code_len\n" ++
  "  ld t3, 568(x20); sd t3, 80(t2)                 # requested_gas = all gas_left (EIP-150 63/64 cap in forward_gas)\n" ++
  "  sd x0, 88(t2)                                  # value_nonzero = 0 (CREATE charges its own gas, not CALL's 9000 transfer)\n" ++
  -- 3. descend: call_frame_descend switches x10/x12/x13/x20/x21 to the child frame.
  "  la a1, create_cd_desc\n" ++
  "  jal ra, call_frame_descend\n" ++
  -- 4. mark the (now-current) child frame as a CREATE-frame for the .5b return handler.
  "  la t0, evm_call_depth; ld t1, 0(t0)            # child depth (post-push)\n" ++
  "  la t0, create_frame_flag; slli t1, t1, 3; add t0, t0, t1\n" ++
  "  li t2, 1; sd t2, 0(t0)\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
  "  ret"

/-- Data for `create_frame_descend`: the CREATE cd_desc, the stack-word form of the
    derived address, and the per-depth CREATE-frame flag. Linked into every dispatcher
    closure whose CREATE tail descends (co-located with `cd_desc` / the create child data). -/
def createFrameDescendData : String :=
  ".balign 8\n" ++
  "create_cd_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "create_address_word:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "create_frame_flag:\n  .zero " ++ toString (createFrameFlagDepths * 8) ++ "\n"

end EvmAsm.Codegen
