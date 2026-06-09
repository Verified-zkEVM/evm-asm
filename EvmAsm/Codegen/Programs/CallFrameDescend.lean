/-
  EvmAsm.Codegen.Programs.CallFrameDescend

  `call_frame_enter` — the child-frame entry primitive for the CALL/CREATE
  descent (bead fhsxz.2.4.2.61.6.5). It composes the merged layout primitives
  `frame_base` (#8516) and `frame_depth_*` (#8517) into the register rebase +
  child-memory zero-init a CALL/STATICCALL descent performs once the
  depth/balance/static gate passes. The env setup, gas forwarding, calldata
  aliasing, and the dispatch re-entry / return are the remaining descent steps
  (still in NoopChildFrame, .61.6); this isolates the register/memory core so it
  is unit-verified (probe `zisk_call_descend`) BEFORE it is wired into the
  verdict-critical dispatcher path.

  Layout offsets from `CallFrameLayout` (docs/call-frame-memory-layout.md §4):
  `frameMemOff = 0`, `frameStackTopOff = 0x18200`, `frameEnvOff = 0x28400`,
  `FRAME_STRIDE = 0x29000`. Per the non-uniform layout, this helper is for
  child depth `d >= 1` (frame[0] keeps the existing `evm_memory`/stack/env).

  HARD soundness requirement (docs §1, §5): the child slot aliases the
  replay-dirtied BAL union, so the child's 64 KiB EVM memory is NOT zero — it
  must be zeroed on every descent (EVM fresh-zero-per-frame semantics; also the
  runtime relies on EVM memory reading as zero for `evm_mload` beyond MSIZE and
  the `.data` calldata-zero assumption).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.CallFrameBase
import EvmAsm.Codegen.Programs.CallFrameSwitch

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `call_frame_enter(a0 = child depth d >= 1)`: rebase the per-frame registers
    onto child `frame[d]` and zero-init its EVM memory. Returns
    `a0 = child memBase` (x13 = `frame_base(d) + frameMemOff`),
    `a1 = child stack top` (x12 = `frame_base(d) + frameStackTopOff`),
    `a2 = child env base` (x20 = `frame_base(d) + frameEnvOff`).
    The caller saves the parent's pc/codebase via `frame_save_regs` before
    calling and re-points x13/x12/x20 from the returns. Clobbers t0/t1. -/
def callFrameEnterFunction : String :=
  "call_frame_enter:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  jal ra, frame_base                 # a0 = call_frame_arena + (d-1)*0x29000\n" ++
  "  mv s0, a0                          # s0 = child slot base (frameMemOff = 0)\n" ++
  -- Zero-init the child's 64 KiB EVM memory [base, base + 0x10000).
  "  mv t0, s0\n" ++
  "  li t1, 0x10000\n" ++
  ".Lcfe_zero:\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -8\n" ++
  "  bnez t1, .Lcfe_zero\n" ++
  -- Child register bases.
  "  mv a0, s0                          # x13 = base + frameMemOff (0)\n" ++
  "  li t0, 0x18200\n" ++
  "  add a1, s0, t0                     # x12 = base + frameStackTopOff\n" ++
  "  li t0, 0x28400\n" ++
  "  add a2, s0, t0                     # x20 = base + frameEnvOff\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16\n" ++
  "  ret"

/-- `call_frame_set_call_env(a0 = child env base, a1 = parent env base,
    a2 = to-word ptr, a3 = value-word ptr, a4 = mode)`: set the child frame's
    per-frame env call-context for one of the four message-call kinds. `a4` mode:
    `0 = CALL`, `1 = STATICCALL`, `2 = CALLCODE`, `3 = DELEGATECALL` (modes 0/1
    keep the exact prior `is_static` behavior, so the descend path and the
    `zisk_call_frame_descend` probe are byte-identical). The three 32-byte words,
    per execution-specs `vm/instructions/system.py` (the current_target / caller /
    value roles):

      mode          ADDRESS (env+0)   CALLER (env+64)    CALLVALUE (env+96)
      0 CALL        to                parent.ADDRESS     value
      1 STATICCALL  to                parent.ADDRESS     0
      2 CALLCODE    parent.ADDRESS    parent.ADDRESS     value
      3 DELEGATECALL parent.ADDRESS   parent.CALLER      parent.CALLVALUE

    CALLCODE/DELEGATECALL run the `to` code in the CALLER's storage context, so
    `current_target` (ADDRESS) stays the parent's; DELEGATECALL further inherits
    the parent's msg.sender (CALLER) and value (CALLVALUE). The callee CODE comes
    from `to` either way — that is the descent's code resolution, not this helper.
    Offsets per the per-frame env layout (docs §3). Clobbers t0/t1. -/
def callFrameSetCallEnvFunction : String :=
  "call_frame_set_call_env:\n" ++
  -- ADDRESS (env+0): mode >= 2 (CALLCODE/DELEGATECALL) -> parent.ADDRESS, else to.
  "  li t1, 2\n" ++
  "  bgeu a4, t1, .Lcfsce_addr_self\n" ++
  "  ld t0, 0(a2); sd t0, 0(a0)\n" ++
  "  ld t0, 8(a2); sd t0, 8(a0)\n" ++
  "  ld t0, 16(a2); sd t0, 16(a0)\n" ++
  "  ld t0, 24(a2); sd t0, 24(a0)\n" ++
  "  j .Lcfsce_caller\n" ++
  ".Lcfsce_addr_self:\n" ++
  "  ld t0, 0(a1); sd t0, 0(a0)\n" ++
  "  ld t0, 8(a1); sd t0, 8(a0)\n" ++
  "  ld t0, 16(a1); sd t0, 16(a0)\n" ++
  "  ld t0, 24(a1); sd t0, 24(a0)\n" ++
  ".Lcfsce_caller:\n" ++
  -- CALLER (env+64): mode == 3 (DELEGATECALL) -> parent.CALLER, else parent.ADDRESS.
  "  li t1, 3\n" ++
  "  beq a4, t1, .Lcfsce_caller_inherit\n" ++
  "  ld t0, 0(a1);  sd t0, 64(a0)\n" ++
  "  ld t0, 8(a1);  sd t0, 72(a0)\n" ++
  "  ld t0, 16(a1); sd t0, 80(a0)\n" ++
  "  ld t0, 24(a1); sd t0, 88(a0)\n" ++
  "  j .Lcfsce_value\n" ++
  ".Lcfsce_caller_inherit:\n" ++
  "  ld t0, 64(a1); sd t0, 64(a0)\n" ++
  "  ld t0, 72(a1); sd t0, 72(a0)\n" ++
  "  ld t0, 80(a1); sd t0, 80(a0)\n" ++
  "  ld t0, 88(a1); sd t0, 88(a0)\n" ++
  ".Lcfsce_value:\n" ++
  -- CALLVALUE (env+96): mode 1 (STATICCALL) -> 0; mode 3 (DELEGATECALL) ->
  -- parent.CALLVALUE; else (CALL/CALLCODE) -> value.
  "  li t1, 1\n" ++
  "  beq a4, t1, .Lcfsce_value_zero\n" ++
  "  li t1, 3\n" ++
  "  beq a4, t1, .Lcfsce_value_inherit\n" ++
  "  ld t0, 0(a3);  sd t0, 96(a0)\n" ++
  "  ld t0, 8(a3);  sd t0, 104(a0)\n" ++
  "  ld t0, 16(a3); sd t0, 112(a0)\n" ++
  "  ld t0, 24(a3); sd t0, 120(a0)\n" ++
  "  ret\n" ++
  ".Lcfsce_value_zero:\n" ++
  "  sd zero, 96(a0); sd zero, 104(a0); sd zero, 112(a0); sd zero, 120(a0)\n" ++
  "  ret\n" ++
  ".Lcfsce_value_inherit:\n" ++
  "  ld t0, 96(a1);  sd t0, 96(a0)\n" ++
  "  ld t0, 104(a1); sd t0, 104(a0)\n" ++
  "  ld t0, 112(a1); sd t0, 112(a0)\n" ++
  "  ld t0, 120(a1); sd t0, 120(a0)\n" ++
  "  ret"

/-- `call_frame_set_calldata(a0 = child env base, a1 = parent mem base,
    a2 = argsOff, a3 = argsLen)`: alias the child's calldata view into the
    parent frame's memory — `callDataPtr@416 = parent_mem + argsOff`,
    `callDataLen@424 = argsLen`. No copy: the parent frame slot persists
    (strictly shallower index) while the child runs, so CALLDATALOAD/COPY read
    directly from it. Clobbers t0. -/
def callFrameSetCalldataFunction : String :=
  "call_frame_set_calldata:\n" ++
  "  add t0, a1, a2\n" ++
  "  sd t0, 416(a0)\n" ++
  "  sd a3, 424(a0)\n" ++
  "  ret"

/-- `call_frame_forward_gas(a0 = gas_left, a1 = requested, a2 = value_nonzero)`:
    EIP-150 message-call gas forwarding (`vm/gas.py:419,424,64,415`). Returns
    `a0 = min(requested, gas_left - gas_left/64) + (value_nonzero ? 2300 : 0)`.
    `gas_left` is the caller's gas AFTER the memory-expansion + access cost is
    charged; the all-but-1/64 cap leaves the caller 1/64; the `CALL_STIPEND`
    (2300) is added to the callee for value-bearing CALL/CALLCODE and is NOT
    charged to the caller (a gift). Clobbers t0/t1. -/
def callFrameForwardGasFunction : String :=
  "call_frame_forward_gas:\n" ++
  "  srli t0, a0, 6\n" ++                 -- gas_left / 64
  "  sub t1, a0, t0\n" ++                 -- max_message_call_gas = gas_left - gas_left/64
  "  bltu a1, t1, .Lcffg_min\n" ++        -- requested < max -> use requested
  "  j .Lcffg_stipend\n" ++               -- else keep max in t1
  ".Lcffg_min:\n" ++
  "  mv t1, a1\n" ++
  ".Lcffg_stipend:\n" ++
  "  mv a1, t1\n" ++                      -- a1 = cost = capped forwarded gas (PRE-stipend) =
                                          -- the EIP-150 caller charge (stipend is a callee gift)
  "  beqz a2, .Lcffg_done\n" ++
  "  li t0, 2300\n" ++                    -- CALL_STIPEND (> addi imm range)
  "  add t1, t1, t0\n" ++
  ".Lcffg_done:\n" ++
  "  mv a0, t1\n" ++                      -- a0 = sub_call = capped + stipend = callee gas
  "  ret"

/-- `call_frame_descend(a1 = &desc)`: orchestrate one CALL/STATICCALL descent
    (depth d → d+1). `&desc` is passed in a1 (x11) so it does not alias the live
    PARENT dispatcher registers this routine reads (x10 pc, x21 code base, x12
    stack top, x13 memory base, x20 env base). The caller-filled descriptor:

      desc+0   to_ptr        (32-byte call target address word)
      desc+8   value_ptr     (32-byte call value word; ignored when is_static)
      desc+16  is_static     (0/1)
      desc+24  argsOff        (calldata offset in parent memory)
      desc+32  argsLen        (calldata length)
      desc+40  outOff         (return-output offset in parent memory)
      desc+48  outSize        (return-output cap)
      desc+56  netPopBytes    (CALL 192 / STATICCALL 160 — args popped on return)
      desc+64  code_ptr       (resolved callee bytecode ptr; caller resolves via
                               code_at_state_root_address using env+576..616)
      desc+72  code_len       (callee bytecode length)
      desc+80  requested_gas  (the CALL gas stack arg, u64)
      desc+88  value_nonzero  (0/1; 0 for STATICCALL / zero value)

    Effect (in order):
      1. `frame_save_regs(parent_depth, parent_pc, parent_code_base)`;
      2. `frame_depth_push` → child depth d;
      3. save the return-context `frame_call_ctx[d]` = (parent_x12,
         outOff_abs = parent_mem + outOff, outSize, netPopBytes) for `frame_return`;
      4. `call_frame_enter(d)` → child memory/stack/env bases (+ child mem zero-init);
      5. `call_frame_set_call_env` (ADDRESS=to, CALLER=parent.ADDRESS, CALLVALUE);
      6. `call_frame_set_calldata` (alias child calldata into parent memory);
      7. `call_frame_forward_gas` (EIP-150 63/64 + stipend) → child env.gasRemaining;
      8. copy the witness context env+576..616 (header/state/codes ptrs+lens) so the
         child's by-address handlers (BALANCE/EXTCODE*/the next descent) resolve;
      9. set the child code base x21=x10=code_ptr (PC at code[0]) and
         env.codeSize (env+496) = code_len.

    On return the live dispatcher registers are repointed to the child frame and
    `evm_call_depth` is bumped; the caller (the CALL handler) then `j .dispatch_loop`.
    This helper does NOT charge the parent's gas / value-transfer costs (the gate
    side of the handler does) and does NOT itself jump, so it is unit-probeable.
    NB: s4/s5 ARE x20/x21 (env/code base) — this routine keeps parent state in
    s0-s3/s6-s9 and never uses s4/s5 as scratch. Clobbers t0-t2, a0-a4. -/
def callFrameDescendFunction : String :=
  "call_frame_descend:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s6, 40(sp); sd s7, 48(sp); sd s8, 56(sp); sd s9, 64(sp)\n" ++
  "  sd s10, 72(sp); sd s11, 80(sp)\n" ++
  -- &desc arrives in a1 (x11) so it does NOT alias x10/x12/x13/x20/x21 (the live
  -- parent PC/stack/mem/env/code-base, which this routine reads first).
  "  mv s7, a1                      # &desc\n" ++
  "  mv s0, x10                     # parent pc\n" ++
  "  mv s6, x21                     # parent code base\n" ++
  "  mv s1, x12                     # parent stack top (args)\n" ++
  "  mv s2, x13                     # parent memory base\n" ++
  "  mv s3, x20                     # parent env base\n" ++
  -- 1. save parent pc/code-base for the matching return.
  "  la t0, evm_call_depth; ld a0, 0(t0)   # a0 = parent depth\n" ++
  "  mv a1, s0; mv a2, s6\n" ++
  "  jal ra, frame_save_regs\n" ++
  -- 2. bump depth -> d.
  "  jal ra, frame_depth_push       # a0 = child depth d\n" ++
  "  mv s8, a0\n" ++
  -- 3. save the return-context frame_call_ctx[d].
  "  la t0, frame_call_ctx\n" ++
  "  slli t1, s8, 5                 # d * 32\n" ++
  "  add t0, t0, t1\n" ++
  "  sd s1, 0(t0)                   # parent_x12\n" ++
  "  ld t2, 40(s7); add t2, s2, t2  # outOff_abs = parent_mem + outOff\n" ++
  "  sd t2, 8(t0)\n" ++
  "  ld t2, 48(s7); sd t2, 16(t0)   # outSize\n" ++
  "  ld t2, 56(s7); sd t2, 24(t0)   # netPopBytes\n" ++
  -- 4. enter the child frame (rebase + zero-init). Stash the returned child
  --    mem/stack/env bases in callee-saved regs — the helper calls below clobber
  --    a0-a4 (= x10/x11/x12/x13/x14), so the live dispatcher regs are set LAST.
  "  mv a0, s8; jal ra, call_frame_enter\n" ++
  "  mv s10, a0                     # child memory base\n" ++
  "  mv s11, a1                     # child stack top\n" ++
  "  mv s9, a2                      # child env base\n" ++
  -- 5. child call-context env (ADDRESS / CALLER / CALLVALUE).
  "  mv a0, s9; mv a1, s3\n" ++
  "  ld a2, 0(s7)                   # to_ptr\n" ++
  "  ld a3, 8(s7)                   # value_ptr\n" ++
  "  ld a4, 16(s7)                  # is_static\n" ++
  "  jal ra, call_frame_set_call_env\n" ++
  -- 6. alias child calldata into the (still-live) parent memory.
  "  mv a0, s9; mv a1, s2\n" ++
  "  ld a2, 24(s7)                  # argsOff\n" ++
  "  ld a3, 32(s7)                  # argsLen\n" ++
  "  jal ra, call_frame_set_calldata\n" ++
  -- 7a. EIP-150 transfer_gas_cost: a value-bearing CALL/CALLCODE charges
  -- GAS_CALL_VALUE (9000) BEFORE the 63/64 forwarding cap (it is part of
  -- extra_gas, deducted from gas_left first). Persist it to the parent so the
  -- forward cap below sees the reduced gas_left and the cost deduction follows it.
  "  ld a2, 88(s7)\n" ++
  "  beqz a2, .Lcfd_no_transfer\n" ++
  "  ld t0, 568(s3)\n" ++
  "  li t1, 9000\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(s3)\n" ++
  ".Lcfd_no_transfer:\n" ++
  -- 7. EIP-150 forwarded gas -> child env.gasRemaining (env+568).
  "  ld a0, 568(s3)                 # parent gas_left (after transfer charge)\n" ++
  "  ld a1, 80(s7)                  # requested_gas\n" ++
  "  ld a2, 88(s7)                  # value_nonzero\n" ++
  "  jal ra, call_frame_forward_gas\n" ++
  "  sd a0, 568(s9)                 # child env.gasRemaining = sub_call (capped + stipend)\n" ++
  -- EIP-150: deduct the caller charge (cost = capped forwarded gas, a1) from the
  -- parent's gasRemaining. cost <= gas_left - gas_left/64 < gas_left, so no OOG.
  -- frame_return refunds the child's UNUSED gas to the parent on the matching pop.
  "  ld t0, 568(s3)\n" ++
  "  sub t0, t0, a1\n" ++
  "  sd t0, 568(s3)\n" ++
  -- 8. copy witness context (header/state/codes ptr+len) parent env -> child env.
  "  ld t0, 576(s3); sd t0, 576(s9)\n" ++
  "  ld t0, 584(s3); sd t0, 584(s9)\n" ++
  "  ld t0, 592(s3); sd t0, 592(s9)\n" ++
  "  ld t0, 600(s3); sd t0, 600(s9)\n" ++
  "  ld t0, 608(s3); sd t0, 608(s9)\n" ++
  "  ld t0, 616(s3); sd t0, 616(s9)\n" ++
  -- 8b. initialize the child env execution-state cells. The child env lives in the
  -- BAL-replay-dirtied arena, so its log/memory-state words are garbage — without
  -- this a child MSTORE/SSTORE reads junk. Continue the (shared) persistent/transient
  -- logs from the parent's current length (so child writes append and a child REVERT
  -- rolls back to here), and reset the child's memory size to 0 (fresh 64 KiB).
  "  ld t0, 448(s3); sd t0, 448(s9)   # persistentLogLength (continue global log)\n" ++
  "  sd t0, 456(s9)                    # persistentLogCheckpoint = current (REVERT point)\n" ++
  "  ld t0, 464(s3); sd t0, 464(s9)   # transientLogLength\n" ++
  "  ld t0, 472(s3); sd t0, 472(s9)   # eventLogLength\n" ++
  "  sd t0, 480(s9)                    # eventLogCheckpoint = current\n" ++
  "  sd x0, 488(s9)                    # activeMemorySize = 0 (fresh child memory)\n" ++
  -- 9. child env.codeSize (env+496).
  "  ld t0, 72(s7); sd t0, 496(s9)\n" ++
  -- 10. frame-relative stack bounds: point the under/overflow guards at the
  --     CHILD arena stack. cur_top = child stack top (s11 = base+0x18200);
  --     cur_low = cur_top - 1024*32 (0x8000), the bottom of the child's arena.
  "  la t0, evm_cur_stack_top\n" ++
  "  sd s11, 0(t0)\n" ++
  "  li t1, 0x8000\n" ++
  "  sub t1, s11, t1                # child stack low = top - 1024*32\n" ++
  "  la t0, evm_cur_stack_low\n" ++
  "  sd t1, 0(t0)\n" ++
  -- 11. set the live dispatcher registers to the child frame (done last).
  "  mv x13, s10                    # child memory base\n" ++
  "  mv x12, s11                    # child stack top\n" ++
  "  mv x20, s9                     # child env base\n" ++
  "  ld t0, 64(s7)                  # code_ptr\n" ++
  "  mv x21, t0                     # child code base\n" ++
  "  mv x10, t0                     # child PC at code[0]\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s6, 40(sp); ld s7, 48(sp); ld s8, 56(sp); ld s9, 64(sp)\n" ++
  "  ld s10, 72(sp); ld s11, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_call_descend`: unit-probe for `call_frame_enter` over a local
    `call_frame_arena` stub. Pushes depth 0->1, pre-dirties the child slot,
    enters the frame, and checks the rebased register bases + the memory
    zero-init.
    Output:
      +0  depth after push from 0            (expect 1)
      +8  child x13 (= frame_base(1))         (expect call_frame_arena)
      +16 child x12                           (= base + 0x18200)
      +24 child x20                           (= base + 0x28400)
      +32 child mem[0] after zero-init        (expect 0, was pre-dirtied)
      +40 x12 - x13                           (expect 0x18200)
      +48 x20 - x13                           (expect 0x28400)
      +56 x13 - call_frame_arena              (expect 0 — depth 1 slot) -/
def ziskCallDescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  jal ra, frame_depth_push\n" ++          -- depth 0 -> 1, a0 = 1
  "  sd a0, 0(s0)\n" ++
  -- Pre-dirty the child slot's first word so the zero-init is observable.
  "  li a0, 1; jal ra, frame_base\n" ++
  "  li t0, 0x1234567; sd t0, 0(a0)\n" ++
  -- Enter the child frame at depth 1.
  "  li a0, 1; jal ra, call_frame_enter\n" ++
  "  sd a0, 8(s0)\n" ++
  "  sd a1, 16(s0)\n" ++
  "  sd a2, 24(s0)\n" ++
  "  ld t0, 0(a0); sd t0, 32(s0)\n" ++
  "  sub t1, a1, a0; sd t1, 40(s0)\n" ++
  "  sub t1, a2, a0; sd t1, 48(s0)\n" ++
  "  la t0, call_frame_arena; sub t1, a0, t0; sd t1, 56(s0)\n" ++
  -- Env setup test: child env = call_frame_arena + frameEnvOff (0x28400) for depth 1.
  "  la a0, call_frame_arena; li t0, 0x28400; add a0, a0, t0\n" ++
  "  la a1, cfd_parent_env\n" ++
  "  la a2, cfd_to_word\n" ++
  "  la a3, cfd_value_word\n" ++
  "  li a4, 0\n" ++                          -- CALL (not static)
  "  jal ra, call_frame_set_call_env\n" ++
  "  ld t0, 0(a0); sd t0, 64(s0)\n" ++       -- child ADDRESS limb0 (expect 0xaaaaaaaa = to)
  "  ld t0, 64(a0); sd t0, 72(s0)\n" ++      -- child CALLER limb0 (expect 0xbbbbbbbb = parent ADDRESS)
  "  ld t0, 96(a0); sd t0, 80(s0)\n" ++      -- child CALLVALUE limb0 (expect 0xcccccccc = value)
  "  la a0, call_frame_arena; li t0, 0x28400; add a0, a0, t0\n" ++
  "  la a1, cfd_parent_env; la a2, cfd_to_word; la a3, cfd_value_word; li a4, 1\n" ++  -- STATICCALL
  "  jal ra, call_frame_set_call_env\n" ++
  "  ld t0, 96(a0); sd t0, 88(s0)\n" ++      -- child CALLVALUE limb0 (expect 0 = static)
  -- Calldata alias test: child callDataPtr@416 = parent_mem + argsOff, len@424.
  "  la a0, call_frame_arena; li t0, 0x28400; add a0, a0, t0\n" ++
  "  la a1, call_frame_arena; li a2, 0x40; li a3, 0x20\n" ++
  "  jal ra, call_frame_set_calldata\n" ++
  "  ld t0, 416(a0); la t1, call_frame_arena; sub t0, t0, t1; sd t0, 96(s0)\n" ++  -- expect 0x40
  "  ld t0, 424(a0); sd t0, 104(s0)\n" ++                                          -- expect 0x20
  -- Gas forward test (EIP-150 63/64 + stipend).
  "  li a0, 6400; li a1, 100000; li a2, 0; jal ra, call_frame_forward_gas; sd a0, 112(s0)\n" ++  -- 6300
  "  li a0, 6400; li a1, 1000; li a2, 1; jal ra, call_frame_forward_gas; sd a0, 120(s0)\n" ++    -- 3300
  "  li a0, 64; li a1, 100; li a2, 0; jal ra, call_frame_forward_gas; sd a0, 128(s0)\n" ++       -- 63
  "  j .Lcd_done\n" ++
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  callFrameSetCalldataFunction ++ "\n" ++
  callFrameForwardGasFunction ++ "\n" ++
  ".Lcd_done:"

/-- Local stubs so the probe links standalone (the real `call_frame_arena`
    lives in the guest's `BlockVerdictDataSection`; `evm_call_depth` in the
    embedded helper data). The arena stub holds one frame slot. -/
def ziskCallDescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "cfd_parent_env:\n  .quad 0xbbbbbbbb, 0, 0, 0\n" ++   -- parent ADDRESS@0
  "cfd_to_word:\n  .quad 0xaaaaaaaa, 0, 0, 0\n" ++       -- call target
  "cfd_value_word:\n  .quad 0xcccccccc, 0, 0, 0\n"       -- call value

def ziskCallDescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCallDescendPrologue
  dataAsm     := ziskCallDescendDataSection
}

/-- `zisk_call_frame_descend`: end-to-end probe for `call_frame_descend`. Sets up
    a depth-0 parent frame (regs + env with witness context) and a call descriptor
    (value-bearing CALL into a codelen-0x33 callee), descends, then records the full
    child-frame setup so a script can assert every field the descent writes.

    Output (each u64):
      +0   evm_call_depth after            (expect 1)
      +8   frame_save_area[0].pc           (expect 0x500 parent pc)
      +16  frame_save_area[0].codebase     (expect 0x600 parent cb)
      +24  ctx[1].parent_x12 - &pstack     (expect 0)
      +32  ctx[1].outOff_abs - &pmem       (expect 0x100)
      +40  ctx[1].outSize                  (expect 0x20)
      +48  ctx[1].netPopBytes              (expect 192)
      +56  child x13 - &call_frame_arena   (expect 0   = frame_base(1)+frameMemOff)
      +64  child x20 - &call_frame_arena   (expect 0x28400 = +frameEnvOff)
      +72  child x21 - &cfd2_code          (expect 0   = callee code base)
      +80  child x10 - &cfd2_code          (expect 0   = child PC at code[0])
      +88  child env.ADDRESS limb0         (expect 0xbb = to)
      +96  child env.CALLER limb0          (expect 0xaa = parent ADDRESS)
      +104 child env.CALLVALUE limb0       (expect 0x7  = value)
      +112 child env.callDataPtr - &pmem   (expect 0x40 = argsOff)
      +120 child env.callDataLen           (expect 0x20 = argsLen)
      +128 child env.gasRemaining          (expect 3300 = min(1000,98438)+2300)
      +136 child env.codeSize              (expect 0x33)
      +144 child env witness.state ptr     (expect 0x592 marker, copied env+592)
      +152 evm_cur_stack_top - &arena      (expect 0x18200 = child frame stack top)
      +160 evm_cur_stack_low - &arena      (expect 0x10200 = top - 1024*32)
      +168 parent env.gasRemaining        (expect 90000 = 100000 - transfer 9000 - cost 1000) -/
def ziskCallFrameDescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_call_depth; sd x0, 0(t0)\n" ++
  -- parent env: ADDRESS@0, gasRemaining@568, witness state ptr marker @592.
  "  la t0, cfd2_penv\n" ++
  "  li t1, 0xaa; sd t1, 0(t0)\n" ++
  "  li t1, 100000; sd t1, 568(t0)\n" ++
  "  li t1, 0x592; sd t1, 592(t0)\n" ++
  -- to / value words.
  "  la t0, cfd2_to; li t1, 0xbb; sd t1, 0(t0)\n" ++
  "  la t0, cfd2_val; li t1, 0x7; sd t1, 0(t0)\n" ++
  -- descriptor.
  "  la t0, cfd2_desc\n" ++
  "  la t1, cfd2_to;  sd t1, 0(t0)\n" ++
  "  la t1, cfd2_val; sd t1, 8(t0)\n" ++
  "  sd x0, 16(t0)\n" ++                       -- is_static = 0
  "  li t1, 0x40; sd t1, 24(t0)\n" ++          -- argsOff
  "  li t1, 0x20; sd t1, 32(t0)\n" ++          -- argsLen
  "  li t1, 0x100; sd t1, 40(t0)\n" ++         -- outOff
  "  li t1, 0x20; sd t1, 48(t0)\n" ++          -- outSize
  "  li t1, 192; sd t1, 56(t0)\n" ++           -- netPopBytes
  "  la t1, cfd2_code; sd t1, 64(t0)\n" ++     -- code_ptr
  "  li t1, 0x33; sd t1, 72(t0)\n" ++          -- code_len
  "  li t1, 1000; sd t1, 80(t0)\n" ++          -- requested_gas
  "  li t1, 1; sd t1, 88(t0)\n" ++             -- value_nonzero
  -- live parent registers.
  "  li x10, 0x500\n" ++
  "  li x21, 0x600\n" ++
  "  la x12, cfd2_pstack\n" ++
  "  la x13, cfd2_pmem\n" ++
  "  la x20, cfd2_penv\n" ++
  "  la a1, cfd2_desc\n" ++          -- &desc in a1 (x11), not a0 (x10 = parent PC)
  "  jal ra, call_frame_descend\n" ++
  -- child env fields (x20 = child env base after descent).
  "  ld t0, 0(x20);   sd t0, 88(s0)\n" ++
  "  ld t0, 64(x20);  sd t0, 96(s0)\n" ++
  "  ld t0, 96(x20);  sd t0, 104(s0)\n" ++
  "  la t1, cfd2_pmem; ld t0, 416(x20); sub t0, t0, t1; sd t0, 112(s0)\n" ++
  "  ld t0, 424(x20); sd t0, 120(s0)\n" ++
  "  ld t0, 568(x20); sd t0, 128(s0)\n" ++
  "  ld t0, 496(x20); sd t0, 136(s0)\n" ++
  "  ld t0, 592(x20); sd t0, 144(s0)\n" ++
  -- child register bases.
  "  la t1, call_frame_arena; sub t0, x13, t1; sd t0, 56(s0)\n" ++
  "  la t1, call_frame_arena; sub t0, x20, t1; sd t0, 64(s0)\n" ++
  "  la t1, cfd2_code; sub t0, x21, t1; sd t0, 72(s0)\n" ++
  "  la t1, cfd2_code; sub t0, x10, t1; sd t0, 80(s0)\n" ++
  -- depth, save-area, and return-context.
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 0(s0)\n" ++
  "  la t0, frame_save_area; ld t1, 0(t0); sd t1, 8(s0); ld t1, 8(t0); sd t1, 16(s0)\n" ++
  "  la t0, frame_call_ctx; addi t0, t0, 32\n" ++
  "  ld t1, 0(t0); la t2, cfd2_pstack; sub t1, t1, t2; sd t1, 24(s0)\n" ++
  "  ld t1, 8(t0); la t2, cfd2_pmem; sub t1, t1, t2; sd t1, 32(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 40(s0)\n" ++
  "  ld t1, 24(t0); sd t1, 48(s0)\n" ++
  -- frame-relative stack bounds set by the descend (child arena stack).
  "  la t0, evm_cur_stack_top; ld t1, 0(t0); la t2, call_frame_arena; sub t1, t1, t2; sd t1, 152(s0)\n" ++
  "  la t0, evm_cur_stack_low; ld t1, 0(t0); la t2, call_frame_arena; sub t1, t1, t2; sd t1, 160(s0)\n" ++
  -- EIP-150: parent gas deducted by transfer (9000, value-bearing) + cost (1000) -> 90000.
  "  la t0, cfd2_penv; ld t1, 568(t0); sd t1, 168(s0)\n" ++
  "  j .Lcfd2_done\n" ++
  frameBaseFunction ++ "\n" ++
  frameDepthPushFunction ++ "\n" ++
  frameSaveRegsFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  callFrameSetCalldataFunction ++ "\n" ++
  callFrameForwardGasFunction ++ "\n" ++
  callFrameDescendFunction ++ "\n" ++
  ".Lcfd2_done:"

/-- Data stubs for the `zisk_call_frame_descend` probe (separate ELF, so it
    redefines `call_frame_arena`/`evm_call_depth` locally). -/
def ziskCallFrameDescendDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++
  ".balign 8\n" ++
  -- Frame-relative stack-bound cells (descend overwrites them; zeroed stubs here).
  "evm_cur_stack_top:\n  .zero 8\n" ++
  "evm_cur_stack_low:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "cfd2_desc:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "cfd2_penv:\n  .zero 640\n" ++
  "cfd2_pmem:\n  .zero 512\n" ++
  "cfd2_pstack:\n  .zero 256\n" ++
  "cfd2_to:\n  .zero 32\n" ++
  "cfd2_val:\n  .zero 32\n" ++
  "cfd2_code:\n  .zero 64\n"

def ziskCallFrameDescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCallFrameDescendPrologue
  dataAsm     := ziskCallFrameDescendDataSection
}

/-- `zisk_set_call_env`: focused probe for `call_frame_set_call_env`'s four
    message-call modes. Parent env markers ADDRESS@0=0xaa, CALLER@64=0xcc,
    CALLVALUE@96=0xee; to-word=0xbb, value-word=0xdd. Runs the helper into four
    distinct child env buffers (modes 0..3) and records the low limb of each
    child's ADDRESS / CALLER / CALLVALUE so a script can assert the address roles.

    Output (each u64, low limb):
      +0/+8/+16   mode 0 CALL        ADDRESS/CALLER/CALLVALUE (expect 0xbb/0xaa/0xdd)
      +24/+32/+40 mode 1 STATICCALL  (expect 0xbb/0xaa/0)
      +48/+56/+64 mode 2 CALLCODE    (expect 0xaa/0xaa/0xdd)
      +72/+80/+88 mode 3 DELEGATECALL(expect 0xaa/0xcc/0xee) -/
def ziskSetCallEnvPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- parent env markers + to/value words.
  "  la t0, sce_penv\n" ++
  "  li t1, 0xaa; sd t1, 0(t0)\n" ++
  "  li t1, 0xcc; sd t1, 64(t0)\n" ++
  "  li t1, 0xee; sd t1, 96(t0)\n" ++
  "  la t0, sce_to;  li t1, 0xbb; sd t1, 0(t0)\n" ++
  "  la t0, sce_val; li t1, 0xdd; sd t1, 0(t0)\n" ++
  -- run the helper for all four modes into distinct child env buffers.
  "  la a0, sce_child0; la a1, sce_penv; la a2, sce_to; la a3, sce_val; li a4, 0\n" ++
  "  jal ra, call_frame_set_call_env\n" ++
  "  la a0, sce_child1; la a1, sce_penv; la a2, sce_to; la a3, sce_val; li a4, 1\n" ++
  "  jal ra, call_frame_set_call_env\n" ++
  "  la a0, sce_child2; la a1, sce_penv; la a2, sce_to; la a3, sce_val; li a4, 2\n" ++
  "  jal ra, call_frame_set_call_env\n" ++
  "  la a0, sce_child3; la a1, sce_penv; la a2, sce_to; la a3, sce_val; li a4, 3\n" ++
  "  jal ra, call_frame_set_call_env\n" ++
  -- read back the low limb of ADDRESS@0 / CALLER@64 / CALLVALUE@96 for each mode.
  "  la t0, sce_child0; ld t1, 0(t0); sd t1, 0(s0); ld t1, 64(t0); sd t1, 8(s0); ld t1, 96(t0); sd t1, 16(s0)\n" ++
  "  la t0, sce_child1; ld t1, 0(t0); sd t1, 24(s0); ld t1, 64(t0); sd t1, 32(s0); ld t1, 96(t0); sd t1, 40(s0)\n" ++
  "  la t0, sce_child2; ld t1, 0(t0); sd t1, 48(s0); ld t1, 64(t0); sd t1, 56(s0); ld t1, 96(t0); sd t1, 64(s0)\n" ++
  "  la t0, sce_child3; ld t1, 0(t0); sd t1, 72(s0); ld t1, 64(t0); sd t1, 80(s0); ld t1, 96(t0); sd t1, 88(s0)\n" ++
  "  j .Lsce_done\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  ".Lsce_done:"

def ziskSetCallEnvDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sce_penv:\n  .zero 128\n" ++
  "sce_to:\n  .zero 32\n" ++
  "sce_val:\n  .zero 32\n" ++
  "sce_child0:\n  .zero 128\n" ++
  "sce_child1:\n  .zero 128\n" ++
  "sce_child2:\n  .zero 128\n" ++
  "sce_child3:\n  .zero 128\n"

def ziskSetCallEnvProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSetCallEnvPrologue
  dataAsm     := ziskSetCallEnvDataSection
}

end EvmAsm.Codegen
