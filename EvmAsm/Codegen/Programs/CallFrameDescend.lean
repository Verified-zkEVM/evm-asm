/-
  EvmAsm.Codegen.Programs.CallFrameDescend

  `call_frame_enter` — the child-frame entry primitive for the CALL/CREATE
  descent (bead fhsxz.2.4.2.61.6.5). It composes the merged layout primitives
  `frame_base` (#8516) and `frame_depth_*` (#8517) into the register rebase +
  child-memory zero-init a CALL/STATICCALL descent performs once the
  depth/balance/static gate passes. The env setup, gas forwarding, calldata
  aliasing, and the dispatch re-entry / return are the remaining descent steps
  (still in ChildFrameHandlers, .61.6); this isolates the register/memory core so it
  is unit-verified (probe `zisk_call_descend`) BEFORE it is wired into the
  verdict-critical dispatcher path.

  Layout offsets from `CallFrameLayout` (docs/call-frame-memory-layout.md §4):
  `frameStackTopOff = 0x8200`, `frameEnvOff = 0x18400`, and
  `FRAME_STRIDE = 0x19000`. Per the non-uniform layout, this helper is for
  child depth `d >= 1` (frame[0] keeps the existing `evm_memory`/stack/env).

  HARD soundness requirement (docs §1, §5): the child slot aliases the
  replay-dirtied BAL union, so the child's 128 KiB EVM memory is NOT zero — it
  must be zeroed on every descent (EVM fresh-zero-per-frame semantics; also the
  runtime relies on EVM memory reading as zero for `evm_mload` beyond MSIZE and
  the `.data` calldata-zero assumption).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.CallFrameBase
import EvmAsm.Codegen.Programs.CallFrameSwitch
import EvmAsm.Codegen.Programs.BodyStateSnapshot
import EvmAsm.Codegen.Programs.StaticContext
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `call_frame_enter(a0 = child depth d >= 1)`: rebase the per-frame registers
    onto child `frame[d]` and select its shared-pool EVM memory. Returns
    `a0 = child memBase` (pool base for depth 1, otherwise
    `parentMemBase + parentMSIZE`),
    `a1 = child stack top` (x12 = `frame_base(d) + frameStackTopOff`),
    `a2 = child env base` (x20 = `frame_base(d) + frameEnvOff`).
    The caller saves the parent's pc/codebase via `frame_save_regs` before
    calling and re-points x13/x12/x20 from the returns. Clobbers t0/t1. -/
def callFrameEnter_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_sparse_memory_next_epoch (GuestAddrs.call_frame_enter + 12)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_sparse_memory_next_epoch (GuestAddrs.call_frame_enter + 12)),
    .LD .x6 .x5 (0 : BitVec 12),
    .ADDI .x7 .x6 (1 : BitVec 12),
    .SD .x5 .x7 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.evm_sparse_memory_epoch_by_depth (GuestAddrs.call_frame_enter + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_sparse_memory_epoch_by_depth (GuestAddrs.call_frame_enter + 32)),
    .SLLI .x7 .x10 (3 : BitVec 6),
    .ADD .x5 .x5 .x7,
    .SD .x5 .x6 (0 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.frame_base (GuestAddrs.call_frame_enter + 52)),
    .MV .x8 .x10,
    .AUIPC .x5 (laHi GuestAddrs.evm_call_depth (GuestAddrs.call_frame_enter + 60)),
    .ADDI .x5 .x5 (laLo GuestAddrs.evm_call_depth (GuestAddrs.call_frame_enter + 60)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (1 : Word),
    .BEQ .x6 .x7 (40 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.frame_parent_bases (GuestAddrs.call_frame_enter + 80)),
    .ADDI .x5 .x5 (laLo GuestAddrs.frame_parent_bases (GuestAddrs.call_frame_enter + 80)),
    .SLLI .x6 .x6 (4 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .LD .x6 .x5 (0 : BitVec 12),
    .LD .x7 .x5 (8 : BitVec 12),
    .LD .x7 .x7 (488 : BitVec 12),
    .ADD .x10 .x6 .x7,
    .JAL .x0 (12 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.evm_memory_pool (GuestAddrs.call_frame_enter + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.evm_memory_pool (GuestAddrs.call_frame_enter + 116)),
    .LUI .x5 (8 : BitVec 20),
    .ADDIW .x5 .x5 (512 : BitVec 12),
    .ADD .x11 .x8 .x5,
    .LUI .x5 (24 : BitVec 20),
    .ADDIW .x5 .x5 (1024 : BitVec 12),
    .ADD .x12 .x8 .x5,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `callFrameEnter_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def callFrameEnter_relocs : RelocTable :=
  [ (3, .la .x5 "evm_sparse_memory_next_epoch"),
    (8, .la .x5 "evm_sparse_memory_epoch_by_depth"),
    (13, .jal .x1 "frame_base"),
    (15, .la .x5 "evm_call_depth"),
    (20, .la .x5 "frame_parent_bases"),
    (29, .la .x10 "evm_memory_pool") ]

def callFrameEnterFunction : String :=
  "call_frame_enter:\n" ++ emitProgramR callFrameEnter_prog callFrameEnter_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `callFrameEnter_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem callFrameEnterFunction_eq_prog :
    callFrameEnterFunction = "call_frame_enter:\n" ++ emitProgramR callFrameEnter_prog callFrameEnter_relocs := rfl

#guard callFrameEnterFunction.startsWith "call_frame_enter:\n"
#guard callFrameEnter_prog.length = 41
/-- `call_frame_set_call_env(a0 = child env base, a1 = parent env base,
    a2 = to-word ptr, a3 = value-word ptr, a4 = mode)`: set the child frame's
    per-frame env call-context for one of the four message-call kinds. `a4` mode:
    `0 = CALL`, `1 = STATICCALL`, `2 = CALLCODE`, `3 = DELEGATECALL` (modes 0/1
    set/propagate the static-context flag). The three 32-byte words,
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
  -- isStatic (env+504): STATICCALL sets it; every other call kind inherits the parent.
  "  li t1, 1\n" ++
  "  beq a4, t1, .Lcfsce_static_set\n" ++
  "  ld t0, " ++ toString staticContextFlagOff ++ "(a1)\n" ++
  "  sd t0, " ++ toString staticContextFlagOff ++ "(a0)\n" ++
  "  j .Lcfsce_addr\n" ++
  ".Lcfsce_static_set:\n" ++
  "  sd t1, " ++ toString staticContextFlagOff ++ "(a0)\n" ++
  ".Lcfsce_addr:\n" ++
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
def callFrameSetCalldata_prog : Program :=
  [ .ADD .x5 .x11 .x12,
    .SD .x10 .x5 (416 : BitVec 12),
    .SD .x10 .x13 (424 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def callFrameSetCalldataFunction : String :=
  "call_frame_set_calldata:\n" ++ emitProgram callFrameSetCalldata_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `callFrameSetCalldata_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem callFrameSetCalldataFunction_eq_prog :
    callFrameSetCalldataFunction = "call_frame_set_calldata:\n" ++ emitProgram callFrameSetCalldata_prog := rfl

#guard callFrameSetCalldataFunction.startsWith "call_frame_set_calldata:\n"
#guard callFrameSetCalldata_prog.length = 4
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
      1. charge the value-transfer gas (or consume the caller's precharge flag),
         before mutating any child-frame state;
      2. `frame_save_regs(parent_depth, parent_pc, parent_code_base)`;
      3. `frame_depth_push` → child depth d;
      4. save the return-context `frame_call_ctx[d]` = (parent_x12,
         outOff_abs = parent_mem + outOff, outSize, netPopBytes) for `frame_return`;
      5. save the parent memory/env bases in `frame_parent_bases[d]`;
      6. `call_frame_enter(d)` → child memory/stack/env bases (+ child mem zero-init);
      7. `call_frame_set_call_env` (ADDRESS=to, CALLER=parent.ADDRESS, CALLVALUE);
      8. `call_frame_set_calldata` (alias child calldata into parent memory);
      9. `call_frame_forward_gas` (EIP-150 63/64 + stipend) → child env.gasRemaining;
     10. copy the witness context env+576..616 (header/state/codes ptrs+lens) so the
         child's by-address handlers (BALANCE/EXTCODE*/the next descent) resolve;
     11. set the child code base x21=x10=code_ptr (PC at code[0]) and
         env.codeSize (env+496) = code_len.

    On return the live dispatcher registers are repointed to the child frame and
    `evm_call_depth` is bumped; the caller (the CALL handler) then `j .dispatch_loop`.
    The normal CALL handler precharges value-transfer gas before state gas and
    arms `cd_xfer_gas_precharged`; this helper consumes that flag. Direct probes
    that call this helper without the precharge still take the legacy transfer
    charge here. It does NOT itself jump, so it is unit-probeable.
    NB: s4/s5 ARE x20/x21 (env/code base) — this routine keeps parent state in
    s0-s3/s6-s9 and never uses s4/s5 as scratch. Clobbers t0-t2, a0-a4. -/
def callFrameDescendFunction : String :=
  "call_frame_descend:\n" ++
  -- execution-specs charges `message_call_gas.cost` before `generic_call`; keep
  -- the same ordering here so a transfer-charge OOG cannot consume a child
  -- frame slot or advance `evm_call_depth`. The CALL handler's one-shot flag is
  -- consumed on the same path; direct helper probes perform the charge here.
  "  ld t0, 88(a1)                  # value_nonzero\n" ++
  "  beqz t0, .Lcfd_no_transfer\n" ++
  "  la t2, cd_xfer_gas_precharged\n" ++
  "  ld t3, 0(t2)\n" ++
  "  beqz t3, .Lcfd_charge_transfer\n" ++
  "  sd x0, 0(t2)\n" ++
  "  j .Lcfd_no_transfer\n" ++
  ".Lcfd_charge_transfer:\n" ++
  "  ld t0, 568(x20)\n" ++
  "  li t1, 10300\n" ++
  "  bltu t0, t1, .exit_outofgas\n" ++
  "  sub t0, t0, t1\n" ++
  "  sd t0, 568(x20)\n" ++
  ".Lcfd_no_transfer:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s6, 40(sp); sd s7, 48(sp); sd s8, 56(sp); sd s9, 64(sp)\n" ++
  "  sd s10, 72(sp); sd s11, 80(sp)\n" ++
  -- Return a per-invocation balance-staging bit in a5. The CREATE descent
  -- consumes it immediately after this call: a set bit means this generic
  -- descent already supplied the child with a live balance (from the BAL table
  -- or a committed in-tx effect), so a later CREATE-specific header fallback
  -- must not overwrite it. Keep it in this frame's unused final save slot,
  -- rather than in global scratch, so nested descents cannot clobber it.
  "  sd zero, 88(sp)                 # a5 return: child env+32 was staged\n" ++
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
  -- Save the exact parent memory/env bases. Depth-0 may be staged by stateless
  -- replay code instead of the global `evm_memory`/`evm_env` labels.
  "  la t0, frame_parent_bases\n" ++
  "  slli t1, s8, 4                 # d * 16\n" ++
  "  add t0, t0, t1\n" ++
  "  sd s2, 0(t0)                   # parent memory base\n" ++
  "  sd s3, 8(t0)                   # parent env base\n" ++
  -- 4. enter the child frame (slot rebase + pool memory base). Stash the returned child
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
  -- 9. EIP-150 forwarded gas -> child env.gasRemaining (env+568); the
  -- transfer charge above has already reduced the parent gas when needed.
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
  -- rolls back to here), and reset the child's memory size to 0 (fresh 128 KiB).
  "  ld t0, 448(s3); sd t0, 448(s9)   # persistentLogLength (continue global log)\n" ++
  -- GH #10981: env+456/+480 REVERT checkpoints retired. NoopHalt REVERT reads
  -- body_state_snapshot_by_depth[d] (+40 persistent, +56 event) instead; the
  -- slab capture below is the sole checkpoint source.
  "  ld t0, 464(s3); sd t0, 464(s9)   # transientLogLength\n" ++
  "  ld t0, 472(s3); sd t0, 472(s9)   # eventLogLength\n" ++
  "  sd x0, 488(s9)                    # activeMemorySize = 0 (fresh child memory)\n" ++
  -- 8b2 (1ipxd): inherit the tx/block-constant env fields (txOrigin@128 .. chainId@384,
  -- a contiguous 288-byte block env+128..415) from the parent. call_frame_set_call_env
  -- sets only the per-frame fields (ADDRESS@0 / CALLER@64 / CALLVALUE@96 / selfBalance@32
  -- below), so without this a nested frame's ORIGIN / GASPRICE / COINBASE / TIMESTAMP /
  -- NUMBER / PREVRANDAO / GASLIMIT / BASEFEE / CHAINID read the BAL-replay-dirtied arena
  -- (garbage/0); pointer_reentry's re-entered frame SSTOREs ORIGIN()=0 instead of the tx
  -- sender, so the recipient BAL storage compare false-rejects a valid block. These nine
  -- fields are tx/block constants (identical in every frame), so a verbatim copy is exact.
  "  addi t0, s3, 128; addi t1, s9, 128; li t2, 288\n" ++
  ".Lcfd_envconst:\n" ++
  "  ld t3, 0(t0); sd t3, 0(t1); addi t0, t0, 8; addi t1, t1, 8; addi t2, t2, -8; bnez t2, .Lcfd_envconst\n" ++
  -- Propagate BLOBBASEFEE (env+512..543, 32 bytes) and blobHashCount (env+544..551)
  -- from parent to child. Without this, a nested CALL/CREATE frame reads
  -- BAL-replay garbage at env+544, so BLOBHASH always returns 0 (count=0).
  -- The evm_blob_hashes table is global (.data), so only the count needs copying.
  "  ld t0, 512(s3); sd t0, 512(s9)\n" ++
  "  ld t0, 520(s3); sd t0, 520(s9)\n" ++
  "  ld t0, 528(s3); sd t0, 528(s9)\n" ++
  "  ld t0, 536(s3); sd t0, 536(s9)\n" ++
  "  ld t0, 544(s3); sd t0, 544(s9)\n" ++
  -- 4ch8f.72: propagate currentBlockNumber (env+552) and blockHashCount (env+560)
  -- from parent to child. Same garbage-read class as BLOBHASH above: h_BLOCKHASH
  -- (EvmBlockHashHandlers.lean) reads both cells; only frame-0's env is initialized
  -- (Dispatch.lean:2299/2300 + trailer load), so a nested frame over the BAL-replay
  -- union front would read Phase-H garbage and, if the two range guards pass, index
  -- evm_block_hashes out of bounds. Both are block constants (identical every frame),
  -- so a verbatim copy is exact. The evm_block_hashes table is global (.data).
  "  ld t0, 552(s3); sd t0, 552(s9)\n" ++
  "  ld t0, 560(s3); sd t0, 560(s9)\n" ++
  -- F3 retirement: resolve the child's SELFBALANCE from authenticated state below.
  -- The former eager `callee_balance_table` scan was only a pre-resolution cache;
  -- removing it leaves env+32 zero until the live-effect or header lookup fills it.
  -- execution-specs vm/instructions/environment.py:510-535 reads the current
  -- account balance for SELFBALANCE; the live-effect overlay and authenticated
  -- header fallback below preserve that demand-driven source.
  "  sd zero, 32(s9); sd zero, 40(s9); sd zero, 48(s9); sd zero, 56(s9)\n" ++
  -- coc3g.6.4: LIVE-BALANCE overlay. A callee that already RECEIVED value earlier in this tx (its
  -- balance was credited by an earlier value-CALL) must descend with the LIVE balance, else its own
  -- later value-CALL debits from the stale pre-state -> the recorded final balance is short and the
  -- exec-vs-BAL non-storage comparator false-rejects (bv_fail=44; frontier/scenarios MCOPY b12:
  -- dd36afb2 receives +1 then sends 3, true 107+1-3=105, but pre-state-debit gave 107-3=104).
  -- The authoritative live balance = the most-recent recorded post_balance in the non-storage effect
  -- log (record_nonstorage_effect captures EVERY value-flow credit/debit), so overlay env+32 with
  -- nonstorage_effect_latest_balance(child_addr) when present; miss -> use authenticated pre-state.
  -- The effect log post_balance is 32B BE; env+32 is LE-limb (h_SELFBALANCE copies env+32 verbatim),
  -- so reverse BE -> LE. Scratch: env+696 (32B addr key: 20B BE + 12B zero) and env+728 (32B BE out);
  -- the env is frameEnvBytes=768 and its fields end at 688, so +696..+759 is free. a0/a1 are leaf-clobbered
  -- but s-regs (s3/s7/s8/s9/s10/s11) are preserved; ra saved across the helper.
  "  sd zero, 696(s9); sd zero, 704(s9); sd zero, 712(s9); sd zero, 720(s9)\n" ++   -- zero the 32B addr key (env+696..+727; all 8-aligned)
  "  sd zero, 728(s9); sd zero, 736(s9); sd zero, 744(s9); sd zero, 752(s9)\n" ++   -- zero the 32B out buffer (env+728..+759)
  "  addi t0, s9, 696; addi t1, s9, 19; li t2, 20\n" ++   -- write 20B BE addr into the key (low 20 bytes)
  ".Lcfd_lbov_rev:\n" ++
  "  lbu t3, 0(t1); sb t3, 0(t0); addi t1, t1, -1; addi t0, t0, 1; addi t2, t2, -1; bnez t2, .Lcfd_lbov_rev\n" ++
  "  addi sp, sp, -8; sd ra, 0(sp)\n" ++
  "  addi a0, s9, 696; addi a1, s9, 728\n" ++
  "  li a2, 4; jal ra, account_writes_latest_balance\n" ++
  "  mv t6, a0\n" ++                              -- 1 = found
  "  ld ra, 0(sp); addi sp, sp, 8\n" ++
  "  beqz t6, .Lcfd_lbov_done\n" ++
  -- reverse the 32B BE post_balance (env+728) -> env+32 (LE).
  "  addi t0, s9, 728; addi t1, s9, 63; li t2, 32\n" ++
  ".Lcfd_lbov_wb:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, -1; addi t2, t2, -1; bnez t2, .Lcfd_lbov_wb\n" ++
  "  li t2, 1; sd t2, 88(sp)         # committed effect supplies the live balance\n" ++
  ".Lcfd_lbov_done:\n" ++
  -- If no live effect supplied a balance, resolve the inherited authenticated header state instead
  -- of executing with a guessed zero.  This is the same prestate fallback used by
  -- CREATE descent: a live effect always wins, authenticated absence is zero, and
  -- malformed lookup results become the existing sticky runtime failure.
  "  ld t0, 88(sp); bnez t0, .Lcfd_prebalance_done\n" ++
  "  addi sp, sp, -8; sd ra, 0(sp)\n" ++
  "  ld a0, 576(s9); ld a1, 584(s9); addi a2, s9, 696; li a3, 20; ld a4, 592(s9); ld a5, 600(s9); la a6, create_prebalance_acct\n" ++
  "  jal ra, account_at_header_state_root_tracked; mv t6, a0\n" ++
  "  ld ra, 0(sp); addi sp, sp, 8\n" ++
  "  beqz t6, .Lcfd_prebalance_found\n" ++
  "  li t0, 1; beq t6, t0, .Lcfd_prebalance_done\n" ++
  "  li t0, 1; la t1, create_prebalance_lookup_status; sd t0, 0(t1); j .Lcfd_prebalance_done\n" ++
  ".Lcfd_prebalance_found:\n" ++
  "  la t0, create_prebalance_acct; addi t0, t0, 39; addi t1, s9, 32; li t2, 32\n" ++
  ".Lcfd_prebalance_copy:\n" ++
  "  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lcfd_prebalance_copy\n" ++
  ".Lcfd_prebalance_done:\n" ++
  -- nxio8.4.1: snapshot the parent's pre-child EIP-8037 state gas (the global
  -- evm_state_gas_left = state_gas_left reservoir, evm_state_gas_used = state_gas_used,
  -- evm_state_gas_spilled = state gas drawn from gas_left) into the child env
  -- so a child REVERT / exceptional halt can restore it in frame_return,
  -- matching execution-specs incorporate_child_on_error (the reverted child's
  -- entire state-gas allocation is returned to the parent and state_gas_used is
  -- NOT accumulated). s9 = child env; env offsets 624/632 are free (the env is
  -- frameEnvBytes=768 and its fields end at 616). Mirrors persistentLogCheckpoint.
  "  la t1, evm_state_gas_left; ld t0, 0(t1); sd t0, 624(s9)   # state_gas_left snapshot\n" ++
  "  la t1, evm_state_gas_used; ld t0, 0(t1); sd t0, 632(s9)   # state_gas_used snapshot\n" ++
  "  la t1, evm_state_gas_spilled; ld t0, 0(t1); sd t0, 760(s9) # state_gas_spilled snapshot\n" ++
  "  la t1, cd_new_account_charged_current; ld t0, 0(t1); sd t0, 752(s9); sd zero, 0(t1) # CALL new-account charge flag\n" ++
  -- nxio8.4.2: also snapshot the EIP-3529 refund accumulator (evm_refund_acc) so a
  -- child REVERT discards the child's refund_counter additions, matching
  -- incorporate_child_on_error (which does NOT add child.refund_counter to the
  -- parent). On success it is kept (incorporate_child_on_success accumulates it).
  "  la t1, evm_refund_acc; ld t0, 0(t1); sd t0, 640(s9)       # refund_counter snapshot\n" ++
  -- nxio8.4.3: snapshot the EIP-2929 storage-warmth count so a child REVERT
  -- discards the (contract,slot) keys the child warmed — incorporate_child_on_error
  -- does NOT .update() the parent's accessed_storage_keys (warmth is rolled back).
  -- The warm-set is append-only; truncating the count on revert reverts the
  -- additions (the gas already charged stays — regular gas is spent on revert).
  "  la t1, evm_storage_access_count; ld t0, 0(t1); sd t0, 648(s9)  # warmth count snapshot\n" ++
  -- account_warm_status_reverted_by_subcall: snapshot EIP-2929 accessed_addresses
  -- alongside accessed_storage_keys. A child REVERT rolls back accounts it warmed,
  -- so the parent's later BALANCE/EXT*/CALL access must be cold again.
  "  la t1, evm_access_account_count; ld t0, 0(t1); sd t0, 720(s9)  # account-warmth count snapshot\n" ++
  -- i3djw/reverted-CREATE rollback: CREATE deposit appends to global code and
  -- non-storage effect logs. A later child REVERT must discard those records,
  -- exactly like storage/log cursors above; otherwise the block-verdict reverse
  -- BAL covers checks see stale created-account effects and false-reject valid
  -- reverted-create blocks.
  -- Canonical body snapshot for this child at record `evm_call_depth`.
  -- Record width is 13 * 8 = 104 bytes: d*104 = d*64 + d*32 + d*8.
  -- Slot +88 (`account_state_overflow`) is root-only: no child restore existed
  -- before this representation migration, so retaining that child behavior is
  -- deliberate rather than an omitted shared restore.
  "  la t1, body_state_snapshot_by_depth; " ++ bodyStateSlabStrideOps "s8" "t2" "t3" ++ "; add t1, t1, t2\n" ++
  bodyStateCaptureCursorsAsm "  " "s3" "t1" "t0" ++
  "  la t4, exec_nonstorage_effect_count; ld t0, 0(t4); sd t0, 0(t1)  # nonstorage effect count snapshot\n" ++
  "  la t4, exec_nonstorage_effect_overflow; ld t0, 0(t4); sd t0, 8(t1)  # nonstorage overflow snapshot\n" ++
  -- Every child frame owns a journal high-water mark captured at ITS entry.
  -- In particular, a CREATE's creator-nonce advance is already committed before
  -- its child descends, so a child REVERT must retain that parent mutation and
  -- roll back only mutations made inside the child (its seed/nested CREATEs).
  bodyStateCaptureScalarAsm "create_nonce_undo_count" "t1" 96 "t4" "t0" ++
  -- r59nm S5a: the storage write-map undo journal takes its mark the same way
  -- and for the same reason -- a child REVERT must roll back only the writes
  -- made inside the child, leaving the parent's earlier writes standing.
  "  la t1, storage_writes_undo_count; ld t0, 0(t1)\n" ++
  "  la t1, storage_writes_undo_checkpoint; slli t2, s8, 3; add t1, t1, t2; sd t0, 0(t1)\n" ++
  "  la t1, body_state_snapshot_by_depth; " ++ bodyStateSlabStrideOps "s8" "t2" "t3" ++ "; add t1, t1, t2\n" ++
  -- Account writes have the same transaction-state rollback rule as storage
  -- writes (but unlike storage reads, which remain evidence of an access).
  bodyStateCaptureScalarAsm "account_writes_undo_count" "t1" 64 "t4" "t0" ++
  bodyStateCaptureScalarAsm "exec_code_effect_count" "t1" 16 "t4" "t0" ++
  bodyStateCaptureScalarAsm "exec_code_effect_next" "t1" 24 "t4" "t0" ++
  bodyStateCaptureScalarAsm "exec_code_effect_overflow" "t1" 32 "t4" "t0" ++
  -- Offset 72 remains reserved in the slab for layout compatibility; the
  -- retired AccountState pending journal has no frame checkpoint anymore.
  bodyStateCaptureScalarAsm "account_state_delete_count" "t1" 80 "t4" "t0" ++
  "  la t1, evm_selfdestruct_destroyed_count; ld t0, 0(t1); sd t0, 728(s9)  # same-tx destroyed-address snapshot\n" ++
  "  la t1, evm_selfdestruct_seen_count; ld t0, 0(t1)\n" ++
  "  la t1, evm_selfdestruct_seen_count_by_depth; slli t2, s8, 3; add t1, t1, t2; sd t0, 0(t1)  # journal snapshot at child depth\n" ++
  "  la t1, evm_selfdestruct_seen_overflow; ld t0, 0(t1)\n" ++
  "  la t1, evm_selfdestruct_seen_overflow_by_depth; slli t2, s8, 3; add t1, t1, t2; sd t0, 0(t1)\n" ++
  -- 3hlnt.2.2: snapshot the hot running block bloom into the child-depth
  -- checkpoint slab. The consensus receipt/log-bloom path still comes from
  -- descriptors; this only gives the hot accumulator the same rollback shape
  -- as the scalar frame checkpoints above.
  "  addi t0, s8, -1\n" ++
  "  slli t0, t0, 8\n" ++
  "  la t1, rb_bloom_checkpoints\n" ++
  "  add t1, t1, t0                 # dst = checkpoint[child_depth - 1]\n" ++
  "  la t2, rb_running_block_bloom  # src = hot running block bloom\n" ++
  "  li t3, 32\n" ++
  ".Lcfd_bloom_checkpoint_loop:\n" ++
  "  beqz t3, .Lcfd_bloom_checkpoint_done\n" ++
  "  ld t4, 0(t2)\n" ++
  "  sd t4, 0(t1)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcfd_bloom_checkpoint_loop\n" ++
  ".Lcfd_bloom_checkpoint_done:\n" ++
  -- 9. child env.codeSize (env+496).
  "  ld t0, 72(s7); sd t0, 496(s9)\n" ++
  -- 10. frame-relative stack bounds: point the under/overflow guards at the
  --     CHILD arena stack. cur_top = child stack top (s11 = base+0x8200);
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
  "  ld a5, 88(sp)                  # return whether env+32 already has a live value\n" ++
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
      +8  child x13 (= frame_base(1))         (expect call_frame_arena + 0x19000)
      +16 child x12                           (= base + 0x8200)
      +24 child x20                           (= base + 0x18400)
      +32 child mem[0] after zero-init        (expect 0, was pre-dirtied)
      +40 x12 - x13                           (expect 0x8200)
      +48 x20 - x13                           (expect 0x18400)
      +56 x13 - call_frame_arena              (expect 0x19000 — the depth-1 slot)

    ⚠️ The last two expectations MOVED when `frame_base` stopped skewing by `depth-1`:
    depth 1 is now slot 1, not slot 0, because slot 0 is reserved for depth 0. -/
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
  -- Env setup test: child env = call_frame_arena + frameEnvOff (0x18400) for depth 1.
  "  la a0, call_frame_arena; li t0, 0x18400; add a0, a0, t0\n" ++
  "  la a1, cfd_parent_env\n" ++
  "  la a2, cfd_to_word\n" ++
  "  la a3, cfd_value_word\n" ++
  "  li a4, 0\n" ++                          -- CALL (not static)
  "  jal ra, call_frame_set_call_env\n" ++
  "  ld t0, 0(a0); sd t0, 64(s0)\n" ++       -- child ADDRESS limb0 (expect 0xaaaaaaaa = to)
  "  ld t0, 64(a0); sd t0, 72(s0)\n" ++      -- child CALLER limb0 (expect 0xbbbbbbbb = parent ADDRESS)
  "  ld t0, 96(a0); sd t0, 80(s0)\n" ++      -- child CALLVALUE limb0 (expect 0xcccccccc = value)
  "  la a0, call_frame_arena; li t0, 0x18400; add a0, a0, t0\n" ++
  "  la a1, cfd_parent_env; la a2, cfd_to_word; la a3, cfd_value_word; li a4, 1\n" ++  -- STATICCALL
  "  jal ra, call_frame_set_call_env\n" ++
  "  ld t0, 96(a0); sd t0, 88(s0)\n" ++      -- child CALLVALUE limb0 (expect 0 = static)
  -- Calldata alias test: child callDataPtr@416 = parent_mem + argsOff, len@424.
  "  la a0, call_frame_arena; li t0, 0x18400; add a0, a0, t0\n" ++
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
  "call_frame_arena:\n  .zero " ++ toString (0x19000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "cfd_parent_env:\n  .quad 0xbbbbbbbb, 0, 0, 0\n" ++   -- parent ADDRESS@0
  "cfd_to_word:\n  .quad 0xaaaaaaaa, 0, 0, 0\n" ++       -- call target
  "cfd_value_word:\n  .quad 0xcccccccc, 0, 0, 0\n"       -- call value

/-- Positive witness for the shared memory pool. A depth-1 frame expands past
    the former 128 KiB limit, a depth-2 child occupies the next LIFO slice, and
    a reused sibling slice is zeroed on expansion without touching the parent. -/
def ziskMemoryPoolWitnessPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- Enter depth 1 at the pool base.
  "  la t0, evm_call_depth; li t1, 1; sd t1, 0(t0)\n" ++
  "  li a0, 1; jal ra, call_frame_enter\n" ++
  "  mv s7, a0; mv s8, a2\n" ++
  "  li t0, 16777216; sd t0, 568(s8); sd zero, 488(s8)\n" ++
  "  mv x13, s7; mv x20, s8\n" ++
  "  li x14, 0x30000; li x15, 32\n" ++
  updateActiveMemorySizeAsm "pool_witness_parent" "x14" "x15" "x16" "x17" "x18" "x19" true false ++
  "  li t0, 0x1122334455667788; add t1, s7, x14; sd t0, 0(t1)\n" ++
  -- Enter depth 2. Its base must be parent base + parent MSIZE.
  "  la t0, frame_parent_bases; addi t0, t0, 32; sd s7, 0(t0); sd s8, 8(t0)\n" ++
  "  la t0, evm_call_depth; li t1, 2; sd t1, 0(t0)\n" ++
  "  li a0, 2; jal ra, call_frame_enter\n" ++
  "  mv s9, a0; mv s10, a2\n" ++
  "  li t0, 16777216; sd t0, 568(s10); sd zero, 488(s10)\n" ++
  "  mv x13, s9; mv x20, s10\n" ++
  "  li x14, 0x40000; li x15, 32\n" ++
  updateActiveMemorySizeAsm "pool_witness_child" "x14" "x15" "x16" "x17" "x18" "x19" true false ++
  "  li t0, 0x8877665544332211; add t1, s9, x14; sd t0, 0(t1)\n" ++
  -- Record child isolation and parent readback.
  "  sub t0, s9, s7; sd t0, 0(s0)\n" ++
  "  add t1, s7, x14; li t2, 0x30000; sub t1, t1, x14; add t1, t1, t2; ld t0, 0(t1); sd t0, 8(s0)\n" ++
  "  add t1, s9, x14; ld t0, 0(t1); sd t0, 16(s0)\n" ++
  -- Re-enter the same depth as a sibling. Expansion must erase stale child bytes.
  "  li a0, 2; jal ra, call_frame_enter\n" ++
  "  mv s11, a0; mv s6, a2; li t0, 16777216; sd t0, 568(s6); sd zero, 488(s6)\n" ++
  "  mv x13, s11; mv x20, s6; li x14, 0x40000; li x15, 32\n" ++
  updateActiveMemorySizeAsm "pool_witness_sibling" "x14" "x15" "x16" "x17" "x18" "x19" true false ++
  "  add t1, s11, x14; ld t0, 0(t1); sd t0, 24(s0)\n" ++
  "  li t0, 0xaabbccddeeff0011; sd t0, 0(t1); ld t0, 0(t1); sd t0, 32(s0)\n" ++
  "  li t2, 0x30000; add t1, s7, t2; ld t0, 0(t1); sd t0, 40(s0)\n" ++
  "  sub t0, s11, s9; sd t0, 48(s0)\n" ++
  "  j .Lpool_witness_done\n" ++
  ".exit_outofgas:\n  li t0, -1; sd t0, 56(s0); j .Lpool_witness_done\n" ++
  frameBaseFunction ++ "\n" ++ frameDepthPushFunction ++ "\n" ++
  callFrameEnterFunction ++ "\n" ++
  ".Lpool_witness_done:"

def ziskMemoryPoolWitnessDataSection : String :=
  ".section .data\n.balign 32\n" ++
  "call_frame_arena:\n  .zero 0x32000\n" ++
  ".balign 8\nevm_memory_pool:\n  .zero 0x100000\nevm_memory_pool_end:\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  "evm_sparse_memory_next_epoch:\n  .quad 1\n" ++
  "evm_sparse_memory_epoch_by_depth:\n  .zero 8200\n" ++
  "frame_parent_bases:\n  .zero 16400\n"

def ziskCallDescendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMemoryPoolWitnessPrologue
  dataAsm     := ziskMemoryPoolWitnessDataSection
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
      +64  child x20 - &call_frame_arena   (expect 0x18400 = +frameEnvOff)
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
      +152 evm_cur_stack_top - &arena      (expect 0x8200 = child frame stack top)
      +160 evm_cur_stack_low - &arena      (expect 0x20200 = top - 1024*32)
      +168 parent env.gasRemaining        (expect 88700 = 100000 - transfer 10300 - cost 1000)
      +176/+184 state-gas snapshots       (expect 12345/67890)
      +192/+200 refund/warmth snapshots   (expect 24680/5)
      +208/+216 running bloom checkpoint  (expect word0/word31 copied) -/
def ziskCallFrameDescendPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t0, evm_call_depth; sd x0, 0(t0)\n" ++
  -- parent env: ADDRESS@0, gasRemaining@568, witness state ptr marker @592.
  "  la t0, cfd2_penv\n" ++
  "  li t1, 0xaa; sd t1, 0(t0)\n" ++
  "  li t1, 100000; sd t1, 568(t0)\n" ++
  "  li t1, 0x592; sd t1, 592(t0)\n" ++
  -- nxio8.4.1: pre-child state gas; descend must snapshot it into child env+624/632.
  "  la t0, evm_state_gas_left; li t1, 12345; sd t1, 0(t0)\n" ++
  "  la t0, evm_state_gas_used; li t1, 67890; sd t1, 0(t0)\n" ++
  "  la t0, evm_refund_acc; li t1, 24680; sd t1, 0(t0)\n" ++
  "  la t0, evm_storage_access_count; li t1, 5; sd t1, 0(t0)\n" ++
  -- Running block bloom snapshot source; descend should copy word0/word31 into
  -- rb_bloom_checkpoints[0].
  "  la t0, rb_running_block_bloom; li t1, 0x1111222233334444; sd t1, 0(t0); li t1, 0xaaaabbbbccccdddd; sd t1, 248(t0)\n" ++
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
  -- nxio8.4.1: descend snapshotted pre-child state gas into child env+624/632.
  "  ld t0, 624(x20); sd t0, 176(s0)\n" ++   -- expect 12345 (state_gas_left)
  "  ld t0, 632(x20); sd t0, 184(s0)\n" ++   -- expect 67890 (state_gas_used)
  "  ld t0, 640(x20); sd t0, 192(s0)\n" ++   -- expect 24680 (refund_acc, nxio8.4.2)
  "  ld t0, 648(x20); sd t0, 200(s0)\n" ++   -- expect 5 (warmth count, nxio8.4.3)
  "  la t0, rb_bloom_checkpoints; ld t1, 0(t0); sd t1, 208(s0); ld t1, 248(t0); sd t1, 216(s0)\n" ++
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
  -- EIP-150: parent gas deducted by transfer (10300, value-bearing) + cost (1000) -> 88700.
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
  "call_frame_arena:\n  .zero " ++ toString (0x19000 : Nat) ++ "\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++
  ".balign 16\n" ++
  "frame_parent_bases:\n  .zero 16400\n" ++
  ".balign 8\n" ++
  -- Frame-relative stack-bound cells (descend overwrites them; zeroed stubs here).
  "evm_cur_stack_top:\n  .zero 8\n" ++
  "evm_cur_stack_low:\n  .zero 8\n" ++
  -- nxio8.4.1: EIP-8037 state-gas globals (real symbols in the guest dispatcher
  -- data section; stubbed so the probe links + can verify the descend snapshot).
  "evm_state_gas_left:\n  .zero 8\n" ++
  "evm_state_gas_used:\n  .zero 8\n" ++
  "evm_refund_acc:\n  .zero 8\n" ++
  "cd_new_account_charged_current:\n  .zero 8\n" ++
  "evm_storage_access_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_overflow:\n  .zero 8\n" ++
  "exec_code_effect_count:\n  .zero 8\n" ++
  "exec_code_effect_next:\n  .zero 8\n" ++
  "exec_code_effect_overflow:\n  .zero 8\n" ++
  "rb_running_block_bloom:\n  .zero 256\n" ++
  "rb_running_receipt_bloom:\n  .zero 256\n" ++
  "rb_bloom_checkpoints:\n  .zero 262144\n" ++
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
      +72/+80/+88 mode 3 DELEGATECALL(expect 0xaa/0xcc/0xee)
      +96/+104/+112/+120 isStatic flags modes 0..3 (expect 7/1/7/7) -/
def ziskSetCallEnvPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- parent env markers + to/value words.
  "  la t0, sce_penv\n" ++
  "  li t1, 0xaa; sd t1, 0(t0)\n" ++
  "  li t1, 0xcc; sd t1, 64(t0)\n" ++
  "  li t1, 0xee; sd t1, 96(t0)\n" ++
  "  li t1, 7; sd t1, " ++ toString staticContextFlagOff ++ "(t0)\n" ++
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
  "  la t0, sce_child0; ld t1, " ++ toString staticContextFlagOff ++ "(t0); sd t1, 96(s0)\n" ++
  "  la t0, sce_child1; ld t1, " ++ toString staticContextFlagOff ++ "(t0); sd t1, 104(s0)\n" ++
  "  la t0, sce_child2; ld t1, " ++ toString staticContextFlagOff ++ "(t0); sd t1, 112(s0)\n" ++
  "  la t0, sce_child3; ld t1, " ++ toString staticContextFlagOff ++ "(t0); sd t1, 120(s0)\n" ++
  "  j .Lsce_done\n" ++
  callFrameSetCallEnvFunction ++ "\n" ++
  ".Lsce_done:"

def ziskSetCallEnvDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "sce_penv:\n  .zero 512\n" ++
  "sce_to:\n  .zero 32\n" ++
  "sce_val:\n  .zero 32\n" ++
  "sce_child0:\n  .zero 512\n" ++
  "sce_child1:\n  .zero 512\n" ++
  "sce_child2:\n  .zero 512\n" ++
  "sce_child3:\n  .zero 512\n"

def ziskSetCallEnvProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSetCallEnvPrologue
  dataAsm     := ziskSetCallEnvDataSection
}

end EvmAsm.Codegen
