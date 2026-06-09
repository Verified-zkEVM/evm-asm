/-
  EvmAsm.Codegen.Programs.CallFrameReturn

  `frame_return` — the call-frame RETURN mechanic for the iterative (non-recursive)
  CALL descent (bead fhsxz.2.4.2.61.6.6). When a child frame halts (STOP / RETURN
  / REVERT / exceptional), instead of halting the whole guest the dispatcher pops
  one frame and RESUMES the parent's dispatch loop:

    1. read the saved call-context for the current (child) depth;
    2. copy `min(outsize, retlen)` returndata bytes into the parent's output region;
    3. pop `evm_call_depth` (child depth d → parent depth d-1);
    4. restore the parent PC / code-base (x10 / x21) from `frame_save_area`;
    5. recompute the parent register bases x13 (memory) / x20 (env): the existing
       `evm_memory` / `evm_env` labels for depth 0, else `frame_base(d-1)+off`;
    6. restore the parent stack top x12 to `parent_x12 + netPopBytes` (pop the CALL
       args) and write the success word (1 = STOP/RETURN, 0 = REVERT/exceptional);
    7. advance the parent PC one byte past the CALL opcode;
    8. `ret` — the caller (the depth-aware halt handler) then `j .dispatch_loop`.

  This helper does NOT itself jump to `.dispatch_loop`, so it can be unit-probed in
  isolation (no MPT / no dispatch loop) — the probe drives it with a synthesized
  call-context + save-area + depth and inspects the restored registers. The descent
  side (CALL handler) and the depth-aware halt branches are wired in a following
  slice; this slice lands the return mechanic + its data area + the unit probe.

  Layout it depends on (CallFrameLayout / CallFrameSwitch):
    `evm_call_depth`   u64 current depth (0 = top-level frame[0]).
    `frame_save_area`  1025 × 16 B (saved pc, codebase) indexed by depth.
    `frame_call_ctx`   1025 × 32 B (parent_x12, outoff_abs, outsize, netPopBytes)
                       indexed by the CHILD depth — saved by the descent, consumed
                       here on the matching return.
    `call_frame_arena` overlay base for frames 1..1024 (FRAME_STRIDE 0x29000);
    `evm_memory`/`evm_env` the depth-0 register bases.
  Child-frame sub-offsets: frameMemOff=0, frameEnvOff=0x28400.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- `frame_return(a0 = success word, a1 = child returndata ptr, a2 = returndata len)`:
    pop one call frame and restore the parent's dispatcher registers, leaving the
    parent ready to resume at `.dispatch_loop` (the caller performs that jump).

    Writes the parent stack: `success` (a0) at the post-pop stack top. For
    RETURN/REVERT, `a1`/`a2` describe the child's returndata so up to `outsize`
    bytes are copied into the caller's output memory window (`outoff_abs` from the
    saved call-context); pass `a1 = a2 = 0` for STOP / exceptional halts. The full
    returndata (capped at the 256-byte frame) is ALSO staged into
    `evm_precompile_frame` (size@+8, data@+16) so the parent's
    RETURNDATASIZE/RETURNDATACOPY observe this sub-call's return.

    On return the live dispatcher registers are repointed to the parent frame:
      x10 = parent PC + 1 (past the CALL), x21 = parent code base,
      x13 = parent memory base, x20 = parent env base,
      x12 = parent stack top with the success word pushed.
    Clobbers t0-t4 (and the dispatcher regs it intentionally repoints). -/
def frameReturnFunction : String :=
  "frame_return:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s6, 40(sp); sd s7, 48(sp)\n" ++
  "  mv s0, a0                      # success word\n" ++
  "  mv s1, a1                      # child returndata ptr\n" ++
  "  mv s2, a2                      # returndata len\n" ++
  -- Capture the child frame's leftover gas (x20 = child env at entry) for the
  -- EIP-150 refund below; held in s7 across the x20 repoint.
  "  ld s7, 568(x20)\n" ++
  -- Load the saved call-context for the CURRENT (child) depth.
  "  la t0, evm_call_depth\n" ++
  "  ld t1, 0(t0)                   # t1 = child depth d\n" ++
  "  la t0, frame_call_ctx\n" ++
  "  slli t2, t1, 5                 # d * 32\n" ++
  "  add t0, t0, t2\n" ++
  "  ld s3, 0(t0)                   # parent_x12 (stack top at the CALL)\n" ++
  "  ld a3, 8(t0)                   # outoff_abs (parent output mem ptr)\n" ++
  "  ld a4, 16(t0)                  # outsize (output cap)\n" ++
  "  ld s6, 24(t0)                  # netPopBytes (CALL 192 / STATICCALL 160)\n" ++
  "                                 # NB: s4/s5 ARE x20/x21 (env/code base) — never use as scratch\n" ++
  -- Copy min(outsize, retlen) bytes of returndata into the caller output window.
  "  mv t2, s2                      # n = retlen\n" ++
  "  bgeu a4, t2, 1f                # if outsize >= retlen keep retlen\n" ++
  "  mv t2, a4                      # else n = outsize\n" ++
  "1:\n" ++
  "  beqz t2, 3f                    # nothing to copy\n" ++
  "  mv t3, s1                      # src = child returndata\n" ++
  "  mv t4, a3                      # dst = outoff_abs\n" ++
  "2:\n" ++
  "  lbu t0, 0(t3)\n" ++
  "  sb t0, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, 2b\n" ++
  "3:\n" ++
  -- Stage the child's returndata into `evm_precompile_frame` so the parent's
  -- RETURNDATASIZE(0x3d)/RETURNDATACOPY(0x3e) see the LAST sub-call's return
  -- (NoopReturnData reads size@+8, data@+16, cap 256). This is independent of the
  -- output-window copy above (which is bounded by the CALL's `outsize`): the
  -- returndata buffer holds the FULL child return capped at the 256-byte frame.
  -- `+8` keeps the TRUE retlen (so RETURNDATASIZE is exact); `+16` gets
  -- min(retlen,256) bytes. STOP / exceptional (s1=s2=0) -> size 0, no copy. Runs
  -- before x13 is repointed, so s1 still points into the (live) child memory.
  "  la t0, evm_precompile_frame\n" ++
  "  sd s2, 8(t0)                   # returndata size = retlen (true)\n" ++
  "  mv t2, s2                      # n = retlen\n" ++
  "  li t1, 256\n" ++
  "  bgeu t1, t2, 7f                # if 256 >= retlen keep retlen\n" ++
  "  mv t2, t1                      # else n = 256 (buffer cap)\n" ++
  "7:\n" ++
  "  beqz t2, 9f                    # nothing to copy\n" ++
  "  mv t3, s1                      # src = child returndata\n" ++
  "  addi t4, t0, 16                # dst = evm_precompile_frame + 16\n" ++
  "8:\n" ++
  "  lbu t1, 0(t3)\n" ++
  "  sb t1, 0(t4)\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, 1\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, 8b\n" ++
  "9:\n" ++
  -- Pop the depth: child d -> parent d-1.
  "  la t0, evm_call_depth\n" ++
  "  ld t1, 0(t0)\n" ++
  "  addi t1, t1, -1                # t1 = parent depth\n" ++
  "  sd t1, 0(t0)\n" ++
  -- Restore parent PC (x10) and code base (x21).
  "  la t0, frame_save_area\n" ++
  "  slli t2, t1, 4                 # parent_depth * 16\n" ++
  "  add t0, t0, t2\n" ++
  "  ld x10, 0(t0)                  # parent pc (points AT the CALL opcode)\n" ++
  "  ld x21, 8(t0)                  # parent code base\n" ++
  -- Recompute parent memory base (x13) and env base (x20).
  "  bnez t1, 4f\n" ++
  "  la x13, evm_memory\n" ++
  "  la x20, evm_env\n" ++
  -- Frame-relative stack bounds: restore the guards to the depth-0 global arena.
  "  la t0, evm_cur_stack_top; la t2, evm_stack_top; sd t2, 0(t0)\n" ++
  "  la t0, evm_cur_stack_low; la t2, evm_stack_low; sd t2, 0(t0)\n" ++
  "  j 5f\n" ++
  "4:\n" ++
  "  addi t2, t1, -1               # (parent_depth - 1)\n" ++
  "  li t3, 0x29000               # FRAME_STRIDE\n" ++
  "  mul t2, t2, t3\n" ++
  "  la t3, call_frame_arena\n" ++
  "  add t2, t3, t2               # frame_base(parent_depth)\n" ++
  "  mv x13, t2                   # + frameMemOff (0)\n" ++
  "  li t3, 0x28400\n" ++
  "  add x20, t2, t3              # + frameEnvOff\n" ++
  -- Frame-relative stack bounds: restore the guards to the parent frame's stack.
  "  li t3, 0x18200\n" ++
  "  add t3, t2, t3               # parent stack top = frame_base + frameStackTopOff\n" ++
  "  la t4, evm_cur_stack_top; sd t3, 0(t4)\n" ++
  "  li t4, 0x8000\n" ++
  "  sub t3, t3, t4               # parent stack low = top - 1024*32\n" ++
  "  la t4, evm_cur_stack_low; sd t3, 0(t4)\n" ++
  "5:\n" ++
  -- EIP-150 gas refund: return the child frame's UNUSED gas to the parent
  -- (x20 = parent env here). Pairs with the cost deduction in call_frame_descend.
  "  ld t0, 568(x20)\n" ++
  "  add t0, t0, s7\n" ++
  "  sd t0, 568(x20)\n" ++
  -- Restore the parent stack top: pop the CALL args, push the success word.
  "  add x12, s3, s6              # parent_x12 + netPopBytes\n" ++
  "  sd s0, 0(x12)\n" ++
  "  sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)\n" ++
  -- Resume the parent one byte past the CALL opcode.
  "  addi x10, x10, 1\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s6, 40(sp); ld s7, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_frame_return`: unit probe for `frame_return` over synthesized state.
    It builds two return scenarios — a depth-1→0 return (parent uses the
    `evm_memory`/`evm_env` labels) and a depth-2→1 return (parent uses
    `frame_base(1)` = `call_frame_arena`) — and records the restored registers so
    a script can assert the pc/codebase/mem/env/stack-top math and the pushed
    success word.

    Output (depth-1→0 case):
      +0  x10 after return            (expect parent_pc 0x100 + 1 = 0x101)
      +8  x21 after return            (expect parent_cb 0x222)
      +16 x13 - &evm_memory           (expect 0)
      +24 x20 - &evm_env              (expect 0)
      +32 x12 - &fr_pstack            (expect 192 = netPopBytes)
      +40 success word at x12         (expect 1)
      +48 evm_call_depth after        (expect 0)
    Output (depth-2→1 case):
      +56 x13 - &call_frame_arena     (expect 0  = frame_base(1)+frameMemOff)
      +64 x20 - &call_frame_arena     (expect 0x28400 = +frameEnvOff)
      +72 x12 - &fr_pstack2           (expect 160 = netPopBytes)
      +80 success word at x12         (expect 0  — REVERT path)
      +88 evm_call_depth after        (expect 1)
      +96 first copied returndata byte at outoff_abs (expect 0xab)
    Frame-relative stack-bound restores:
      +104 evm_cur_stack_top - &evm_stack_top   (scenario A, expect 0)
      +112 evm_cur_stack_top - &call_frame_arena (scenario B, expect 0x18200)
    Returndata staging into evm_precompile_frame:
      +120 precompile_frame size after scenario A (STOP, expect 0)
      +128 precompile_frame size after scenario B (expect 4 = retlen)
      +136 precompile_frame data[0] after scenario B (expect 0xab)
    EIP-150 gas refund (parent gas += child leftover):
      +144 parent gas after scenario A (100 + 50 = 150)
      +152 parent gas after scenario B (200 + 30 = 230) -/
def ziskFrameReturnPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0xa0010000\n" ++
  -- ---- Scenario A: depth 1 -> 0, STOP-style (no returndata) ----
  "  la t0, evm_call_depth; li t1, 1; sd t1, 0(t0)\n" ++
  -- frame_save_area[0] = (pc=0x100, cb=0x222)
  "  la t0, frame_save_area; li t1, 0x100; sd t1, 0(t0); li t1, 0x222; sd t1, 8(t0)\n" ++
  -- frame_call_ctx[1] = (parent_x12=fr_pstack, outoff_abs=fr_out, outsize=0, netPop=192)
  "  la t0, frame_call_ctx; addi t0, t0, 32\n" ++
  "  la t1, fr_pstack; sd t1, 0(t0)\n" ++
  "  la t1, fr_out; sd t1, 8(t0)\n" ++
  "  sd x0, 16(t0)\n" ++
  "  li t1, 192; sd t1, 24(t0)\n" ++
  "  la x20, fr_child_env\n" ++                       -- child env for the gas read
  "  la t0, fr_child_env; li t1, 50; sd t1, 568(t0)\n" ++   -- child leftover gas = 50
  "  la t0, evm_env;      li t1, 100; sd t1, 568(t0)\n" ++  -- parent gas = 100
  "  li a0, 1; li a1, 0; li a2, 0\n" ++
  "  jal ra, frame_return\n" ++
  "  sd x10, 0(s0)                  # expect 0x101 (parent_pc 0x100 + 1)\n" ++
  "  sd x21, 8(s0)                  # expect 0x222\n" ++
  "  la t0, evm_memory; sub t0, x13, t0; sd t0, 16(s0)   # expect 0\n" ++
  "  la t0, evm_env;    sub t0, x20, t0; sd t0, 24(s0)   # expect 0\n" ++
  "  la t0, fr_pstack;  sub t0, x12, t0; sd t0, 32(s0)   # expect 192\n" ++
  "  ld t0, 0(x12); sd t0, 40(s0)                        # expect 1\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 48(s0)  # expect 0\n" ++
  -- frame-relative stack bounds restored to the depth-0 global arena (cur_top == &evm_stack_top).
  "  la t0, evm_cur_stack_top; ld t1, 0(t0); la t2, evm_stack_top; sub t1, t1, t2; sd t1, 104(s0)  # expect 0\n" ++
  -- returndata staging: STOP carried no returndata -> precompile_frame size 0.
  "  la t0, evm_precompile_frame; ld t1, 8(t0); sd t1, 120(s0)  # expect 0\n" ++
  -- EIP-150 gas refund: parent gas 100 + child leftover 50 = 150.
  "  la t0, evm_env; ld t1, 568(t0); sd t1, 144(s0)  # expect 150\n" ++
  -- ---- Scenario B: depth 2 -> 1, REVERT-style with a returndata byte ----
  "  la t0, evm_call_depth; li t1, 2; sd t1, 0(t0)\n" ++
  -- frame_save_area[1] = (pc=0x300, cb=0x444)
  "  la t0, frame_save_area; addi t0, t0, 16; li t1, 0x300; sd t1, 0(t0); li t1, 0x444; sd t1, 8(t0)\n" ++
  -- frame_call_ctx[2] = (parent_x12=fr_pstack2, outoff_abs=fr_out, outsize=1, netPop=160)
  "  la t0, frame_call_ctx; addi t0, t0, 64\n" ++
  "  la t1, fr_pstack2; sd t1, 0(t0)\n" ++
  "  la t1, fr_out; sd t1, 8(t0)\n" ++
  "  li t1, 1; sd t1, 16(t0)\n" ++
  "  li t1, 160; sd t1, 24(t0)\n" ++
  -- returndata source: one byte 0xab
  "  la t0, fr_ret; li t1, 0xab; sb t1, 0(t0)\n" ++
  "  la x20, fr_child_env\n" ++
  "  la t0, fr_child_env; li t1, 30; sd t1, 568(t0)\n" ++   -- child leftover gas = 30
  "  la t0, call_frame_arena; li t2, 0x28400; add t0, t0, t2; li t1, 200; sd t1, 568(t0)\n" ++  -- parent (frame[1]) gas = 200
  "  li a0, 0; la a1, fr_ret; li a2, 4\n" ++
  "  jal ra, frame_return\n" ++
  "  la t0, call_frame_arena; sub t0, x13, t0; sd t0, 56(s0)   # expect 0\n" ++
  "  la t0, call_frame_arena; sub t0, x20, t0; sd t0, 64(s0)   # expect 0x28400\n" ++
  "  la t0, fr_pstack2; sub t0, x12, t0; sd t0, 72(s0)         # expect 160\n" ++
  "  ld t0, 0(x12); sd t0, 80(s0)                              # expect 0\n" ++
  "  la t0, evm_call_depth; ld t1, 0(t0); sd t1, 88(s0)        # expect 1\n" ++
  "  la t0, fr_out; lbu t1, 0(t0); sd t1, 96(s0)               # expect 0xab\n" ++
  -- frame-relative stack bounds restored to the parent frame[1] arena stack.
  "  la t0, evm_cur_stack_top; ld t1, 0(t0); la t2, call_frame_arena; sub t1, t1, t2; sd t1, 112(s0)  # expect 0x18200\n" ++
  -- returndata staging: retlen 4 -> precompile_frame size 4; first byte 0xab @ +16.
  "  la t0, evm_precompile_frame; ld t1, 8(t0); sd t1, 128(s0)    # expect 4\n" ++
  "  la t0, evm_precompile_frame; lbu t1, 16(t0); sd t1, 136(s0)  # expect 0xab\n" ++
  -- EIP-150 gas refund: parent gas 200 + child leftover 30 = 230.
  "  la t0, call_frame_arena; li t2, 0x28400; add t0, t0, t2; ld t1, 568(t0); sd t1, 152(s0)  # expect 230\n" ++
  "  j .Lfr_done\n" ++
  frameReturnFunction ++ "\n" ++
  ".Lfr_done:"

/-- Data stubs so the probe links standalone (the real symbols live in the guest's
    dispatcher data section). `call_frame_arena` holds frame[1] (depth-2→1 parent). -/
def ziskFrameReturnDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_call_depth:\n  .zero 8\n" ++
  ".balign 16\n" ++
  "frame_save_area:\n  .zero 16400\n" ++
  ".balign 32\n" ++
  "frame_call_ctx:\n  .zero 32800\n" ++          -- 1025 × 32 B
  ".balign 32\n" ++
  "call_frame_arena:\n  .zero " ++ toString (0x29000 : Nat) ++ "\n" ++
  ".balign 32\n" ++
  "evm_memory:\n  .zero 64\n" ++
  "evm_env:\n  .zero 640\n" ++          -- enlarged: frame_return refunds gas at env+568
  "fr_child_env:\n  .zero 640\n" ++       -- child env (x20 at frame_return entry); +568 = child gas

  -- Frame-relative stack-bound labels + cells. `evm_stack_top`/`evm_stack_low`
  -- are address-only stubs (frame_return takes their `&` for the depth-0
  -- restore); the cur cells hold the restored current-frame bounds.
  "evm_stack_top:\n  .zero 8\n" ++
  "evm_stack_low:\n  .zero 8\n" ++
  "evm_cur_stack_top:\n  .zero 8\n" ++
  "evm_cur_stack_low:\n  .zero 8\n" ++
  -- Returndata staging target (frame_return writes size@+8, data@+16, cap 256).
  ".balign 8\n" ++
  "evm_precompile_frame:\n  .zero 1280\n" ++
  "fr_pstack:\n  .zero 256\n" ++
  "fr_pstack2:\n  .zero 256\n" ++
  "fr_out:\n  .zero 64\n" ++
  "fr_ret:\n  .zero 64\n"

def ziskFrameReturnProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskFrameReturnPrologue
  dataAsm     := ziskFrameReturnDataSection
}

end EvmAsm.Codegen
