/-
  EvmAsm.Codegen.Programs.EvmMcopyGas

  Raw-asm helper snippets for the concrete runtime MCOPY handler. Kept
  separate from Programs/Evm.lean so the main opcode registry stays under
  the file-size guardrail.
-/

import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-- Dispatcher env offset used by MCOPY gas helpers for the runtime active
    memory size in bytes. Must match `activeMemorySizeOff` in `Evm.lean`. -/
private def mcopyActiveMemorySizeOff : Nat := 488

/-- Inline asm for MCOPY's EIP-5656 dynamic gas. The dispatch loop
    already charges the static base cost (3). This adds
    `3 * ceil32(length) / 32` plus execution-specs memory expansion
    over `(source, length)` then `(destination, length)`, using the
    dispatcher-maintained rounded active-memory size. On insufficient
    gas it jumps to the shared out-of-gas exit before stack or memory
    mutation. Scratch registers: x5/x6/x7/x17/x18/x19. -/
def mcopyDynamicGasAsm : String :=
  "  li x18, 0\n" ++                    -- x18 = dynamic gas accumulator
  "  beqz x16, .Lmcopy_charge_dynamic\n" ++
  -- copy gas: 3 * ceil32(length) / 32
  "  addi x17, x16, 31\n" ++
  "  srli x17, x17, 5\n" ++
  "  slli x18, x17, 1\n" ++
  "  add x18, x18, x17\n" ++
  "  ld x19, " ++ toString mcopyActiveMemorySizeOff ++ "(x20)\n" ++
  -- source extension: after = ceil32(source + length)
  "  add x5, x15, x16\n" ++
  "  addi x5, x5, 31\n" ++
  "  li x6, -32\n" ++
  "  and x5, x5, x6\n" ++
  "  bgeu x19, x5, .Lmcopy_src_gas_done\n" ++
  -- before cost = words*3 + words^2/512 for x19
  "  srli x6, x19, 5\n" ++
  "  slli x7, x6, 1\n" ++
  "  add x7, x7, x6\n" ++
  -- mulhu: UNIFICATION with updateActiveMemorySizeAsm, not overflow-required
  -- after the range guard. Post-guard ends ≤ arena (depth0 0x400000 → w≤2^17,
  -- w²≤2^34; nested ≤ pool 0x6000000 → w≤2^22, w²≤2^44). Both fit in u64
  -- with margin; mulhu cannot fire on reachable clamped ends. Kept so MCOPY
  -- quadratic cost matches the shared helper pattern (w≥2^32 → OOG).
  "  mulhu x17, x6, x6\n" ++
  "  bnez x17, .exit_outofgas\n" ++
  "  mul x6, x6, x6\n" ++
  "  srli x6, x6, 9\n" ++
  "  add x6, x6, x7\n" ++
  -- after cost = words*3 + words^2/512 for x5.
  -- Spill after-rounded to x19 HERE (expansion path only): next mulhu writes
  -- x5, so x5 cannot survive until the old post-cost spill site. Window from
  -- this mv to old `mv x19,x5` (end of after-cost): srli/slli/add/mulhu/bnez/
  -- mul/srli/add/sub/add — none reads x19; only mulhu writes x5 (intentional).
  "  mv x19, x5\n" ++
  "  srli x7, x5, 5\n" ++
  "  slli x17, x7, 1\n" ++
  "  add x17, x17, x7\n" ++
  "  mulhu x5, x7, x7\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  mul x7, x7, x7\n" ++
  "  srli x7, x7, 9\n" ++
  "  add x7, x7, x17\n" ++
  "  sub x7, x7, x6\n" ++
  "  add x18, x18, x7\n" ++
  ".Lmcopy_src_gas_done:\n" ++
  -- destination extension uses the source-updated current size (x19).
  "  add x5, x14, x16\n" ++
  "  addi x5, x5, 31\n" ++
  "  li x6, -32\n" ++
  "  and x5, x5, x6\n" ++
  "  bgeu x19, x5, .Lmcopy_dst_gas_done\n" ++
  "  srli x6, x19, 5\n" ++
  "  slli x7, x6, 1\n" ++
  "  add x7, x7, x6\n" ++
  "  mulhu x17, x6, x6\n" ++
  "  bnez x17, .exit_outofgas\n" ++
  "  mul x6, x6, x6\n" ++
  "  srli x6, x6, 9\n" ++
  "  add x6, x6, x7\n" ++
  "  srli x7, x5, 5\n" ++
  "  slli x17, x7, 1\n" ++
  "  add x17, x17, x7\n" ++
  "  mulhu x5, x7, x7\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  mul x7, x7, x7\n" ++
  "  srli x7, x7, 9\n" ++
  "  add x7, x7, x17\n" ++
  "  sub x7, x7, x6\n" ++
  "  add x18, x18, x7\n" ++
  ".Lmcopy_dst_gas_done:\n" ++
  ".Lmcopy_charge_dynamic:\n" ++
  "  ld x5, 568(x20)\n" ++
  "  bltu x5, x18, .exit_outofgas\n" ++
  "  sub x5, x5, x18\n" ++
  "  sd x5, 568(x20)\n"

/-- MCOPY range checks before dynamic gas or memory mutation. The current
    runtime memory arena is u64-addressed; non-zero high limbs in length,
    source, or destination are treated as memory-expansion OOG. Per
    execution-specs, zero length skips source/destination expansion, so
    high source/destination limbs are accepted when length is exactly zero.
    Low-limb `offset + length` wraparound also routes to OOG.

    Arena bound uses `memoryArenaLimitAsm` (same helper as MLOAD/MSTORE/COPY
    family) — not a hardcoded `0x10000` (#10523). At this site `x13` is the
    live EVM-memory base (handler later does `add dst/src, x13, offset`);
    depth 0 → `rootRuntimeMemoryArenaLimitBytes`; nested →
    `evm_memory_pool_end - x13`. Scratch: loads `x6` (limit); `x5` ends. -/
def mcopyRangeGuardAsm : String :=
  -- Any non-zero high length limb means length is not representable here.
  "  ld x5, 72(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 80(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 88(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  beqz x16, .Lmcopy_range_ok\n" ++
  -- Non-zero length expands/copies both ranges, so offsets must be u64.
  "  ld x5, 8(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 16(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 24(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 40(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 48(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 56(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  -- Frame arena limit into x6 (clobbers x6 only). Tag unique to this site.
  memoryArenaLimitAsm "mcopy" "x6" ++
  -- Detect u64 source/destination end wraparound; both ends ≤ arena limit.
  "  add x5, x15, x16\n" ++
  "  bltu x5, x15, .exit_outofgas\n" ++
  "  bltu x6, x5, .exit_outofgas\n" ++
  "  add x5, x14, x16\n" ++
  "  bltu x5, x14, .exit_outofgas\n" ++
  "  bltu x6, x5, .exit_outofgas\n" ++
  ".Lmcopy_range_ok:\n"

end EvmAsm.Codegen
