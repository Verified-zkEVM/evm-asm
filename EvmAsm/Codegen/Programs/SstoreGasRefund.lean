/-
  EvmAsm.Codegen.Programs.SstoreGasRefund

  SSTORE gas/refund outcome helper matching the Amsterdam execution-specs
  original/current/new-value branches. This is the gas-sensitive storage
  outcome that later descriptor emitters need before writing final storage
  values into the post-state-root path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Stateless.SpecRef.Gas

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## sstore_gas_refund_outcome

    a0 = original value ptr (32-byte BE)
    a1 = current value ptr  (32-byte BE)
    a2 = new value ptr      (32-byte BE)
    a3 = warm flag — **now unused**; retained so the caller's argument setup
         (`Storage.lean`, `seqz a3, x19`) and the probe ABI do not change
    a4 = output ptr

    Output:
      +0  ALWAYS ZERO — retired, see below. The field is kept so the caller's
          hardcoded `+8` and `+32` displacements do not move.
      +8  refund delta i64 encoded as two's-complement u64
      +16 changed flag (current != new)
      +24 accessed-after flag (always 1 for a successful SSTORE access)
      +32 zero-restore state-gas credit flag (original == new == 0 with a
          change → the caller applies credit_state_gas_refund(97920))

    Mirrors the refund-counter branch of
    execution-specs/src/ethereum/forks/amsterdam/vm/instructions/storage.py.

    ## Why there is no gas output (GH #10574, #10576)

    The spec computes gas and refund in **one** function with **one**
    accumulator (`storage.py:66-130`): `gas_cost` starts at zero, the access
    cost is added once cold-or-warm, `STORAGE_WRITE` is added on the
    first-change condition, and the `refund_counter` updates sit in the same
    function driven by the same three-way comparison of original/current/new.

    The guest splits that across two routines, and this one used to re-derive
    the gas cost into a second accumulator **that no caller ever read** —
    `Storage.lean` reads only `+8` and `+32`. Two independent copies of one spec
    quantity is the defect; the dead copy had already drifted, over-counting by
    one `WARM_ACCESS` because it initialised to 100 and then added the full
    access cost. It was repaired by deletion rather than by correcting the
    arithmetic, so the two copies cannot diverge again.

    The regular-gas charge for SSTORE lives in `sstoreValueTransitionGasAsm`
    (`Programs/Storage.lean`), which is the single writer.

    Amsterdam dropped the legacy EIP-2200 SET(20000) split, so the restore
    refund is `STORAGE_WRITE`; the zero-restore case additionally credits state
    gas, surfaced via the +32 flag. -/

def sstoreGasRefundOutcomeFunction : String :=
  "sstore_gas_refund_outcome:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  li s0, 1                    # original_zero\n" ++
  "  li s1, 1                    # current_zero\n" ++
  "  li s2, 1                    # new_zero\n" ++
  "  li s3, 1                    # original_eq_current\n" ++
  "  li s4, 1                    # current_eq_new\n" ++
  "  li s5, 1                    # original_eq_new\n" ++
  "  li t0, 0\n" ++
  ".Lsgr_cmp:\n" ++
  "  li t1, 32; beq t0, t1, .Lsgr_cmp_done\n" ++
  "  add t2, a0, t0; ld t2, 0(t2)\n" ++
  "  add t3, a1, t0; ld t3, 0(t3)\n" ++
  "  add t4, a2, t0; ld t4, 0(t4)\n" ++
  "  beqz t2, .Lsgr_orig_zero_limb\n" ++
  "  li s0, 0\n" ++
  ".Lsgr_orig_zero_limb:\n" ++
  "  beqz t3, .Lsgr_cur_zero_limb\n" ++
  "  li s1, 0\n" ++
  ".Lsgr_cur_zero_limb:\n" ++
  "  beqz t4, .Lsgr_new_zero_limb\n" ++
  "  li s2, 0\n" ++
  ".Lsgr_new_zero_limb:\n" ++
  "  beq t2, t3, .Lsgr_oc_eq_limb\n" ++
  "  li s3, 0\n" ++
  ".Lsgr_oc_eq_limb:\n" ++
  "  beq t3, t4, .Lsgr_cn_eq_limb\n" ++
  "  li s4, 0\n" ++
  ".Lsgr_cn_eq_limb:\n" ++
  "  beq t2, t4, .Lsgr_on_eq_limb\n" ++
  "  li s5, 0\n" ++
  ".Lsgr_on_eq_limb:\n" ++
  "  addi t0, t0, 8\n" ++
  "  j .Lsgr_cmp\n" ++
  ".Lsgr_cmp_done:\n" ++
  -- No gas accumulator here. The regular-gas charge for SSTORE is
  -- `sstoreValueTransitionGasAsm` (`Programs/Storage.lean`), which debits
  -- `568(x20)` directly; this routine computes only the refund delta and the
  -- zero-restore credit flag, which are the two fields its caller reads. See
  -- the header note on why the second accumulator was removed.
  "  li s7, 0                    # refund_delta signed\n" ++
  "  li t2, 0                    # zero-restore state-gas credit flag\n" ++
  "  bnez s4, .Lsgr_store\n" ++
  "  bnez s0, .Lsgr_restore_check\n" ++
  "  bnez s1, .Lsgr_reverse_clear\n" ++
  "  beqz s2, .Lsgr_restore_check\n" ++
  s!"  li t0, {EvmAsm.Stateless.SpecRef.GasCosts.REFUND_STORAGE_CLEAR}\n" ++
  "  add s7, s7, t0\n" ++
  "  j .Lsgr_restore_check\n" ++
  ".Lsgr_reverse_clear:\n" ++
  s!"  li t0, {EvmAsm.Stateless.SpecRef.GasCosts.REFUND_STORAGE_CLEAR}\n" ++
  "  sub s7, s7, t0\n" ++
  ".Lsgr_restore_check:\n" ++
  "  beqz s5, .Lsgr_store\n" ++
  s!"  li t0, {EvmAsm.Stateless.SpecRef.GasCosts.STORAGE_WRITE}                # restore: STORAGE_WRITE\n" ++
  "  add s7, s7, t0\n" ++
  "  beqz s0, .Lsgr_store\n" ++
  "  li t2, 1                    # zero restore: caller credits state gas (EIP-8037)\n" ++
  ".Lsgr_store:\n" ++
  "  sd x0, 0(a4)\n" ++          -- +0 retired: the five-field footprint is kept so
                                 -- the caller's hardcoded +8 and +32 do not move

  "  sd s7, 8(a4)\n" ++
  "  xori t0, s4, 1\n" ++
  "  sd t0, 16(a4)\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 24(a4)\n" ++
  "  sd t2, 32(a4)\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_sstore_gas_refund_outcome`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8   warm flag
      +16  original value (32-byte BE)
      +48  current value (32-byte BE)
      +80  new value (32-byte BE)
    Output layout:
      OUTPUT+0  status
      OUTPUT+8  gas cost
      OUTPUT+16 refund delta i64/two's-complement u64
      OUTPUT+24 changed flag
      OUTPUT+32 accessed-after flag
      OUTPUT+40 zero-restore state-gas credit flag -/
def ziskSstoreGasRefundOutcomePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a3, 8(t0)                # warm flag\n" ++
  "  addi a0, t0, 16             # original\n" ++
  "  addi a1, t0, 48             # current\n" ++
  "  addi a2, t0, 80             # new\n" ++
  "  li a4, 0xa0010008           # outcome payload at OUTPUT+8\n" ++
  "  jal ra, sstore_gas_refund_outcome\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lsgr_pdone\n" ++
  sstoreGasRefundOutcomeFunction ++ "\n" ++
  ".Lsgr_pdone:"

def ziskSstoreGasRefundOutcomeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSstoreGasRefundOutcomePrologue
}

end EvmAsm.Codegen
