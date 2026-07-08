/-
  EvmAsm.Codegen.Programs.SstoreGasRefund

  SSTORE gas/refund outcome helper matching the Amsterdam execution-specs
  original/current/new-value branches. This is the gas-sensitive storage
  outcome that later descriptor emitters need before writing final storage
  values into the post-state-root path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## sstore_gas_refund_outcome

    a0 = original value ptr (32-byte BE)
    a1 = current value ptr  (32-byte BE)
    a2 = new value ptr      (32-byte BE)
    a3 = warm flag (1 if already warm, 0 if cold)
    a4 = output ptr

    Output:
      +0  gas cost u64 (regular gas only; the EIP-8037 state-gas charge for a
          zero-origin creation is accounted by the caller via
          `evm_state_gas_left`/`evm_state_gas_used`)
      +8  refund delta i64 encoded as two's-complement u64
      +16 changed flag (current != new)
      +24 accessed-after flag (always 1 for a successful SSTORE access)
      +32 zero-restore state-gas credit flag (original == new == 0 with a
          change → the caller applies credit_state_gas_refund(97920))

    Mirrors execution-specs/src/ethereum/forks/amsterdam/vm/instructions/storage.py:
    cold surcharge, original/current/new gas branch, and refund counter branch.
    Amsterdam charges the access cost (cold 3000 or warm 100) and, on the first
    change to a slot in the transaction, STORAGE_WRITE = 10000. Restore refunds
    STORAGE_WRITE, and first-time clears use REFUND_STORAGE_CLEAR = 12480. The
    zero-restore case additionally credits state gas, surfaced via the +32 flag. -/
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
  "  li s6, 100                  # gas_cost\n" ++
  "  li s7, 0                    # refund_delta signed\n" ++
  "  bnez a3, .Lsgr_access_warm\n" ++
  "  li s6, 3000\n" ++
  ".Lsgr_access_warm:\n" ++
  "  beqz s3, .Lsgr_warm_access_cost\n" ++
  "  bnez s4, .Lsgr_warm_access_cost\n" ++
  "  li t0, 10000                # clean-changing: STORAGE_WRITE\n" ++
  "  add s6, s6, t0\n" ++        -- (Amsterdam: no SET split; zero-origin creation is EIP-8037 state gas)
  "  j .Lsgr_refund\n" ++
  ".Lsgr_warm_access_cost:\n" ++
  ".Lsgr_refund:\n" ++
  "  li t2, 0                    # zero-restore state-gas credit flag\n" ++
  "  bnez s4, .Lsgr_store\n" ++
  "  bnez s0, .Lsgr_restore_check\n" ++
  "  bnez s1, .Lsgr_reverse_clear\n" ++
  "  beqz s2, .Lsgr_restore_check\n" ++
  "  li t0, 12480\n" ++
  "  add s7, s7, t0\n" ++
  "  j .Lsgr_restore_check\n" ++
  ".Lsgr_reverse_clear:\n" ++
  "  li t0, 12480\n" ++
  "  sub s7, s7, t0\n" ++
  ".Lsgr_restore_check:\n" ++
  "  beqz s5, .Lsgr_store\n" ++
  "  li t0, 10000                # restore: STORAGE_WRITE\n" ++
  "  add s7, s7, t0\n" ++
  "  beqz s0, .Lsgr_store\n" ++
  "  li t2, 1                    # zero restore: caller credits state gas (EIP-8037)\n" ++
  ".Lsgr_store:\n" ++
  "  sd s6, 0(a4)\n" ++
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
