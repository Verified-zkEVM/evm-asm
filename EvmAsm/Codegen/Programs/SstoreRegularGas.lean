/-
  EvmAsm.Codegen.Programs.SstoreRegularGas

  `sstore_regular_gas` (bead nxio8.1) — the exact Amsterdam SSTORE *regular* gas
  cost (the EIP-7778 "block_regular" component; the EIP-8037 state-gas and the
  EIP-3529 refund are accounted separately).

  Per execution-specs amsterdam `vm/instructions/storage.py` (sstore) + `vm/gas.py`:

      gas_cost = 0
      if cold:                              gas_cost += COLD_STORAGE_ACCESS   (3000)
      else:                                 gas_cost += WARM_ACCESS            (100)
      if original == current and current != new:
                                            gas_cost += STORAGE_WRITE          (10000)

  So the four cases are:
      cold  + clean-changing : 3000 + 10000 = 13000
      cold  + otherwise      : 3000          =  3000
      warm  + clean-changing :  100 + 10000 = 10100
      warm  + otherwise      :  100          =   100

  where "clean-changing" = the slot is unmodified this tx (original == current)
  AND the store changes it (current != new). Note Amsterdam dropped the legacy
  EIP-2200 SET(20000)/RESET split for the *regular* cost — the storage-creation
  charge moved to the EIP-8037 state-gas dimension.

  This is a pure computation over the (original, current, new) values that the
  recipient storage preload already stages, plus the cold/warm bit (EIP-2929,
  tracked by `evm_storage_access_gas`). It is the gas leaf the dispatcher's
  SSTORE handler needs to charge the dynamic cost instead of the static-only base
  (the gap documented in nxio8). NOT wired here — soundness-neutral; the handler
  wiring is the follow-up (dispatcher-gas / Dispatch.lean domain).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.U256

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## sstore_regular_gas
    a0 = original value ptr (32-byte BE)   a1 = current value ptr (32-byte BE)
    a2 = new value ptr (32-byte BE)        a3 = is_cold (1 = slot cold this tx, else 0)
    a0 (output) = the Amsterdam SSTORE regular gas cost.
    Calls u256_eq (returns 1 if the two 32-byte buffers are equal). -/
def sstoreRegularGasFunction : String :=
  "sstore_regular_gas:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a1                    # current ptr (for the 2nd compare)\n" ++
  "  mv s1, a2                    # new ptr\n" ++
  "  mv s2, a3                    # is_cold\n" ++
  "  jal ra, u256_eq              # a0,a1 = original,current -> a0 = original_eq_current\n" ++
  "  mv s3, a0                    # s3 = original_eq_current\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, u256_eq   # a0 = current_eq_new\n" ++
  -- gas = (is_cold ? COLD_STORAGE_ACCESS : WARM_ACCESS)
  "  li t0, 100\n" ++
  "  beqz s2, .Lsrg_cold_done\n" ++
  "  li t0, 3000\n" ++                              -- COLD_STORAGE_ACCESS
  ".Lsrg_cold_done:\n" ++
  -- clean-changing = original_eq_current && !current_eq_new
  "  beqz s3, .Lsrg_warm\n" ++                      -- original != current -> warm-access branch
  "  bnez a0, .Lsrg_warm\n" ++                      -- current == new (no change) -> warm-access branch
  "  li t1, 10000; add t0, t0, t1\n" ++              -- STORAGE_WRITE
  "  j .Lsrg_done\n" ++
  ".Lsrg_warm:\n" ++
  ".Lsrg_done:\n" ++
  "  mv a0, t0\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- `zisk_sstore_regular_gas`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : is_cold (u64, 0/1)
      bytes 16..48 : original (32B BE)
      bytes 48..80 : current  (32B BE)
      bytes 80..112: new      (32B BE)
    Output: bytes 0..8 = the SSTORE regular gas cost. -/
def ziskSstoreRegularGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a3, 8(t6)                # is_cold\n" ++
  "  addi a0, t6, 16             # original ptr\n" ++
  "  addi a1, t6, 48             # current ptr\n" ++
  "  addi a2, t6, 80             # new ptr\n" ++
  "  jal ra, sstore_regular_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # gas\n" ++
  "  j .Lsrg_pdone\n" ++
  sstoreRegularGasFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  ".Lsrg_pdone:"

def ziskSstoreRegularGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSstoreRegularGasPrologue
  dataAsm     := ""
}

end EvmAsm.Codegen
