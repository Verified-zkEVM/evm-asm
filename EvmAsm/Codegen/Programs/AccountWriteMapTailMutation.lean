/-
  EvmAsm.Codegen.Programs.AccountWriteMapTailMutation

  Extracted from `AccountWriteMapTail.lean` to keep the Codegen/Programs
  file under the FileSizeGuard cap. This module contains the inert,
  runtime-only mutation-boundary observation checkpoint; it is re-exported
  by `AccountWriteMapTail` through its import.
-/

module

public import EvmAsm.Codegen.Emit

@[expose] public section

namespace EvmAsm.Codegen

/-! Runtime-only mutation-boundary observations.  The old map/overlay
    agreement probe and per-reader differential are retired; the remaining
    checkpoint records mutation events for the verdict/control sweep. -/

def accountAgreementMutationEventCapacity : Nat := 1024

/-! A mutation-boundary witness for paths that do not naturally read the
    freshly-mutated balance.  This is a debug-only checkpoint: it is inert
    unless the agreement harness is armed, preserves the caller ABI, and
    records the canonical address plus the raw live `env+32` bytes after the
    mutation.  The metadata word is `{ mutation_id, depth }`; the sequence
    word is the zero-based event index.  It intentionally does not alter the
    production account maps or turn a missing natural read into one. -/
def accountAgreementMutationCheckpointFunction : String :=
  "account_agreement_mutation_checkpoint:\n" ++
  "  addi sp, sp, -96; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd a0, 40(sp); sd a1, 48(sp); sd a2, 56(sp); sd a3, 64(sp)\n" ++
  "  la t0, account_agreement_enabled; ld t1, 0(t0); beqz t1, .Laamc_done; mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  la t0, account_agreement_mutation_event_count; ld t1, 0(t0); li t2, " ++ toString accountAgreementMutationEventCapacity ++ "; bgeu t1, t2, .Laamc_overflow\n" ++
  "  slli t2, t1, 5; slli t3, t1, 6; add t2, t2, t3; la t3, account_agreement_mutation_events; add t3, t3, t2\n" ++
  "  mv t0, s0; addi t4, t3, 0; li t5, 20\n" ++
  ".Laamc_addr:\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; bnez t5, .Laamc_addr\n" ++
  "  mv t0, s1; addi t4, t3, 32; li t5, 32\n" ++
  ".Laamc_balance:\n" ++
  "  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; bnez t5, .Laamc_balance\n" ++
    "  slli t4, s3, 8; or t4, t4, s2; sd t4, 64(t3); sd t1, 72(t3); addi t1, t1, 1; la t0, account_agreement_mutation_event_count; sd t1, 0(t0); j .Laamc_done\n" ++
  ".Laamc_overflow:\n" ++
  "  la t0, account_agreement_mutation_event_overflow; li t1, 1; sd t1, 0(t0)\n" ++
  ".Laamc_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld a0, 40(sp); ld a1, 48(sp); ld a2, 56(sp); ld a3, 64(sp); addi sp, sp, 96; ret\n"

end EvmAsm.Codegen
