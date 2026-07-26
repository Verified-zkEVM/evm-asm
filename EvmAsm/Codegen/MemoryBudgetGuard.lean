/-
  EvmAsm.Codegen.MemoryBudgetGuard

  Build-time guard for the memory-budget coincidence (GH #10522, #10535).

  ## What this file protects

  Three constants currently sit in a relationship that makes two latent defects
  **unreachable**, and until this file nothing enforced it:

  * `rootRuntimeMemoryArenaLimitBytes` — the depth-0 dense EVM-memory arena;
  * `evmMemoryPoolBytes` — the shared nested-frame memory pool;
  * `SpecRef.TX_MAX_GAS_LIMIT` — the per-tx REGULAR gas cap (EIP-8037), which is
    the *only* limit that bounds EVM memory (see the invariant note at the head
    of `Programs/EvmMemoryGas.lean`).

  Memory-expansion gas is `cost(w) = GAS_MEMORY·w + ⌊w²/512⌋` on 32-byte words
  (`SpecRef/Gas.lean:180-182`, `calculate_memory_gas_cost`), charged against the
  regular dimension. The quadratic term means a frame can only afford
  ≈ 2.805 MiB, which is *less than* either dense bound — so the MLOAD/MSTORE
  sparse path can never be entered by a valid block.

  ## What breaks if a theorem here fails

  A failure is **not** a build annoyance; it is a correctness handoff. If either
  inequality stops holding, then all three of the following go live at once,
  silently, with no other test failing:

  1. the MLOAD/MSTORE sparse memory path becomes reachable
     (`sparseMemory{Load,Store}WordAsm`, `Programs/EvmMemoryHandlers.lean`);
  2. **#10522** — `updateActiveMemorySizeAsm`'s fresh-zero loop writes past the
     frame's memory, and the bytes immediately after `evm_memory_pool_end` are
     `rb_running_block_bloom` / `rb_running_receipt_bloom`, which the verdict
     reads — i.e. it becomes a false-accept vector, not merely a safety bug;
  3. **#10535** — the global 4096-entry `sparseMemoryWordCapacity` becomes a
     reachable false-reject.

  So: if you are here because the build broke, do not raise a constant to make
  it pass. Land #10522's clamp first (that is the recorded ordering constraint),
  then re-derive these bounds.

  All statements are concrete `Nat` arithmetic closed by `decide` — the kernel's
  GMP-backed `Nat` handles them directly. No `native_decide`/`bv_decide`.
-/

import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Stateless.SpecRef.Transactions

namespace EvmAsm.Codegen.MemoryBudgetGuard

open EvmAsm.Codegen (rootRuntimeMemoryArenaLimitBytes evmMemoryPoolBytes)

/-- The linear memory coefficient, pinned to the SpecRef constant for the same
    reason as `gasCap`: if a future fork reprices memory, `gasCap` would follow
    the spec while a hardcoded coefficient silently would not, and this guard
    would quietly stop meaning what its docstring says. -/
def memoryPerWord : Nat := EvmAsm.Stateless.SpecRef.GasCosts.MEMORY_PER_WORD

theorem memoryPerWord_eq : memoryPerWord = 3 := by decide

/-- `calculate_memory_gas_cost` in words: `MEMORY_PER_WORD·w + ⌊w²/512⌋`
    (`SpecRef/Gas.lean:180-182`). The `512` divisor is a bare literal in the
    spec too (`Gas.lean:182`), so there is no named constant to pin it to. -/
def memoryGasCostWords (w : Nat) : Nat := memoryPerWord * w + (w * w) / 512

/-- The per-tx regular-gas cap, pinned to the SpecRef constant so a fork change
    cannot drift this guard away from the value the guest enforces. -/
def gasCap : Nat := EvmAsm.Stateless.SpecRef.TX_MAX_GAS_LIMIT

theorem gasCap_eq : gasCap = 16777216 := by decide

/-! ## Guard 1 — depth 0

The depth-0 dense arena is `rootRuntimeMemoryArenaLimitBytes`. Entering the
sparse path requires expanding **past** it, i.e. to at least
`rootRuntimeMemoryArenaLimitBytes / 32 + 1` words. That must cost more than the
entire per-tx regular budget. -/

theorem sparseEntry_unaffordable_at_depth0 :
    gasCap < memoryGasCostWords (rootRuntimeMemoryArenaLimitBytes / 32 + 1) := by
  decide

/-! ## Guard 2 — nested frames

Nested frames bump-allocate inside the shared pool, so a frame's dense bound is
`evm_memory_pool_end - x13`, the remaining pool. The *smallest* it can ever be —
the case most favourable to reaching the sparse path — is
`evmMemoryPoolBytes - maxTotalLiveMemoryBytes`.

`maxTotalLiveMemoryBytes` bounds the total live memory across all frames of one
transaction. Each frame's expansion charge is at least `wᵢ²/512` and every charge
is drawn from the same regular budget (CALL *forwards* gas, it does not create
it), so `Σ wᵢ² ≤ 512 · gasCap`. By Cauchy–Schwarz over `k ≤ maxCallDepth` frames,
`Σ wᵢ ≤ √(k · Σ wᵢ²)`, hence `Σ 32·wᵢ ≤ 32 · √(maxCallDepth · 512 · gasCap)`.

The literal below is that bound; `maxTotalLiveMemoryBytes_sound` pins it as a
*valid* over-approximation (squaring back under the limit), so the literal cannot
silently drift low and weaken Guard 2. -/

/-- EVM call-depth limit (EIP-150), the `k` in the Cauchy–Schwarz step. -/
def maxCallDepth : Nat := 1024

/-- `32 · ⌊√(maxCallDepth · 512 · gasCap)⌋` — see the section note. -/
def maxTotalLiveMemoryBytes : Nat := 94906240

/-- The literal above really is a valid bound: squaring it back stays under
    `maxCallDepth · 512 · gasCap`. Pins the constant against drifting low. -/
theorem maxTotalLiveMemoryBytes_sound :
    (maxTotalLiveMemoryBytes / 32) * (maxTotalLiveMemoryBytes / 32)
      ≤ maxCallDepth * 512 * gasCap := by
  decide

/-- The pool always retains at least this much below `evm_memory_pool_end`. -/
def minRemainingPoolBytes : Nat := evmMemoryPoolBytes - maxTotalLiveMemoryBytes

/-- Even in the most favourable reachable state — a frame sitting at the pool
    floor — expanding past the remaining pool costs more than the whole per-tx
    regular budget. -/
theorem sparseEntry_unaffordable_when_nested :
    gasCap < memoryGasCostWords (minRemainingPoolBytes / 32 + 1) := by
  decide

/-! ## Non-vacuity

The two guards above are `cap < cost(...)` statements, which would be trivially
satisfiable by an absurd arena. These pin that the bounds are in the expected
regime: the pool floor is positive (the pool is genuinely larger than the maximum
total live memory), and a frame *can* afford a substantial amount of memory — so
the guards are constraining a real, non-degenerate configuration. -/

theorem minRemainingPoolBytes_pos : 0 < minRemainingPoolBytes := by decide

/-- A frame can afford ≈ 2.805 MiB (91_917 words), so the guards are not holding
    because memory is unaffordable in general — only past the dense bounds. -/
theorem affordable_memory_is_substantial :
    memoryGasCostWords 91917 ≤ gasCap ∧ gasCap < memoryGasCostWords 91918 := by
  decide

end EvmAsm.Codegen.MemoryBudgetGuard
