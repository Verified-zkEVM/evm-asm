/-
  EvmAsm.Codegen.MemoryBudgetGuard

  Build-time guard for the memory-budget coincidence (GH #10522, #10535).

  ## Scope: this is the home for constant-relationship invariants generally

  It was created for one such invariant and has since taken on three distinct
  remits: a guard on #10522's unreachability precondition, a guard on the
  achievable steps-per-gas constant `k` that the top theorem's fuel is derived
  from (#10552), and a guard on the clamped fill loop's exit exactness
  (`clampEnd_alignment_*`). **If you need to pin a relationship between guest
  constants that nothing else enforces, add it here rather than starting a
  second file** — and note the new remit in this list, so the next person finds
  it too.

  The test for whether an assertion belongs here is *coincidence vs
  construction*: a relationship that holds because several independently
  editable constants happen to line up is a coincidence and needs a
  kernel-checked pin; one where the check and the checked value are the same
  symbol is maintained by construction and a pin would be redundant ceremony.
  State which of the two you have, and where a bound has both halves, guard
  only the coincidental half and say why the other needs nothing (see the
  nested-vs-depth-0 split on `clampEnd_alignment_*`). Pin the quantity that is
  *used*, not the ones it is computed from — `minRemainingPoolBytes` rather
  than only `evmMemoryPoolBytes`, `SpecRef.MEMORY_PER_WORD` rather than a
  local copy.

  ### Boundary: constants only — link-chosen addresses belong in the ELF gate

  "Constant-relationship" is the literal limit of this file's remit. Every
  statement here is closed by `decide` over values Lean can **see**. An
  invariant that involves an address the **linker** chooses — a symbol's
  address, a section's base or end, `__BSS_END__` — cannot be stated here
  honestly: Lean has no access to the linked image, so a `decide` on such a
  relationship would pin a number nobody had checked against the ELF, which is
  worse than no guard because it *looks* verified.

  Those belong in `scripts/check-region-map.sh`, which already reads the symbol
  table with `readelf` and exists to gate link-layout drift. Worked example
  (GH #10559): "one of the two dense arenas ends exactly at `__BSS_END__`, whose
  neighbour is unmapped space" is a genuine coincidence between an arena size
  (a Lean constant) and a section layout (a linker decision) — so it needs a
  guard, but not one here. It is checked against the ELF instead.

  Rule of thumb: if you cannot write the invariant without naming a symbol or a
  section, it is an ELF-gate invariant. If both sides are `Nat`s defined in
  Lean, it is ours.

  One more transferable lesson from that gate, worth applying to assertions
  here too: **pin the property, not the instance.** #10559 asserts *whichever*
  arena ends at `__BSS_END__`, not that `evm_memory` does — so it stays silent
  through an intended layout change and still fires on accidental drift. A gate
  pinned to the current instance fires on the first deliberate change, gets
  weakened by whoever is making that change, and disappears exactly when the
  thing it protects is in motion.

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
import EvmAsm.Stateless.SpecRef.InstructionsCore
import EvmAsm.Stateless.SpecRef.InstructionsEnv

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

/-! ## Guard 3 — 8-alignment of the clamped fill end (GH #10522)

`updateActiveMemorySizeAsm`'s clamped fresh-zero loop (`clampToArena = true`)
stores with `sd` and steps the pointer by 8, exiting on `bgeu ptr, end`. That
exit is **exact only if the clamped end is 8-aligned**: a misaligned end lets the
pointer step OVER it, so the loop exits having written the 8 bytes at the
previous position — overshooting by up to 7 bytes past the bound the clamp exists
to enforce, i.e. reintroducing a smaller form of the defect it fixes.

Two paths, and only one of them needs a guard:

* **nested** — the clamped end reduces algebraically to `evm_memory_pool_end`
  (`x13 + (pool_end - x13)`), so its alignment is the assembler's `.balign 8`
  rather than arithmetic. Nothing to pin beyond the size below.
* **depth 0** — the end is `x13 + rootRuntimeMemoryArenaLimitBytes`, which needs
  both terms 8-aligned. `x13` is the `.balign 32` `evm_memory` label; the limit is
  a constant, so it is pinned here.

`evmMemoryPoolBytes` is pinned too: `pool_end`'s alignment follows from an
8-aligned base *and* an 8-aligned size, so a size change could break the nested
path even though the base is assembler-aligned. -/

theorem clampEnd_alignment_root : rootRuntimeMemoryArenaLimitBytes % 8 = 0 := by
  decide

theorem clampEnd_alignment_pool : evmMemoryPoolBytes % 8 = 0 := by
  decide

/-- The nested path's clamped end is `pool_end`, whose offset from the pool base
    is the whole pool; both the 32-byte-multiple MSIZE accumulation and the pool
    size must keep it 8-aligned. Stated over the derived floor for the same
    reason `minRemainingPoolBytes` is. -/
theorem clampEnd_alignment_minRemaining : minRemainingPoolBytes % 8 = 0 := by
  decide

/-- A frame can afford ≈ 2.805 MiB (91_917 words), so the guards are not holding
    because memory is unaffordable in general — only past the dense bounds. -/
theorem affordable_memory_is_substantial :
    memoryGasCostWords 91917 ≤ gasCap ∧ gasCap < memoryGasCostWords 91918 := by
  decide

/-! ## Guard 4 — the copy coefficient serves two spec constants (GH #10565)

`copyWordGasAsm` (`Programs/EvmMemoryGas.lean`) charges `3 * ceil32(len)/32` with the
`3` synthesised arithmetically (`slli words, 1` then `add`), and it is the **single**
helper used for both copy families:

* `OPCODE_COPY_PER_WORD` — MCOPY, CALLDATACOPY, CODECOPY, EXTCODECOPY
  (`EvmCalldataHandlers.lean:94`, `EvmCodeHandlers.lean:55`, `EvmExtcodecopy.lean:88`);
* `OPCODE_RETURNDATACOPY_PER_WORD` — RETURNDATACOPY (`NoopReturnData.lean:49`).

The spec keeps these as **two independently editable symbols**
(`execution-specs` Amsterdam `vm/gas.py:218,225`). They are equal today; nothing
enforces that. A fork repricing one family would leave the guest charging the old
shared value for the other, **silently** — no build error, and an EEST sweep would
show only unexplained mispricing on one opcode family. Coincidence class, so pinned.

`copyPerWord_families_agree` is the load-bearing one: when it fails, the fix is to
**split or parameterise `copyWordGasAsm`**, never to edit this theorem.

**The copy coefficient has TWO emission sites, in different files. Fix both.**
`copyWordGasAsm` (`Programs/EvmMemoryGas.lean`) serves CALLDATACOPY / CODECOPY /
EXTCODECOPY / RETURNDATACOPY, and `mcopyDynamicGasAsm`
(`Programs/EvmMcopyGas.lean`) independently synthesises the same `3*words` for
MCOPY (`srli w,5` then `slli w,1` then `add`, twice — once per range). Nothing
links the two, so a reprice needs both edited; `copyPerWord_is_three` below fires
once and does not say how many call sites implement it. That is why this
paragraph exists.
`copyPerWord_is_three` pins the value the emitted `slli`/`add` actually implements,
so a reprice of *both* families also fails loudly rather than mis-charging. -/

theorem copyPerWord_families_agree :
    EvmAsm.Stateless.SpecRef.GasCosts.OPCODE_COPY_PER_WORD
      = EvmAsm.Stateless.SpecRef.GasCosts.OPCODE_RETURNDATACOPY_PER_WORD := by
  decide

theorem copyPerWord_is_three :
    EvmAsm.Stateless.SpecRef.GasCosts.OPCODE_COPY_PER_WORD = 3 := by
  decide

/-! ## Guard 5 — the remaining inline dynamic-gas coefficients (GH #10565)

Every inline helper in `Programs/EvmMemoryGas.lean` synthesises its per-unit cost
as bare arithmetic, with no reference to the spec symbol it implements. All are
**correct today** — verified against `execution-specs` Amsterdam — so these pins
are drift protection, not bug fixes. Each records the emitted arithmetic so a
reader can check the pin against the code it stands for:

| helper | emitted arithmetic | value | spec symbol |
|---|---|---|---|
| `keccakWordGasAsm` | `slli w,2` + `add` + `add` | 6/word | `OPCODE_KECCAK256_PER_WORD` |
| `expDynamicGasAsm` | `li x7, 50; mul` | 50/byte | `OPCODE_EXP_PER_BYTE` |
| `logDynamicGasAsm` | `li x18, topics*375` | 375/topic | `OPCODE_LOG_TOPIC` |
| `logDynamicGasAsm` | `slli x5, x15, 3` | 8/byte | `OPCODE_LOG_DATA_PER_BYTE` |
| `createInitcodeGasAsm` | `li gas, 2` (no salt) | 2/word | `CODE_INIT_PER_WORD` |
| `createInitcodeGasAsm` | `li gas, 8` (salt) | 8/word | **a SUM — see below** |

### CREATE2's 8 is a sum of two independently editable constants

`createInitcodeGasAsm` uses `perWordCost := if hasSalt then 8 else 2`. The spec
(`vm/instructions/system.py:244-250`) charges CREATE2
`OPCODE_KECCAK256_PER_WORD * words + init_code_cost(...)`, i.e. `6 + 2 = 8` per
word, because CREATE2 additionally hashes the initcode; CREATE (`:190-193`)
charges only `init_code_cost`, i.e. `2`.

This is a **worse collapse than the copy case**. There, two constants had to stay
*equal*, and equality is at least a relation someone might notice. Here a single
literal must equal a *sum*, so repricing **either** input silently mis-charges
CREATE2 with nothing to compare against. `create2PerWord_is_sum` states the
decomposition, so the build fails if either summand moves.

When any of these fails, the fix is to **update the helper's arithmetic to match
the new spec value** — never to edit the theorem. For `create2PerWord_is_sum`
specifically, check which summand changed before touching the `8`. -/

open EvmAsm.Stateless.SpecRef.GasCosts

theorem keccakPerWord_is_six : OPCODE_KECCAK256_PER_WORD = 6 := by decide

theorem expPerByte_is_fifty : OPCODE_EXP_PER_BYTE = 50 := by decide

theorem logTopic_is_375 : OPCODE_LOG_TOPIC = 375 := by decide

theorem logDataPerByte_is_eight : OPCODE_LOG_DATA_PER_BYTE = 8 := by decide

theorem createPerWord_is_two : CODE_INIT_PER_WORD = 2 := by decide

/-- CREATE2's hardcoded `8` decomposes as keccak-per-word plus init-code-per-word.
    If this fails, one of the two summands was repriced: fix the `8` in
    `createInitcodeGasAsm`, not this theorem. -/
theorem create2PerWord_is_sum :
    OPCODE_KECCAK256_PER_WORD + CODE_INIT_PER_WORD = 8 := by decide

end EvmAsm.Codegen.MemoryBudgetGuard
