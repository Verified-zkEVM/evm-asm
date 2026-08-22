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
  only the coincidental half and say why the other needs nothing (the unified
  pool-end clamp is maintained by construction). Pin the quantity that is
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

  Two constants currently sit in a relationship that makes two latent defects
  **unreachable**, and until this file nothing enforced it:

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
  it pass. #10522's clamp is already landed in `EvmMemoryGas.lean`; this change
  unifies the depth-0 and nested bound only after that source-side fix, then
  re-derives the remaining pool guards.

  All statements are concrete `Nat` arithmetic closed by `decide` — the kernel's
  GMP-backed `Nat` handles them directly. No `native_decide`/`bv_decide`.
-/

import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Stateless.SpecRef.Transactions
import EvmAsm.Stateless.SpecRef.InstructionsCore
import EvmAsm.Stateless.SpecRef.InstructionsEnv
import EvmAsm.Codegen.Programs.EvmAccessGas
import EvmAsm.Codegen.Programs.EvmStorageAccessGas

namespace EvmAsm.Codegen.MemoryBudgetGuard

open EvmAsm.Codegen (evmMemoryPoolBytes)

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

/-! ## Guard 1 — remaining pool

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
silently drift low and weaken Guard 1. -/

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

/-- Even at depth zero, where the frame starts at the pool origin, crossing the
    shared pool bound costs more than the whole per-tx regular-gas budget.
    This is the depth-0 successor to the former root-arena guard: it pins the
    same sparse-entry property against the bound the emitted code actually
    uses, rather than against a separate private limit. -/
theorem sparseEntry_unaffordable_at_shared_pool :
    gasCap < memoryGasCostWords (evmMemoryPoolBytes / 32 + 1) := by
  decide

/-! ## Non-vacuity

The guards above are `cap < cost(...)` statements, which would be trivially
satisfiable by an absurd arena. These pin that the bounds are in the expected
regime: the pool floor is positive (the pool is genuinely larger than the maximum
total live memory), and a frame *can* afford a substantial amount of memory — so
the guards are constraining a real, non-degenerate configuration. -/

theorem minRemainingPoolBytes_pos : 0 < minRemainingPoolBytes := by decide

/-! ## Guard 2 — 8-alignment of the clamped fill end (GH #10522)

`updateActiveMemorySizeAsm`'s clamped fresh-zero loop (`clampToArena = true`)
stores with `sd` and steps the pointer by 8, exiting on `bgeu ptr, end`. That
exit is **exact only if the clamped end is 8-aligned**: a misaligned end lets the
pointer step OVER it, so the loop exits having written the 8 bytes at the
previous position — overshooting by up to 7 bytes past the bound the clamp exists
to enforce, i.e. reintroducing a smaller form of the defect it fixes.

The clamped end reduces algebraically to `evm_memory_pool_end`
(`x13 + (pool_end - x13)`), so its alignment is the assembler's `.balign 8`
rather than an arithmetic coincidence. Nothing needs pinning beyond the pool
size below.

`evmMemoryPoolBytes` is pinned too: `pool_end`'s alignment follows from an
8-aligned base *and* an 8-aligned size, so a size change could break the nested
path even though the base is assembler-aligned. -/

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

/-! ## Guard 3 — the copy coefficient serves two spec constants (GH #10565)

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

/-! ## Guard 4 — the remaining inline dynamic-gas coefficients (GH #10565)

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

/-! ## Guard 5 — the five gas tiers behind the static table (GH #10569)

`Dispatch.lean:509-558`'s `staticGasCost` prices all 256 opcode bytes with bare
literals and **zero** `SpecRef` references, so nothing links the shipped table to
the spec. Pinning all 256 entries needs a byte→mnemonic mapping that does not
exist in-tree yet; the **tiers** need no such mapping, because they are named
symbols already (`SpecRef/Gas.lean`, `GasCosts` namespace).

This is the cheap high-value slice: five theorems cover every range-based entry in
the table — PUSH0 (`BASE`), PUSH1–32 / DUP / SWAP / DUPN / SWAPN / EXCHANGE and the
whole comparison-and-bitwise block (`VERY_LOW`), the MUL/DIV/SDIV/MOD/SMOD/
SIGNEXTEND/CLZ group (`LOW`), ADDMOD/MULMOD (`MID`), and EXP's base (`HIGH`).
**A fork repricing `VERY_LOW` moves roughly 50 opcodes at once and nothing
currently catches it.**

When one of these fails, the fix is to update the corresponding literals in
`staticGasCost` — never to edit the theorem. Note the table's own trailing
comments already record which tier each opcode belongs to (`-- PUSH0 (BASE)`,
`-- PUSH1..PUSH32 (VERYLOW)`), so the sites to change are locatable.

Scope: this pins the **tier values**, not that each opcode is assigned the right
tier. The latter needs the per-opcode comparison #10569 describes and is not
established here. -/

theorem gasTier_base_is_two : EvmAsm.Stateless.SpecRef.GasCosts.BASE = 2 := by decide

theorem gasTier_veryLow_is_three :
    EvmAsm.Stateless.SpecRef.GasCosts.VERY_LOW = 3 := by decide

theorem gasTier_low_is_five : EvmAsm.Stateless.SpecRef.GasCosts.LOW = 5 := by decide

theorem gasTier_mid_is_eight : EvmAsm.Stateless.SpecRef.GasCosts.MID = 8 := by decide

theorem gasTier_high_is_ten : EvmAsm.Stateless.SpecRef.GasCosts.HIGH = 10 := by decide

/-! ## Guard 6 — the cold/warm access decomposition (GH #10569)

EIP-2929 access gas is charged in **two pieces** by the guest: a flat
`WARM_ACCESS` debited inline, then the cold delta added by
`runtime_access_account_charge` / `evm_storage_access_charge_key` when the address
or slot is newly accessed. The spec states only the totals
(`amsterdam/vm/gas.py:69-71`: `WARM_ACCESS = 100`, `COLD_ACCOUNT_ACCESS = 3000`,
`COLD_STORAGE_ACCESS = 3000`), so the *split* is the guest's own invention and
the sum is what must match.

Four independently editable places participate:

* the inline `li …, 100` (28 sites in the emitted image) — unpinned literal;
* `runtimeAccessColdDeltaGas = 2900` (`Programs/EvmAccessGas.lean:33`);
* `storageAccessColdDeltaGas = 2900` (`Programs/EvmStorageAccessGas.lean:35`);
* the two spec totals above.

The two guest deltas being **separate** constants is correct — the account and
storage paths track distinct spec symbols and should be able to diverge. What was
missing is any tie from either to its spec total, so a fork repricing
`COLD_ACCOUNT_ACCESS` alone would leave both paths charging the old sum.

Same *sum*-decomposition shape as `create2PerWord_is_sum`, and the same failure
instruction: when one of these fails, **fix the guest's delta constant (or the
inline 100), never the theorem** — and check which side of the sum the spec moved
before choosing. -/

theorem warmAccess_is_hundred :
    EvmAsm.Stateless.SpecRef.GasCosts.WARM_ACCESS = 100 := by decide

/-- The account path's split reconstitutes `COLD_ACCOUNT_ACCESS`. -/
theorem accountColdDelta_completes_cold :
    EvmAsm.Stateless.SpecRef.GasCosts.WARM_ACCESS
        + EvmAsm.Codegen.runtimeAccessColdDeltaGas
      = EvmAsm.Stateless.SpecRef.GasCosts.COLD_ACCOUNT_ACCESS := by
  decide

/-- The storage path's split reconstitutes `COLD_STORAGE_ACCESS`. -/
theorem storageColdDelta_completes_cold :
    EvmAsm.Stateless.SpecRef.GasCosts.WARM_ACCESS
        + EvmAsm.Codegen.storageAccessColdDeltaGas
      = EvmAsm.Stateless.SpecRef.GasCosts.COLD_STORAGE_ACCESS := by
  decide

/-! ## Guard 7 — the gas-derived fuel constant `k` (GH #10552)

The top theorem's `fuel` (`runStatelessGuestSound`, obligation 12 / bead `.64`)
must be instantiated with a **gas-derived step cap** `fuel = k · gas_limit`,
where `k` bounds steps-per-gas over all reachable guest paths. Until now `k`
existed only as the adjective "gas-derived" (three prose sites, zero
definitions) — so the quantity that every step-bound audit constrains had
nothing to be checked against, and a path with a worse ratio would surface
only as an unprovable triple far downstream (#10552).

`stepsPerGas` below is a **provisional envelope, not a proven maximum**, and as
of the audit recorded in §7b it is a **known-insufficient** one: it is
constrained from below by the audited ratios pinned next to it, and three
independent mechanisms now exceed it outright — one of them (ECRECOVER) on
every transaction, with no adversarial input required. The contract:

* a new audit that measures a ratio **≤ `stepsPerGas`** adds its
  `measuredStepsPerGas*` constant and `≤`-pin here and changes nothing else;
* one that measures a ratio **above `stepsPerGas`** must either fix the path
  (the KECCAK256 `ceil32` wrap sat at 1.2 × 10⁸ steps/gas before #10521 fixed
  it) or raise `stepsPerGas` **in the same change as the recorded
  measurement** — the ratchet only moves with evidence attached. §7b records
  such paths whose disposition is deliberately *neither* yet: the envelope
  is left at 128 and the exceedance is kernel-checked instead, so the choice
  between path fix and ratchet raise stays visible on #10552 rather than being
  pre-empted by a silent raise;
* consumers (bead `.64`) instantiate `fuelFromGas`, never a bare literal, so a
  ratchet raise reprices the top theorem's fuel automatically.

Coincidence class: the audited ratios and the envelope are independently
editable numbers that nothing else relates, which is exactly this file's
remit (the header has carried the #10552 remit since July; this section
discharges it).

Absolute-capacity note (issue ask 3): the ratio constrains `k`; absolute steps
constrain the prover. At the 200M-gas envelope `fuelFromGas` yields
2.56 × 10¹⁰ steps, above the ≈1 × 10⁹ prover working figure cited in
`Programs/Ripemd160.lean` — a capacity concern tracked on #10548, not a
soundness input to this guard.

Unit note (the open question on #10552): `k` must be denominated in the steps
`cpsHaltTripleWithin`'s `fuel` counts, i.e. the Lean `step` relation, and the
worry was that instruction-level figures are in a different currency because an
accelerator call does far more work than one instruction. It is not a different
currency: `Rv64/Execution.lean:531 step_csrs` makes one accelerator CSRRS
**exactly one** Lean `step`, and both spike and ziskemu retire that CSRRS as one
instruction — so retired-instruction counts and Lean-step counts agree 1:1,
including across the accelerator surface. What an accelerator call costs the
*prover* is real but belongs to the absolute-capacity note above, not to `k`.
Every figure in this section is therefore in `k`'s unit. -/

/-- Memory fresh-zero loop, measured ≤ 5.3 steps/gas (#10521), pinned at its
    ceiling. -/
def measuredStepsPerGasFreshZero : Nat := 6

/-- KECCAK256 absorb, normal path, measured ≈ 6 steps/gas (#10521). -/
def measuredStepsPerGasKeccakAbsorb : Nat := 6

/-- MCOPY byte-copy loop, measured 64 steps/gas (#10521). -/
def measuredStepsPerGasMcopyByteCopy : Nat := 64

/-- EIP-2929 warmth-table scan at its adversarial optimum, measured
    ≈ 114 steps/gas (#10548) — the binding path on current evidence. -/
def measuredStepsPerGasWarmthScan : Nat := 114

/-- MPT walk per cold access at its adversarial optimum: indexed binary-search
    resolution (17 probes over the sorted witness index) at the grinding-limited
    trie depth ≈ 14, analysed ≈ 14 steps/gas on #10547 (2026-08-21 comment),
    pinned at its power-of-two ceiling. The structural ceiling (64-deep path +
    systematic keccak prefix collisions) is unreachable — same disposition as
    the warmth scan's optimum-vs-ceiling split. -/
def measuredStepsPerGasMptWalkCold : Nat := 16

/-- RIPEMD-160 software core (no ZisK accelerator): ~5.3k instructions per
    64-byte block (`Programs/Ripemd160.lean` header; 160 table-driven rounds
    × ~33 instr — RV64 base has no rotate) against the marginal
    `PRECOMPILE_RIPEMD160_PER_WORD` 120 × 2 words = 240 gas ≈ 22 steps/gas,
    pinned with margin. The 600-gas base case is cheaper (~9). -/
def measuredStepsPerGasRipemd160 : Nat := 24

/-- Transaction-RLP decode and the per-calldata-byte tx path, measured
    ≈ 0.29 steps/gas, pinned at 1 (its ceiling).

    Numerator, counted from the emitted asm: the decode of the calldata field
    itself is **O(1) in the calldata length** — `txEip1559Decode_prog`
    indices 107..113 (`Programs/TxDecode1559.lean:247`) record an
    (offset, length) *span* and never touch the payload bytes, and
    `rlp_walk_next` takes the `< 0xc0` byte-string arm
    (`Programs/RlpWalk.lean:176`) which skips `rlp_validate_payload`
    entirely; its only loops are the ≤ 8-iteration length-of-length loops. So
    the decode is ≤ 82 instructions for *any* calldata length. The per-byte
    cost on the tx path is elsewhere: 9 instr/byte in the intrinsic-gas token
    count (`Dispatch.lean:2902`, `.runtime_tx_gas_data_loop`), 7.625 in the
    calldata staging copy plus its arena pre-zero
    (`Programs/BlockVerdictContractStage.lean:129`), and ≈ 2.1 in the keccak
    absorb over the tx envelope (`Programs/HashBridgeProg.lean:182`,
    146 instr per 136-byte block, ~2 passes) — ≈ 18.7 instr per calldata byte.

    Denominator: **64 gas per calldata byte, unconditionally.** EIP-7976 drops
    EIP-7623's zero-byte discount *in the floor* —
    `floor_tokens_in_calldata = data.length * TX_DATA_TOKEN_STANDARD`
    (`SpecRef/Transactions.lean:573`) weights every byte at 4 tokens whatever
    its value, and `calldataFloor` prices each token at
    `TX_DATA_TOKEN_FLOOR = 16` (`SpecRef/Gas.lean:95`), so 4 × 16 = 64;
    `validate_transaction` rejects `calldataFloor > tx.gas`
    (`Transactions.lean:591`) and `Fork.lean:430` charges the floor as the
    minimum. Confirmed by the in-tree `#guard` at `Transactions.lean:796`
    (4 calldata bytes ⇒ `calldataFloor = 21256 = 21000 + 4 × 64`) and by the
    guest asm charging `addi x10, x10, 64` on *both* the zero and non-zero
    arms. All-zero calldata therefore gains an attacker nothing here.

    18.7 / 64 ≈ 0.29 — ~440× inside the envelope. This is the tx half of the
    "RLP/witness decoders" item on #10552's unmeasured list. -/
def measuredStepsPerGasTxRlpDecode : Nat := 1

/-- **`k`** — the steps-per-gas envelope the top theorem's fuel is derived
    from: the smallest power of two above the measured lower bound of 114.
    Raise only together with the measurement that forces it (section note). -/
def stepsPerGas : Nat := 128

/-- The gas-derived step cap: obligation 12 instantiates the top theorem's
    `fuel` as `fuelFromGas gas_limit`, never as a bare literal. -/
def fuelFromGas (gasLimit : Nat) : Nat := stepsPerGas * gasLimit

/-! The ratchet: every audited path's ratio is inside the envelope. A failure
here means a measured ratio moved above `k` — fix the path or raise
`stepsPerGas` with the measurement attached, never edit the pin. -/

theorem freshZero_within_envelope :
    measuredStepsPerGasFreshZero ≤ stepsPerGas := by decide

theorem keccakAbsorb_within_envelope :
    measuredStepsPerGasKeccakAbsorb ≤ stepsPerGas := by decide

theorem mcopyByteCopy_within_envelope :
    measuredStepsPerGasMcopyByteCopy ≤ stepsPerGas := by decide

theorem warmthScan_within_envelope :
    measuredStepsPerGasWarmthScan ≤ stepsPerGas := by decide

theorem mptWalkCold_within_envelope :
    measuredStepsPerGasMptWalkCold ≤ stepsPerGas := by decide

theorem ripemd160_within_envelope :
    measuredStepsPerGasRipemd160 ≤ stepsPerGas := by decide

theorem txRlpDecode_within_envelope :
    measuredStepsPerGasTxRlpDecode ≤ stepsPerGas := by decide

/-! Non-vacuity: an absurdly large `k` would satisfy every `≤`-pin while
making `fuelFromGas` useless, so the envelope is pinned from above too —
within 2× of the binding measured path. Raising `stepsPerGas` past this
bound requires a measurement that moves the binding path with it. -/

theorem stepsPerGas_pos : 0 < stepsPerGas := by decide

theorem stepsPerGas_not_slack :
    stepsPerGas < 2 * measuredStepsPerGasWarmthScan := by decide

/-! ## Guard 7b — measured ratios **above** the envelope (open, #10552)

**Three of the four** subsystems audited off #10552's unmeasured list do not
fit inside `stepsPerGas`. Only the transaction-RLP decode does. Three unrelated
mechanisms:

* **MODEXP** — a software inner loop whose cost grows ~1200× faster than the
  price of the thing it computes. A per-operation ratio, in the same family as
  the warmth scan, just far larger.
* **The curve kernels** — where the standing disposition ("they ride ZisK
  accelerator syscalls, so their step counts are trivial") turned out to be
  **wrong**. The accelerators cover only leaf primitives; every layer above
  them is software. See `ecrecoverStepsPerGasLowerBound`.

**Why a per-operation ratio bounds `k` at all.** This was questioned on #10552
and the answer is yes, by a block-filling argument: if an operation costs `r`
steps per unit of its own gas, an adversary spends the whole gas limit on that
operation and forces `r · gas_limit` steps, so `fuel = k · gas_limit` requires
`k ≥ r`. The earlier retraction on #10552 — that a steps-per-operation-gas
ratio "does not bound `k` at all" because `k` is defined against `gas_limit` —
was too strong. It is right that such a ratio is not *itself* the quantity in
the theorem, and right that a *fixed* per-block cost needs the separate
treatment `blockPrologueStepFloor` gives it; but for an operation that can be
repeated to fill a block, the ratio transfers to `gas_limit` directly.
* **Everything gas does not price at all** — the once-per-block witness / SSZ
  prologue. Two pins cover it, because it has a measured face and an
  adversarial one: `blockPrologueStepFloor` (what real blocks actually spend,
  which is gas-independent) and `witnessIndexStepsPerGasLowerBound` (what a
  witness-shaped input can force, which scales with a quantity no gas schedule
  mentions). Both divide by `LIMIT_MINIMUM = 5000`, and establishing *that*
  denominator is what refuted the "≥ 30M block gas, so < 1 step/gas"
  disposition these subsystems had been dismissed under.

They are recorded here rather than in the `≤`-ratchet above, because the
`≤`-pin would simply be false.

**Direction, and why the names differ.** A `measuredStepsPerGas*` constant is an
*upper* bound on its path's ratio, pinned a little above the measurement, and is
consumed by a `≤ stepsPerGas` pin. The constants here are the opposite: each is
a **lower** bound on a ratio, pinned deliberately *below* the measurement, and
consumed by a `<`-pin in the other direction. Same-prefix naming would invite
someone to move one into the ratchet above and get a theorem that says the
reverse of what it looks like, so these carry `…LowerBound` / `…Floor` names.
Pinning below the central estimate is the point: it makes each exceedance
robust to the one inferred parameter in its derivation (see each docstring), so
the conclusion does not rest on the inference.

**Disposition — read this before "fixing" anything here.** The §7 contract
offers two responses to a ratio above the envelope: fix the path, or raise
`stepsPerGas` with the measurement attached. This change takes **neither**, on
purpose. A `k` large enough to absorb these (≳ 2¹⁸ on the central estimates)
would satisfy every pin while making `fuelFromGas` useless — `fuel` would
exceed the ≈1 × 10⁹ prover working figure at any realistic gas limit — and
would break `stepsPerGas_not_slack`, which is doing its job by refusing.
Fixing either path is separate work with a design choice in it. So the
envelope stays at 128 and the exceedance is made a
build-time fact instead, which is the honest state: **`stepsPerGas` is not a
sound `k` today, and this section is why.**

**These theorems ratchet in the useful direction.** `modexp_exceeds_envelope`
fails if MODEXP is fixed to within the envelope — at which point the constant
belongs in §7's ratchet, not here, and the failure is what tells you to move it.
Likewise `fuelFromGas_insufficient_at_minimum_gas_limit` fails once `fuel`
grows an additive gas-independent term (see below), which is the intended
resolution of that one. Neither is a pin you should weaken in place. -/

/-- **MODEXP (0x05): ≥ ~6.1 × 10³ steps/gas**, ~48× outside the envelope — the
    largest *per-operation* ratio measured anywhere (the witness prologue below
    is larger still, but is not an operation and is not priced at all).
    Software, reachable, and priced by a formula whose shape is right and whose
    constant factor is off by ~1200×.

    Implementation: pure RV64, no accelerator. `zkvm_modexp` has exactly one
    definition (`Programs/ModexpBackend.lean:207`), contains no `ecall`, and
    both call sites reach it by `jal` (`Programs/Modexp.lean:228`, `:353`).
    (`Evm64/Accelerators/SyscallIds.lean:59` declares `modexp = 0x105`, but that
    is a declared host interface in the `0x100` band, not the `0x800..0x819`
    accelerator surface, and nothing in `Codegen` emits an ecall with it.)
    Reachable: `Dispatch.lean:2034` and `:3268` splice
    `zkvmModexpBackendImpl` into the guest text, and
    `Programs/PrecompileRuntime.lean:807` routes precompile address 5 to it.

    Numerator basis — the cost is dominated by `modexp_binmod`
    (`ModexpBackend.lean:141`), which reduces by **bit-serial long division
    over the full dividend width, with no leading-zero skip**: `slli t1, a1, 6`
    / `addi s5, t1, -1` (`:153`) sets the counter to `na·64 − 1` and
    `.Lmbinm_bit` counts it down to zero. Each bit re-shifts the whole
    remainder — `.Lmbinm_shift` (`:158`) is 12 instructions per limb over
    `nm+1` limbs — plus a `modexp_cmpge` call and a conditional `nm`-limb
    `modexp_sub`. Counting only the instructions that execute unconditionally
    gives a floor of ≈ 93 instr/bit at `nm = 4` (62 for the shift loop, 5
    prologue, 10 bring-in, 4 high-limb check, 4 + ≥5 for the compare call, 3
    loop overhead), so one reduction of a `2·nm`-limb product costs
    ≥ 512 × 93 ≈ 4.8 × 10⁴ instructions. The schoolbook `modexp_mul`
    (`:114`, ≈ 20·nm² + 25·nm) is ~120× cheaper and is noise here.

    Denominator basis — `SpecRef/Precompiles.lean:96`..`113`:
    `complexity = if max(B,M) > 32 then 2·words² else 16`,
    `iterations = max 1 (bitlen(head) − 1)` for `E ≤ 32`, and
    `gas = max 500 (complexity · iterations)`. There is no `GQUADDIVISOR` and
    no 200-gas floor in tree; 500 is the only floor. The guest re-implements
    the same formula in asm (`PrecompileRuntime.lean:778`, `:792`).

    Worst case over the domain, and it is **not** the largest input: take
    `B = E = M = 32` (192 bytes of calldata) with exponent `2³³ − 1`. Then
    `max(B,M) = 32` is *not* `> 32`, so `complexity = 16`, and
    `iterations = 33 − 1 = 32`, giving `gas = max 500 (16 · 32) = 512`
    (checked by evaluating the SpecRef functions, not by reading them). The
    guest meanwhile runs 33 squarings + 33 multiplies, each a full 256-bit
    modmul: `66 × 4.8 × 10⁴ ≈ 3.1 × 10⁶` instructions. `3.1 × 10⁶ / 512
    ≈ 6.1 × 10³ steps/gas`. Central estimate with a ~50% subtract rate is
    ≈ 9.1 × 10³; the pin uses 2¹² = 4096, below even the floor, so the
    exceedance does not depend on the subtract-rate inference.

    Two structural reasons the maximizer is small, both worth keeping in mind
    if this is repriced rather than fixed: for `E ≤ 32` the formula charges one
    iteration per exponent bit while `E > 32` charges two
    (`16·(E−32)` over `8·E` bits), and the 500-gas floor pins the price while
    the guest still does 33 real modmuls. The largest-modulus shape
    (`B = M = 1024`) is *better*, ≈ 2.5 × 10³, because `2·words²` grows at the
    same order as the guest's `≈ 2452·nm²` — which is the tell that the fix is
    a path fix: the gas formula already has the right shape, so replacing the
    bit-serial division with Montgomery (or even limb-wise Knuth) reduction
    closes the gap directly. The ratio *is* bounded — EIP-7823's 1024-byte cap
    is enforced at `Programs/Modexp.lean:36` and `SpecRef/Precompiles.lean:118`
    — just bounded at ~10⁴ rather than at 128. Absolute capacity is a separate
    problem: the largest-everything shape is ~6.7 × 10¹¹ steps against the
    ≈1 × 10⁹ prover working figure. -/
def modexpStepsPerGasLowerBound : Nat := 4096

/-- **The ≥ 30M block-gas denominator claimed for the once-per-block witness /
    SSZ decode is refuted: the smallest admissible block gas limit is 5000.**

    The claim under test was that the witness/SSZ decode and index build are
    amortized once per block and therefore < 1 step/gas against ≥ 30M of block
    gas. The numerator is not the problem; the denominator is. Two things are
    wrong with it.

    First, `fuel = k · gas_limit` divides by the gas **limit**, not by gas
    *used*, so the denominator is whatever limit a block may legally carry —
    and `check_gas_limit` (`SpecRef/SeamShell.lean:200`) accepts any limit down
    to `GasCosts.LIMIT_MINIMUM = 5000` (`SpecRef/Gas.lean:104`), pinned by the
    spec's own `#guard check_gas_limit 4999 30000000 == false`
    (`SeamShell.lean:481`). This is not a spec-side abstraction the guest fails
    to implement: `check_gas_limit` is a **proven** guest routine at
    `GuestAddrs.check_gas_limit`, called from `validate_header`
    (`Programs/ValidateHeader.lean:80`) and tied to the SpecRef function
    including `LIMIT_MINIMUM` (`Programs/CheckGasLimitBridge.lean:74`). So
    5000, not 30 × 10⁶, is the denominator `k` must survive. (`HeaderBaseFee`'s
    header comment already states the 5000 minimum independently.)

    Second, the once-per-block work is a **gas-independent constant**, so
    dividing it by any gas figure is a category error dressed as a ratio — and
    `GuestPhaseLayout` (`Codegen/Proofs/TopComposition.lean:357`) already has
    the right shape for it: `budgetDecode` and `budgetWitness` are separate
    additive summands of `fuel`, not multiples of the gas limit.

    The measured constant: ~5.1–5.5 × 10⁶ retired instructions across five real
    blocks whose gas limits span 8×, essentially flat (#10552, 2026-08-21
    comment) — taken with `scripts/spike/spike_run` under `SPIKE_COMMITLOG`,
    one line per retired instruction, 5,437,182 lines on the counted block.
    This constant is pinned at the *smallest* of the five (5,081,997) so the
    `<` below is conservative. **I did not re-run that measurement**: the
    instrument is in tree but neither `spike_run` nor a guest ELF is built in
    this checkout, so the numerator here is cited, not reproduced. The 5000 and
    the arithmetic are mine.

    `fuelFromGas 5000 = 640000 < 5081997`: at the minimum legal gas limit the
    current envelope buys ~1/8 of the steps the guest spends before it looks at
    a transaction. Expressed as a ratio the once-per-block floor alone is
    ≈ 1016 steps/gas there, ~8× the envelope. The clean resolution is the
    additive one — `fuel = C + k · gas_limit`, which the six-budget shape
    already supports — rather than a `k` inflated to absorb a constant. -/
def blockPrologueStepFloor : Nat := 5081997

/-- **The witness-index build is unpriced work: ≥ ~3.7 × 10³ steps/gas at the
    minimum legal gas limit.** This is the same refutation as
    `blockPrologueStepFloor` seen from the other side — that constant is the
    *measured* per-block floor on real blocks, where witnesses are small; this
    one is the *adversarial* figure, because the index build scales with the
    witness record count `N` and **no gas is charged for witness size at all**.

    `N` is capped at 131072 in asm — `LUI x6, 32` (32 ≪ 12) then
    `BLTU x6, x18 → fail` at `Programs/MptWitnessIndex.lean:285`, mirrored for
    `witness_codes_index_build` at `Programs/WitnessCodeLookup.lean:514`. The
    512 KiB `bsrMaxWitnessBytes` guard (`Programs/BlockVerdictParams.lean:133`)
    does **not** bound this work: it is checked inside
    `block_state_root_pre_accounts` (`Programs/BlockVerdictStateRoot.lean:81`),
    while `witness_index_build` is called much earlier from
    `stateless_verdict_v2` (`BlockVerdictStateRoot.lean:507`) with no size check
    between it and `extract_witness_state_section`. So the sort runs to
    completion before the byte guard can reject.

    The sort itself is fine — `witnessIndexBuild_prog`
    (`MptWitnessIndex.lean:217`) is a genuine heapsort: bottom-up heapify at
    indices 101..107 (`SRLI x20, x18, 1`, then `N/2` `widx_sift_down` calls)
    followed by `N−1` extract-max iterations at indices 109..124, with
    `widxSiftDown_prog` (`:121`) a real sift-down. O(N log N), not O(N²).

    Conservative numerator, using only loops whose body I counted and whose
    trip count is exactly `N` — no analytic sum-of-depths, no keccak estimate,
    no sift-down work at all: the record-fill loop at 33 instr × 131072
    ≈ 4.3 × 10⁶, plus extract-max's straight-line body at 109 instr × 131071
    ≈ 1.43 × 10⁷, totalling **≥ 1.86 × 10⁷ instructions**. Counting the
    sift-down descents (≥ 156 instr per level) and the per-record
    `zkvm_keccak256` brings the state index to ≈ 4.1 × 10⁸ and the pair of
    indices to ≈ 8 × 10⁸, but that estimate is not what the pin rests on.

    `1.86 × 10⁷ / 5000 ≈ 3.7 × 10³ steps/gas`; at the ≈ 8 × 10⁸ figure it is
    ≈ 1.6 × 10⁵. Pinned at 2¹¹ = 2048, below even the conservative floor.

    A second, wholly independent refutation needing none of the above:
    `ssz_pack_bytes` (`Programs/Ssz.lean:373`) copies **7 instructions per
    byte** (loop indices 3..9 — `BEQ`/`LBU`/`SB`/3×`ADDI`/`JAL`), not the
    "~L instructions" its docstring at `:372` claims, and its stated
    `0 ≤ L ≤ 1024` is prose with no `li`/`bgtu` behind it. At the 512 KiB
    witness that is 3.67 × 10⁶ instructions ⇒ ≈ 734 steps/gas against a
    5000-gas limit, from one loop.

    Reachability of the large-`N` case was checked, not assumed: the input body
    runs from `INPUT_ADDR = 0x40000000` to `Rv64.MEM_END = 0x78000000`
    (`Stateless/EntrySpec.lean:88`, `:97`), and that whole span is admitted by
    the **first** disjunct of `Rv64.isValidMemAddr` (`MEM_START ≤ a ≤ MEM_END`,
    `Rv64/Word.lean:111`). The 8 KiB `INPUT_MEM_END` disjunct is a redundant
    legacy subset of it, *not* an 8 KiB input cap — so `MAX_INPUT_BYTES`
    (≈ 896 MiB) is genuinely addressable and a 131072-record witness fits.

    Two stale in-repo figures found while measuring this, both making the path
    look cheaper than it is: `BlockVerdictParams.lean:129` cites the index node
    cap as "8192" (actual 131072, 16× off), and `Ssz.lean:372`'s per-byte claim
    above. Neither is load-bearing for a proof; both mislead anyone pricing
    this path from the comments. -/
def witnessIndexStepsPerGasLowerBound : Nat := 2048

/-- **The curve kernels do NOT ride accelerator syscalls above the leaf
    primitives, and 10 of 14 curve precompile paths exceed the envelope.** This
    corrects the disposition #10552 carried: "secp256k1 / bn254 / bls12-381 ride
    ZisK accelerator syscalls (0x800..0x819), so their step counts are trivial."
    The premise is half true and the conclusion does not follow.

    What the accelerators actually cover, from the authoritative table at
    `Rv64/ZiskAccel.lean:25`..`58` (whose closing note says it "closes the full
    set of accelerator ids the guest emits"): one modmul (`Arith256Mod` 0x802,
    `Arith384Mod` 0x80B), one affine add/double per curve (0x803/4, 0x806/7,
    0x80C/D), and Fp2 add/sub/mul (0x808..0x80A, 0x80E..0x810). **There is no
    inversion, no square root, no scalar-multiplication, no pairing, and no
    P-256 accelerator of any kind.** So the ladders, Miller loops, final
    exponentiations, and the BE↔LE operand marshalling around every leaf call
    are all software. (`Programs/Ripemd160.lean:9` loosely lists "secp256r1"
    among the accelerators; that prose is wrong — the table has no such entry.)

    The `…FieldMulModPSAsm` / `…PointDoubleSAsm` file names are *not* evidence
    of software field arithmetic, which was the obvious hypothesis: they are
    verified SAsm wrappers *around* the syscall
    (`Programs/Secp256k1FieldMulModPSAsm.lean:16` is `csrs 2050`,
    `Secp256k1PointDoubleSAsm.lean:20` is `csrs 2052`). The software is one
    level up, in the callers.

    **This constant pins ECRECOVER**, chosen over the worse paths because it is
    the one that is not adversarial at all — every transaction performs a sender
    recovery. `secp256k1_recover_pubkey_staged` (`Programs/TxPubkey.lean:580`)
    runs an R-decompression sqrt ladder, a `secf_inv_mod_n` Fermat inversion,
    and two 256-iteration `secp256k1_scalar_mul` double-and-add ladders
    (`Programs/Secp256k1Curve.lean:315`). Its own docstring
    (`TxPubkey.lean:468`) puts one full recovery at **~2 × 10⁶ ziskemu steps**
    *with the accelerators credited* — a figure independently corroborated
    twice: by a bottom-up instruction count agreeing to ~15%, and by the
    ~5.4 × 10⁶-step whole-block spike measurement on #10552, of which recovery
    is the documented bulk. Against `PRECOMPILE_ECRECOVER = 3000`
    (`SpecRef/Gas.lean:98`) that is ≈ 667 steps/gas; pinned at 2⁹ = 512.
    Reachability is not in doubt — `ecrecover_backend_ptr` is armed with the
    real backend at `Programs/BlockVerdictDispatchTx.lean:684`.

    The other paths measured, for the record (ratios are estimates with roughly
    ±2× uncertainty on the pairing/G2 figures; the classification is not
    uncertain): **P256VERIFY 0x100 ≈ 3.3 × 10⁴** — the worst, because
    `p256_point_dbl` calls `p256_pow` with exponent `p256_pm2_be`, i.e. a **full
    256-iteration Fermat inversion on every single point doubling**
    (`Programs/P256Verify.lean:663`; verified directly, and `:8` states there is
    no P-256 accelerator), inside a 256-doubling scalar ladder, twice per
    verify, against `PRECOMPILE_P256VERIFY = 6900`
    (`SpecRef/PrecompilesCurve.lean:106`); KZG point-evaluation ≈ 2.3 × 10³;
    BLS12 pairing ≈ 1.3 × 10³; BN254 pairing ≈ 7.9 × 10²; BLS12 MAP_FP2_TO_G2
    ≈ 6.2 × 10²; BLS12 G2MSM ≈ 5.2 × 10²; EIP-7702 per-auth recovery ≈ 2.3 ×
    10². Inside the envelope: BN254 ECADD ≈ 43 and ECMUL ≈ 77, BLS12 G1ADD ≈ 23,
    G2ADD ≈ 30, G1MSM ≈ 14, MAP_FP_TO_G1 ≈ 9.

    The split is instructive and points at the fix: the cheap paths are cheap
    because they stay in the accelerator's native limb layout, and BLS12 G1
    documents that as a deliberate ~25× win (`Programs/Bls12G1.lean:943`),
    while the expensive ones pay a Fermat inversion inside an inner loop
    (P-256, and `blsg2_fp_inv`'s 384-iteration ladder called from inside
    `blsg2_point_dbl`, `Programs/Bls12G2.lean:675`) or re-marshal BE↔LE around
    every leaf call (~960 instr/point-op in `bnc_scalar_mul`). None of that is
    an accelerator gap; it is projective-coordinate and layout work that the
    cheap paths already show how to do. -/
def ecrecoverStepsPerGasLowerBound : Nat := 512

/-- MODEXP's measured ratio is outside the envelope. Fixing the path (not
    weakening this) is what closes it; see §7b's disposition note. -/
theorem modexp_exceeds_envelope :
    stepsPerGas < modexpStepsPerGasLowerBound := by decide

/-- The witness-index build's ratio at the minimum legal gas limit is outside
    the envelope too. Unlike MODEXP this one is not a slow inner loop but
    *unpriced* work — gas never mentions witness size — so the fix is a charge
    or a cap, not a faster sort. -/
theorem witnessIndex_exceeds_envelope :
    stepsPerGas < witnessIndexStepsPerGasLowerBound := by decide

/-- ECRECOVER's ratio is outside the envelope, and unlike the other two this
    path is on **every** transaction — there is no adversarial input to
    disallow. It is also the mildest of the curve findings; see the docstring
    for the ones up to ~50× worse. -/
theorem ecrecover_exceeds_envelope :
    stepsPerGas < ecrecoverStepsPerGasLowerBound := by decide

/-- At the minimum legal block gas limit, `fuelFromGas` does not cover the
    measured gas-independent per-block step floor. -/
theorem fuelFromGas_insufficient_at_minimum_gas_limit :
    fuelFromGas EvmAsm.Stateless.SpecRef.GasCosts.LIMIT_MINIMUM
      < blockPrologueStepFloor := by
  decide

/-- Non-vacuity for the pin above: the shortfall is a property of the envelope
    at a small gas limit, not of `fuelFromGas` being degenerate — the same
    formula does cover the floor once the limit is large enough, so the pin
    distinguishes a real configuration rather than holding everywhere. -/
theorem fuelFromGas_sufficient_at_forty_thousand_gas :
    blockPrologueStepFloor ≤ fuelFromGas 40000 := by decide

end EvmAsm.Codegen.MemoryBudgetGuard
