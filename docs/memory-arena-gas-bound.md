# Which gas limit bounds EVM memory? (and what it means for the frame arenas)

*Status: reference note. Resolves a recurring ambiguity and frames the open
arena-sizing decision for `evm-asm-274cr` (the beyond-dense memory-window
false-reject class). Fork = amsterdam, execution-specs pin `40f956fab`.*

## TL;DR

EVM memory is bounded by the **per-transaction REGULAR gas cap
`TX_MAX_GAS_LIMIT = 16_777_216 = 2^24`**, not by the block gas limit. A single
frame can legitimately expand memory to **≈ 2.90 MiB**; beyond that is a
**correct OOG**, not a false-reject. The affordable memory summed over all live
frames on the call stack is **≈ 90 MiB**. Size memory arenas against these
numbers — never against the 200M–500M block gas limit.

## The three gas limits (only one bounds memory)

| limit | value | dimension | bounds memory? |
|---|---|---|---|
| `TX_MAX_GAS_LIMIT` | `16_777_216 = 2^24` | per-tx **regular** | **YES** — memory-expansion gas is charged here |
| per-tx **state** gas (EIP-7778/8037) | separate | per-tx state | no (does not pay for memory) |
| block gas limit (`header.gas_limit`) | ~200M–500M | total block, both dims, all txs | no (BAL / tx-array SSZ sizing only) |

Spec anchors (amsterdam):

- `transactions.py:63` — `TX_MAX_GAS_LIMIT = Uint(16_777_216)`.
- `transactions.py:624` — `if intrinsic.regular > TX_MAX_GAS_LIMIT: raise …`.
- `vm/gas.py::calculate_memory_gas_cost` — memory cost `3·w + ⌊w²/512⌋` (words),
  charged against the **regular** dimension (`gas_left`).
- `stateless_ssz.py:57-81` — the 200M/500M figures are the **block** gas limit
  ("At 500M gas … BAL permits block_gas_limit // 2_000 items"), used to size
  the BAL and tx arrays — unrelated to per-frame memory.

Guest: the `2^24` regular cap is already enforced in `BlockVerdictGasGate`
(`li …, 16777216`, the EIP-8037 `min(TX_MAX_GAS_LIMIT, tx.gas)` inclusion).

## The numbers (from `3·w + w²/512 ≤ 2^24`, `w` = 32-byte words)

- **Max affordable memory, one frame:** `w ≈ 92_681` words ≈ **2.90 MiB**.
  Any offset needing more expansion gas than `2^24` is a legitimate OOG.
- **Per-depth decay:** CALL forwards ≤ 63/64 of remaining gas, so a depth-`d`
  frame's affordable memory ≈ `2.90 MiB · (63/64)^(d/2)`.
- **Total-live bound (all frames on the stack at once):** `Σ wᵢ²/512 ≤ 2^24`
  ⇒ `Σ wᵢ ≤ √(k · 512 · 2^24)` ≈ **90 MiB** at `k = 1024`.

## Why this matters: the current arenas under-serve the affordable bound

- `rootRuntimeMemoryArenaLimitBytes = 4 MiB` (depth 0): **correct** — covers the
  full 2.90 MiB affordable, rejects beyond it legitimately.
- `runtimeMemoryArenaLimitBytes = 128 KiB` (nested): **too small** — a nested
  frame can afford up to 2.90 MiB.
- Sparse word store = `4096 words = 128 KiB` (shared): **too small** — a frame
  can afford ~92_681 beyond-dense words; entries 4097+ hit the capacity bail →
  OOG. So the sparse approach, at today's capacity, *also* false-rejects a frame
  using 256 KiB … 2.90 MiB of memory.

Net: every path caps effective nested-frame memory at ~256 KiB, while the spec
allows ~2.90 MiB — a false-reject band of 256 KiB … 2.90 MiB per nested frame.

## Arena-sizing options to fully close the class (open decision)

All must provision up to ~2.90 MiB/frame and ~90 MiB total-live. Following
execution-specs (flat growable `bytearray`, every window op via
`memory_read_bytes`/`memory_write`), three shapes fit within the RAM window
(`.data` ≈ 473 MiB budget; current frame arena = `0x39000 × 1025` ≈ 228 MiB):

1. **Grow the shared sparse store toward the total-live bound (~90 MiB / ~3M
   words)** + per-opcode sparse-awareness (the `evm-asm-274cr` families).
   One shared region; per-opcode glue; store scans stay O(entries).
2. **Per-depth-decaying static dense arenas (~360 MiB).** Frame `d`'s arena =
   its `(63/64)^d`-affordable max; all window ops work raw, no sparse, class
   closed structurally. Cost: non-uniform frame stride (prefix-sum offsets
   instead of `d · 0x39000`) — a change to the byte-tied `frame_base`
   arithmetic and its proofs; ~360 MiB footprint is tight vs the RAM window.
3. **Dynamic per-frame memory pool (~90 MiB shared).** Bump-allocate a frame's
   arena on descend, free on return; flat per-frame memory, no sparse, tightest
   footprint; pool exhaustion = legitimate OOG. Cost: a runtime allocator +
   save/restore discipline across the call stack.

Trade-off summary: (1) is the least structural change but keeps per-opcode
sparse glue and needs the store grown; (2)/(3) close the class structurally
(no per-opcode work, spec-faithful flat memory) at the cost of a frame-layout /
allocator change. The `evm-asm-274cr` umbrella currently assumes (1); (2)/(3)
would supersede its per-family plan. Decision pending.
