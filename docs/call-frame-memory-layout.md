# Nested CALL/CREATE frame memory layout (depth-indexed pre-allocated frame array)

> **STATUS (2026-08-02): historical design record; current emitted geometry is
> summarized below and the Lean sources are authoritative.**
> The live authorities are `EvmAsm/Codegen/CallFrameLayout.lean` (constants,
> re-pinned to the emitted geometry by #9852), `EvmAsm/Codegen/RegionMap.lean`
> (region extents + overlap inventory, ELF-drift-guarded), and
> `EvmAsm/Codegen/CallFramePhase.lean` + `docs/4ch8f-callframe-audit.md`
> (the union-aliasing soundness story). Specifically superseded here:
> (1) §5's grep-based "SOUNDNESS GATE" is replaced by the verified
> phase-ownership model + the Own-not-Is / sequencing audits; (2) the union now
> coalesces FIVE Phase-H children, inventoried in `RegionMap.dataUnionChildren`;
> (3) `bv_system_storage_log` is standalone because it is read post-dispatch.
> Older seven-child tables and `0x39000`/228 MiB figures below are historical
> snapshots; trust the Lean constants + `scripts/check-region-map.sh`.

> **Current emitted artifact:** `frameStride = 0x19000`,
> `frameArrayBytes = 1025 × 0x19000 = 104,960,000 B` (about 100.1 MiB), with
> a 96 MiB `evm_memory_pool` immediately after the frame arena. The five
> coalesced children are `basr_values`, `basr_accounts`, `baap_storage_desc`,
> `baap_storage_paths`, and `baap_storage_values`; the standalone system log
> is 4 MiB. Current linked anchors are `call_frame_arena = 0xadd053a0`,
> `evm_memory_pool = 0xb411e3a0`, and `.sszscratch = 0xbf980000`.

Design for bead `evm-asm-fhsxz.2.4.2.61.2` (P0, foundational). Owner: claude-c2.
This settles the guest `.data` layout and register conventions for nested EVM
call frames up to the protocol depth limit (1024) **before** the
`.61` frame-execution skeleton is built, so the CALL/CREATE/RETURN/REVERT
handlers and the post-state merge/revert are written once against a fixed map.

Status: DESIGN (no code yet). Downstream consumers: `.61` skeleton,
`.61.1` CALL-family EEST frontiers, `.61.1.5` child-frame handler wiring,
`kpvxz` (STATICCALL+CREATE+SELFDESTRUCT-in-init).

---

## 1. Goal and constraints

- Support EVM call nesting **depth 0..1024** (**1025 frames**) for CALL, CALLCODE,
  DELEGATECALL, STATICCALL, CREATE, CREATE2 — each frame with its own EVM
  memory, operand stack, PC, code base, calldata view, returndata, and the
  per-frame env fields — without frames clobbering each other.
  - Spec (execution-specs amsterdam): top-level message `depth=Uint(0)`
    (`fork.py:859`); a call/create from depth `d` is rejected iff
    `d + 1 > STACK_DEPTH_LIMIT` where `STACK_DEPTH_LIMIT = Uint(1024)`
    (`vm/instructions/system.py:116,333`, `vm/interpreter.py:70`). So a call from
    depth **1023 succeeds** (child at depth 1024 executes); a call from depth
    **1024 fails** (push 0, no child). `process_message` raises only when
    `depth > 1024` (`vm/interpreter.py:278`). ⇒ executing depths are **0..1024 =
    1025 slots**. (This is the easy off-by-one — the limit is on the *child*
    depth, and depth is 0-based.)
- The guest runs under a **fixed, statically-linked memory map** (no runtime
  allocator). From `EvmAsm/Codegen/Driver.lean:83` and the EEST harness
  (`scripts/codegen-eest-stateless-check.sh:491`):
  - `.text`      @ `0x80000000`
  - `.data`      @ `0xa3000000`
  - `.sszscratch`@ `0xbf980000`
  - ⇒ usable `.data` span before `.sszscratch` = `0xbf980000 − 0xa3000000`
    = `0x1c980000` = `479,723,520` B = **457.5 MiB** (≈ 480 MB decimal).
    (Pinned + proved in `EvmAsm/Codegen/CallFrameLayout.lean:244`
    `data_gap_bytes` by `decide`. The total reserved NOBITS footprint of the
    emitted guest ELF, per `readelf -SW`, is `.bss` `0x1c101b40` +
    `.sszscratch` `0x680000` ≈ **482 MB**;
    the ziskemu RAM region is 512 MiB (`0xa0000000..0xc0000000`,
    CODEGEN.md:149) — the relevant ceiling for any new reserved arena.)
- Amsterdam caps: `MAX_CODE_SIZE = 0x10000` (64 KiB), `MAX_INIT_CODE_SIZE =
  0x20000` (128 KiB).
- This project **avoids misaligned load/store** — every per-frame sub-region is
  aligned, and `FRAME_STRIDE` is a multiple of 32.

Design principle: **don't touch depth-0; pre-allocate frames 1..1024.**
`frame[0]` IS the existing single-frame dispatcher state (`evm_memory` / the
operand stack / `evm_env`), left **completely unchanged** — depth-0 is the only
currently-executed path and the verdict-critical one, so it must stay
byte-identical. Frames **1..1024** (the nested children) live in the overlay
arena: `frame[d] = call_frame_arena + (d-1) * FRAME_STRIDE` for `d ≥ 1`
    (1024 slots × `FRAME_STRIDE`; current emitted geometry is 100.1 MiB). A CALL descends by
bumping a depth counter and, for `d ≥ 1`, computing the child register bases
from `call_frame_arena + (d-1)*FRAME_STRIDE`; the parent of a depth-1 child is
`frame[0]` (the existing `evm_memory`/env). This **avoids rebasing the
verdict-critical dispatcher onto the union** (and its `frame[0]` zero-init and
cross-build-unit aliasing hazards): `frame[0]` keeps its pre-zeroed `.data`
buffers, and only child frames (depth ≥ 1) draw from the replay-dirtied union, so
the CALL handler zero-inits child memory on descent (inherent to EVM
fresh-zero-per-frame semantics) — no special transition memset of `frame[0]`.
No copying of code (referenced via the
witness) and no copying of calldata (aliased into the parent's memory).

---

## 2. Current single-frame layout (ground truth)

From `EvmAsm/Codegen/Dispatch.lean:1525-1600` (`emitDispatcherDataSection`) and
the register conventions in `EvmTinyInterp.lean`:

| Region | Size | Reg | Notes |
|---|---|---|---|
| `evm_code` | bytecode | x10 (PC) base | baked bytecode; will become x21→witness.codes slice |
| `evm_memory` | `0x20000` (128 KiB) | x13 (memBaseReg), grows ↑ | EVM memory |
| `evm_env` | 656 B | x20 (env base) | **mixed** per-frame + shared fields (see §3) |
| `evm_blob_hashes` | 512 B | — | 16 × 32 B tx blob versioned hashes (SHARED) |
| `evm_block_hashes` | 8192 B | — | 256 × 32 B recent BLOCKHASH ancestors (SHARED) |
| `evm_event_logs` | 4096 B | — | 16 × 256 B bounded LOG descriptors (SHARED log list) |
| selfdestruct / 7708 / storage-gas / precompile / modexp / sha256 scratch | varies | — | SHARED helper scratch |
| `zk3_state` | 200 B | — | keccak permutation state (SHARED) |
| account-witness data | varies | — | SHARED |
| `lp64_stack` | `0x40000` (256 KiB) | x2 (sp) | helper-call stack for KECCAK/RLP/MPT/account (SHARED) |
| `evm_stack_guard_low` | 512 B | — | guard |
| `evm_stack_low` | 32 KiB (1024×32) | x12 (sp), grows ↓ from `evm_stack_top` | EVM operand stack |
| `evm_stack_top_guard` | 512 B | — | guard |
| `opcode_handlers` | 2 KiB (256×8) | — | dispatch jump table (SHARED) |

Constants (`Dispatch.lean:47-51`): `evmStackWordCapacity=1024`,
`evmStackWordBytes=32` ⇒ `evmStackScratchBytes=32768`; `evmStackGuardBytes=512`.

Register conventions (today, single frame): `x10`=PC, `x12`=operand stack
pointer (grows down), `x13`=memBaseReg (EVM memory base), `x20`=env base,
`x21`=code base, `x2`=lp64 helper sp.

---

## 3. Per-frame vs shared partition

The current `evm_env` (656 B) **interleaves** per-frame execution context with
shared tx/block env. The design splits it. Offsets are the existing ones
(`Dispatch.lean:1803-1808`, `:1561-1569`) so handler code keeps working:

### Per-frame env fields (replicated × depth)
| Offset | Field | Why per-frame |
|---|---|---|
| 0 | ADDRESS | executing account (changes on CALL/DELEGATECALL distinctly) |
| 32 | SELFBALANCE | balance of executing account |
| 64 | CALLER | caller address (msg.sender) |
| 96 | CALLVALUE | msg.value (0 for DELEGATECALL/STATICCALL) |
| 416/424 | calldata ptr / len | child's calldata view (aliased into parent mem) |
| 448–480 | log checkpoints (M22/M24/M26) | per-frame revert rollback point |
| 496 | codeSize (M33) | running code length (CODESIZE/CODECOPY) |
| 568 | gasRemaining (M30) | per-frame gas (63/64 rule on entry) |

### Shared env fields (single instance)
| Offset | Field |
|---|---|
| 128 | ORIGIN (tx) |
| 160 | GASPRICE (tx) |
| 192/224/256/288/320/352/384 | COINBASE/TIMESTAMP/NUMBER/PREVRANDAO/GASLIMIT/BASEFEE/CHAINID (block) |
| 512 | BLOBBASEFEE (M28, block) |
| 544 | blobHashCount (M28) |
| 552/560 | BLOCKHASH current/count (M29) |
| 576–616 | account-witness context (M31) |
| 624–655 | SLOTNUM (EIP-7843) |

Shared also: `evm_blob_hashes`, `evm_block_hashes`, `evm_event_logs` (the global
LOG accumulation list — see §6 for the per-frame *checkpoint* into it),
`opcode_handlers`, `lp64_stack`, `zk3_state`, account-witness/precompile/modexp/
sha256 scratch, and the whole BlockVerdict verdict-spine data.

> **Implementation note.** The shared fields move to a separate `shared_env`
> block addressed by a dedicated register (**x22 = shared_env base**); the
> shared-field handlers (ORIGIN/GASPRICE/COINBASE/…/BLOBBASEFEE/BLOCKHASH/SLOTNUM)
> read it instead of the per-frame env.
>
> This is **proof-cheap**, not proof-blocked. The env handlers are the verified
> `evm_env_load .x20 .x15 .<field>` Program, but `evm_env_load_spec_within`
> (`EvmAsm/Evm64/Env/Spec.lean:115`) is *parametric* over both `envBaseReg` and
> `field` — it's a layout/framing triple ("load the 4 limbs of `field.value env`
> from `envAddr + field.offset + 8*i`"), with no arithmetic tied to a specific
> register or offset. So the split needs only: (a) pass `.x22` as the base for
> shared-field handlers (the generic lemma already covers any base register), and
> (b) give the shared fields their `shared_env`-relative offsets via the
> `SimpleEnvField.offset` map (`EvmAsm/Evm64/Env/Field.lean:72`) — the same
> generic lemma applies at the new offsets unchanged. No new proof obligations.
>
> (Alternative considered: keep one full contiguous env per frame and *replicate*
> the shared fields, copying them parent→child on descent — also proof-trivial,
> ~0.4 MiB + a small per-descent memcpy. The `x22` split is preferred as the
> single-source-of-truth for block/tx-global env; replication is the fallback if
> reserving x22 proves inconvenient.)

---

## 4. Frame slot structure and `FRAME_STRIDE`

Each depth slot is a contiguous, 32-aligned block:

```
frame[d] for d>=1 (at call_frame_arena + (d-1)*FRAME_STRIDE); frame[0] = the
existing dispatcher evm_memory/stack/env (see §1, NOT in this arena):
  +0x00000  frame_stack_glo:  .zero 512        (guard)
  +0x00200  frame_stack_low:  .zero 0x8000    (32 KiB operand stack)
  +0x08200  frame_stack_top:                   (x12 init = here, grows ↓)
  +0x08200  frame_stack_ghi:  .zero 512        (guard)
  +0x08400  frame_returndata: .zero 0x10000   (64 KiB last-subcall returndata)
  +0x18400  frame_env:        .zero 0x300     (768 B per-frame env, §3)     x20
  +0x18700  frame_pc:         .zero 8          (saved PC / x10 on descent)
  +0x18708  frame_codebase:   .zero 8          (saved x21 = witness.codes slice)
  +0x18710  frame_meta:       .zero 0xF0       (caller depth, ret-offset/len in
                                                parent mem, is_static, is_create,
                                                created-address, state checkpoint id)
  ── round up to FRAME_STRIDE = 0x19000 (100 KiB, 32-aligned) ──
```

`FRAME_STRIDE = 0x19000` (100 KiB). Nested-frame memory is in the shared 96 MiB
pool; the slot contains the stack/guards, returndata, env, saved registers, and
metadata, rounded to the stride.

Total frame array = `1025 * 0x19000` = `104,960,000 B` ≈ **100.1 MiB** (depths
0..1024 inclusive — see §1).

> **Returndata sizing.** Returndata is per-frame (RETURNDATASIZE/COPY read the
> *last* sub-call's output of *this* frame) and a sub-call's RETURN/REVERT output
> is bounded by its memory, so 64 KiB is the safe max. A `frame_returndata`
> buffer is needed because the child slot `frame[d+1]` is reused by the parent's
> next CALL, so the output must be copied into the parent's frame on return.
> (Optimization deferred: returndata is usually small; a shared spill or a
> tapered buffer could cut the 64 MiB this costs — see §8.)

---

## 5. Memory-map placement — five-child union plus standalone memory pool

> **CURRENT (2026-08-02).** The Amsterdam 200M target uses
> `bsrMaxBalItems = 100000`. The current emitted `call_frame_arena` is
> coalesced with the five Phase-H children listed in `RegionMap.lean`; its
> `104,960,000 B` frame extent is followed by the standalone 96 MiB
> `evm_memory_pool`. `bv_system_storage_log` is outside that union because
> post-dispatch validators read it after frame zeroing. Fit and absolute
> placement are checked by `frameArray_unions_basr_baap`,
> `RegionMap.callFrameArena_within_data`, and `scripts/check-region-map.sh`.

> The old 1G/228 MiB/244 MiB layout is retained below only as historical
> rationale; it is not a description of the current guest.

> **CORRECTION (empirically validated 2026-06-08).** An earlier draft of this
> section assumed `.data` is ~16 MiB and the `0xa4000000..0xbf980000` window is
> free, "proving" a 164 MiB arena fits. **That is wrong.** ziskemu's RAM region
> is only **512 MiB** (`0xa0000000..0xc0000000`; CODEGEN.md:149,
> `docs/agents/eest-static-layout.md`). The current guest `.data` already spans
> **~427 MiB** (`0xa3000000..0xbdb2e067`), of which **~385 MiB** is BAL-replay
> scratch sized for the 500k-item / 1G-gas worst case:
>
> | arena | size | role |
> |---|---|---|
> | `basr_values`, `basr_accounts` | 122 MiB each | block_state_root replay |
> | `baap_storage_paths`/`_delete_paths`/`_values` | 32 MiB each | BAL-apply storage |
> | `bsr_changes`, `baap_storage_desc` | 20 MiB each | state-change / desc |
> | `basr_records` | 12 MiB | pre-account record table |
>
> Only **~36 MiB** is free below `0xc0000000`. A standalone 164 MiB arena placed
> at `0xa4000000` **overlaps `.data`** — the linker rejects it (confirmed). The
> CallFrameLayout `frameArray_fits` theorem is arithmetically true but its
> premise (`0xa4000000` is unoccupied) is false.

**Approach: overlay the frame arena on the execution-dead BAL-replay arenas
(union region).** A soundness-gate grep (2026-06-08) over *every* reference to
the BAL arenas pins down exactly which are dead during execution — and one is
NOT, so the naive "all `basr_*`/`baap_*` are dead" claim is wrong:

- **`basr_values` + `basr_accounts`** (122 MiB each, declared **contiguously** at
  `BlockVerdictDataSection.lean:539–540`) are referenced **only inside
  `block_state_root`** (`BlockVerdict.lean` ≤ line 302). `block_state_root` runs
  at `:348`, producing the post-state root compared to the header **before** any
  tx executes, and nothing past line 302 reads them. ⇒ **244 MiB of contiguous,
  execution-dead space** — the overlay target (≥ the 164 MiB needed).
- **`basr_records`** (12 MiB, `:537`) is **LIVE during execution** — read at
  `BlockVerdict.lean:528/577/620` (per-tx gas precharge + recipient/fee balance
  verify). It must **NOT** be overlaid (doing so corrupts the gas/balance check →
  false verdict). It sits *just before* `basr_values`, so aliasing the frame
  arena at the `basr_values` base excludes it automatically.
- The `*_fail_code` / `bsr_*_count` diagnostic **cells** (e.g. `baap_fail_code`,
  `bsr_fail_code`) are read post-replay (`:1020+`, copied to OUTPUT) but are tiny
  status words, not arenas — untouched by the overlay.

So the frame arena **aliases `basr_values`** and spans 244 MiB
(`basr_values`+`basr_accounts`), reusing that execution-dead region. (`baap_*`
are also block_state_root-only, but the contiguous `basr_values`+`basr_accounts`
pair alone exceeds the 164 MiB need, so the overlay needs only those two.)

This is a **union region**, not a linker overlay (GNU ld rejects overlapping
sections): one physical region, used as `basr_values`+`basr_accounts` during
`block_state_root` and as `call_frame_arena` during execution. Concretely, define
the frame arena to *alias* the `basr_values` base (same base symbol / a
`union`-style section) spanning the contiguous `basr_values`+`basr_accounts`
244 MiB. The frame arena needs 164 MiB ≤ 244 MiB and is the existing footprint —
**zero net RAM growth**.

```
0xa0000000  RAM start (ziskemu window 0xa0000000..0xc0000000 = 512 MiB)
0xa3000000  .data start
            ├─ initialized data + verdict spine + shared_env
            ├─ basr_records (12 MiB) — LIVE during exec (gas/bal verify); NOT overlaid
            ├─ ┌──────────────────────────────────────────────────────┐
            │  │ UNION REGION = basr_values+basr_accounts (244 MiB)     │
            │  │  phase 1 (≤ BlockVerdict:302): BAL-replay encoded accts │
            │  │  phase 2 (execution, :626+):   call_frame_arena (164MiB)│
            │  └──────────────────────────────────────────────────────┘
0xbdb2e067  .data end (unchanged)
0xbf980000  .sszscratch (NOBITS)
0xc0000000  RAM end
```

**SOUNDNESS GATE — verified for `basr_values`/`basr_accounts` (2026-06-08).** A
grep over every reference to these two symbols finds readers only inside
`block_state_root` (`BlockVerdict.lean` ≤ 302) and the data declaration; **no
post-replay reader** (verdict body, runtime-dispatch handlers, gas/arena helpers,
`.6.4.3.x` contract-dispatch path). The gate **fails** for `basr_records` (read at
`:528/577/620`), which is therefore excluded. Any future code that adds a
post-`block_state_root` read of `basr_values`/`basr_accounts` **breaks this union
and must be caught** — keep the gate grep in the implementation PR's checks.

> Consequence for `CallFrameLayout.lean`: `frameArrayBase` is **not** `0xa4000000`
> — it is the base of the BAL-replay union region (inside the existing `.data`).
> `frameArray_fits` should be restated against the union-region size, not a
> phantom free gap. `FRAME_STRIDE`, the sub-offsets, and `frameSlotCount` are
> unaffected.

---

## 6. Register conventions and frame transitions

Per-frame registers: for `depth == 0` they keep today's values (`evm_memory`,
`evm_stack_top`, `evm_env` — unchanged); for `depth ≥ 1` they are recomputed as
`call_frame_arena + (depth-1)*FRAME_STRIDE + sub`:

| Reg | Meaning | Per-frame? |
|---|---|---|
| x10 | PC (offset into code) | yes (saved to `frame_pc` on descent) |
| x12 | operand stack ptr (grows ↓) | yes (= `frame[d]+frame_stack_top`) |
| x13 | memBaseReg (EVM memory base) | yes (= `frame[d]+frame_mem`) |
| x20 | per-frame env base (per-frame fields only) | yes (= `frame[d]+frame_env`) |
| x21 | code base (→ witness.codes slice) | yes (saved to `frame_codebase`) |
| x22 | **shared_env base** (block/tx-global env; proof-cheap, see §3 note) | no (constant) |
| x2  | lp64 helper sp | no (shared; helpers run within one frame at a time) |
| x?? | **depth counter** (proposal: a fixed `.data` cell `evm_call_depth`) | global |

Transitions (depth d → d+1 on call, d+1 → d on return):

- **CALL / CALLCODE / DELEGATECALL / STATICCALL**:
  1. depth-limit check: `if depth + 1 > 1024` (i.e. `depth == 1024`) **or**
     balance < value `→ push 0 (fail)`, refund the reserved gas, continue in the
     parent (no child frame allocated). The deepest child that *executes* is
     depth 1024 (call from depth 1023). (`vm/instructions/system.py:116`.)
  2. gas: forward `min(requested, max_message_call_gas(gas_left − memory_cost −
     extra_gas))` (EIP-150 all-but-1/64, `vm/gas.py:419,424`) into
     `frame[d+1].frame_env+568`; **for value-bearing CALL/CALLCODE add the
     `CALL_STIPEND = 2300`** to the callee's gas (`vm/gas.py:64,415` — stipend is
     0 when value == 0).
  3. set child env: ADDRESS/CALLER/CALLVALUE per call type (DELEGATECALL keeps
     parent ADDRESS+CALLER+CALLVALUE; CALLCODE keeps ADDRESS; STATICCALL sets
     is_static + value 0).
  4. calldata view: `frame[d+1].calldata ptr/len = (frame[d].frame_mem + argsOff,
     argsLen)` — **aliased, no copy** (parent frame persists during child).
  5. code base: `x21 = witness.codes slice for callee` via
     `code_at_header_state_root`-style lookup; `x10 = 0`.
  6. `frame_meta`: record return-offset/len (into parent mem), is_static,
     caller depth, and a **state checkpoint id** (see revert below).
  7. recompute x12/x13/x20 from `d+1`; `depth++`; jump to interpreter.
- **CREATE / CREATE2**: like CALL but child code = init code from parent memory
  (≤ `MAX_INIT_CODE_SIZE`=0x20000 — note this fits one 128 KiB `frame_mem`;
  init code is read from the *parent's* memory slice as calldata-style, executed
  with `x21`→ a staged init-code buffer; the deployed code is the init code's
  RETURN output, validated ≤ `MAX_CODE_SIZE`). Computed address via
  `address_compute_create`/`create2`.
- **RETURN / STOP**: copy output (mem slice) → `frame[d-1].frame_returndata`;
  write success(1) + return-data to parent stack/mem per the recorded
  `frame_meta` ret-offset/len; **commit** child state to parent (no rollback);
  `depth--`; restore x10/x12/x13/x20/x21 from `frame[d-1]`.
- **REVERT / exceptional halt (OOG, invalid op, stack over/underflow)**:
  push 0 (fail) to parent; for REVERT copy revert-data → parent returndata;
  for exceptional halt returndata is empty and all child gas is consumed;
  **roll back** child state to the checkpoint; `depth--`; restore parent regs.

---

## 7. State revert/merge (soundness-critical)

Nesting requires that a child REVERT/halt undoes the child's state and log
effects but a child RETURN keeps them. Two checkpoint stacks, indexed by depth:

- **Log checkpoint**: `frame_env+448..480` already reserves per-frame log-state
  cells. On descent, record the current `evm_event_logs` write cursor; on child
  revert/halt, truncate the global log list back to that cursor; on child
  return, keep.
- **State-tracker checkpoint**: the runtime STATE_TRACKER persistent log
  (original=current=value entries, from the M22 storage preload machinery) needs
  a per-depth checkpoint id stored in `frame_meta`. On descent, snapshot the
  tracker length / a journal mark; on revert/halt, roll the journal back to the
  mark (restoring touched slots/balances/nonces and discarding child
  selfdestructs/creations); on return, keep. **This is the part that most needs
  c1 coordination** — it intersects the BAL-replay/state-tracker representation.

The post-tx BAL/post-state recompute (block_verdict) then sees the
merged-or-reverted state exactly as `run_stateless_guest` would.

---

## 8. Edge cases and deferred optimizations

- **Depth limit**: a call from depth 1023 *succeeds* (child at depth 1024
  executes); a call from depth 1024 *fails* (push 0, no `frame[1025]` allocated).
  The array needs indices **0..1024** (1025 slots); `frame_array_end` is never
  addressed. (Off-by-one trap: the limit is on the child depth, depth is 0-based
  — `depth + 1 > 1024`, not `depth >= 1024`.)
- **63/64 gas taper** (optimization, not v1): a frame at depth d has ≤
  `G·(63/64)^d` gas, so frames past ~depth 490 cannot expand memory to 128 KiB
  (a 128 KiB expansion costs ~34k gas). A *tapered* stride (large mem arenas for
  shallow frames, small for deep) could cut the 164 MiB substantially. Deferred:
  v1 uses uniform stride for simplicity/correctness; revisit if the map tightens.
- **Returndata 64 MiB** (see §4): could be a shared spill buffer or tapered.
- **`.zero` materialization / ELF size**: the current guest emits `.zero`
  buffers into `.data`, which the linker materializes as zero-filled bytes in
  the ELF (the single-frame guest ELF is already ~448 MiB). A 164 MiB frame
  array of `.zero` would balloon the ELF and ziskemu load. The implementation
  should emit the frame array (and other large zero arenas) into a **`.bss`/
  `NOBITS` section** (zero-initialized, not stored in the file) — placed in the
  same `0xa4000000..` address window — so the on-disk ELF does not grow. This is
  an emit-time concern, not an address-map concern; the map in §5 is unchanged.
- **calldata aliasing**: safe because the parent frame slot is never reused
  while a child is live (strictly deeper index). RETURNDATACOPY reads the
  copied `frame_returndata`, not the freed child memory.
- **Three distinct address roles** (spec `generic_message`,
  `vm/instructions/system.py:316-355`): `caller` (CALLER, env+64),
  `current_target` (ADDRESS / storage owner / value sink, env+0), and
  `code_address` (where code is loaded — drives `x21` code base). They diverge
  per call type:
  - CALL/STATICCALL: caller=parent.current_target, current_target=to, code=to.
  - CALLCODE: `current_target = parent.current_target` (storage = caller's!),
    code = code_address (`system.py:536`).
  - DELEGATECALL: caller=parent.caller, current_target=parent.current_target,
    value=parent.callvalue, code = code_address.
  - CREATE/CREATE2: current_target = computed new address, code = init code.
  `frame_meta` + the per-frame env (ADDRESS/CALLER/CALLVALUE) + `x21` capture all
  three; storage ops (SLOAD/SSTORE) and SELFBALANCE use `current_target`.
- **STATICCALL**: `is_static` in `frame_meta`; SSTORE/LOG/CREATE/SELFDESTRUCT/
  CALL-with-value inside a static frame are exceptional halts.

---

## 9. Decomposition into implementation children (proposed)

Build bottom-up against this fixed map (each ≈ 1 PR):

1. **layout constants + `.data` emit**: add `FRAME_STRIDE`, `frame_array_base`,
   the per-frame sub-offsets, `evm_call_depth` cell, `shared_env` block (x22);
   split today's `evm_env` into per-frame + shared; re-point the
   ORIGIN/GASPRICE/block-env/BLOBBASEFEE/BLOCKHASH/SLOTNUM handlers to x22.
   (Pure layout; the single-frame guest must still pass — depth 0 == today.)
2. **frame address helper**: `frame_base(depth) → ptr` + register-recompute
   macro (x12/x13/x20 from depth); unit-probe it.
3. **descent/return register save+restore** + `evm_call_depth` push/pop, no
   semantics yet (depth-0 unchanged).
4. **CALL/STATICCALL** child env setup + calldata aliasing + 63/64 gas + returndata
   copy + success/fail push (value-transfer + recipient code via witness).
5. **DELEGATECALL/CALLCODE** storage-context + value/caller rules.
6. **CREATE/CREATE2** init-code staging + address compute + deployed-code cap.
7. **revert/merge**: log + state-tracker per-depth checkpoint + rollback.
8. **depth-1024 limit** + static-context exceptional halts.

Each references this doc for offsets/registers. (1) and (7) need c1 coordination
(c1's in-flight call-frame PRs and the state-tracker representation).

---

## Coordination note

c1 began call-frame work; operator reassigned the *full 1024-deep frame stack +
memory layout* to c2 (this doc). Confirm with c1's in-flight PRs that the
per-frame ABI (entry/exit, gas forwarding, returndata) and the state-tracker
journal shape match §6/§7 before building (1)/(7). Keep unique `.data` label
prefixes (`frame_*`, `shared_env_*`) and union-resolve any layout-PR conflicts.
