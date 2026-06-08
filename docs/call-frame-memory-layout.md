# Nested CALL/CREATE frame memory layout (depth-indexed pre-allocated frame array)

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
  - `.sszscratch`@ `0xbf500000`
  - ⇒ usable `.data` span before `.sszscratch` = `0xbf500000 − 0xa3000000`
    = `0x1c500000` = `475,004,928` B = **453 MiB** (≈ 475 MB decimal).
- Amsterdam caps: `MAX_CODE_SIZE = 0x10000` (64 KiB), `MAX_INIT_CODE_SIZE =
  0x20000` (128 KiB).
- This project **avoids misaligned load/store** — every per-frame sub-region is
  aligned, and `FRAME_STRIDE` is a multiple of 32.

Design principle: **uniform-stride pre-allocated array, simple and correct
first.** Frame `d` lives at `frame_array_base + d * FRAME_STRIDE`. A CALL
descends by bumping a depth counter and recomputing the per-frame register
bases by `base + depth*FRAME_STRIDE`. No copying of code (referenced via the
witness) and no copying of calldata (aliased into the parent's memory).

---

## 2. Current single-frame layout (ground truth)

From `EvmAsm/Codegen/Dispatch.lean:1525-1600` (`emitDispatcherDataSection`) and
the register conventions in `EvmTinyInterp.lean`:

| Region | Size | Reg | Notes |
|---|---|---|---|
| `evm_code` | bytecode | x10 (PC) base | baked bytecode; will become x21→witness.codes slice |
| `evm_memory` | `0x10000` (64 KiB) | x13 (memBaseReg), grows ↑ | EVM memory |
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

> **Implementation note:** keep the *intra-frame* env field offsets identical to
> today (0,32,64,96,416,424,496,568, log 448-480). Handlers that do
> `ld …, N(x20)` keep working once `x20` points at the *per-frame* env subblock.
> The shared fields move to a separate `shared_env` block addressed by a new
> dedicated register (proposal: **x22 = shared_env base**), and the handlers for
> ORIGIN/GASPRICE/COINBASE/…/BLOBBASEFEE/BLOCKHASH/SLOTNUM switch from `N(x20)`
> to `M(x22)`. This is the one mechanical handler edit the split forces.

---

## 4. Frame slot structure and `FRAME_STRIDE`

Each depth slot is a contiguous, 32-aligned block:

```
frame[d] (at frame_array_base + d*FRAME_STRIDE):
  +0x00000  frame_mem:        .zero 0x10000   (64 KiB EVM memory)          x13
  +0x10000  frame_stack_glo:  .zero 512        (guard)
  +0x10200  frame_stack_low:  .zero 0x8000    (32 KiB operand stack)
  +0x18200  frame_stack_top:                   (x12 init = here, grows ↓)
  +0x18200  frame_stack_ghi:  .zero 512        (guard)
  +0x18400  frame_returndata: .zero 0x10000   (64 KiB last-subcall returndata) 
  +0x28400  frame_env:        .zero 0x300     (768 B per-frame env, §3)     x20
  +0x28700  frame_pc:         .zero 8          (saved PC / x10 on descent)
  +0x28708  frame_codebase:   .zero 8          (saved x21 = witness.codes slice)
  +0x28710  frame_meta:       .zero 0xF0       (caller depth, ret-offset/len in
                                                parent mem, is_static, is_create,
                                                created-address, state checkpoint id)
  ── round up to FRAME_STRIDE = 0x29000 (164 KiB, 32-aligned) ──
```

`FRAME_STRIDE = 0x29000` (164 KiB). Components: 64 KiB mem + 33 KiB stack(+guards)
+ 64 KiB returndata + 768 B env + meta, rounded.

Total frame array = `1025 * 0x29000` = `0xA429000` ≈ **164.2 MiB** (depths
0..1024 inclusive — see §1).

> **Returndata sizing.** Returndata is per-frame (RETURNDATASIZE/COPY read the
> *last* sub-call's output of *this* frame) and a sub-call's RETURN/REVERT output
> is bounded by its memory, so 64 KiB is the safe max. A `frame_returndata`
> buffer is needed because the child slot `frame[d+1]` is reused by the parent's
> next CALL, so the output must be copied into the parent's frame on return.
> (Optimization deferred: returndata is usually small; a shared spill or a
> tapered buffer could cut the 64 MiB this costs — see §8.)

---

## 5. Memory-map placement (fits-in-map proof)

```
0xa3000000  .data start
            ├─ shared region: evm_code(removed; code via witness), shared_env,
            │  blob/block hashes, event logs, helper scratch, lp64_stack(256K),
            │  opcode_handlers, zk3_state, account-witness, AND the full
            │  BlockVerdict verdict-spine data section.  Reserve 0x1000000 (16 MiB).
0xa4000000  frame_array_base (16 MiB after .data start, 32-aligned)
            ├─ 1025 × 0x29000 = 0xA429000 (164.2 MiB)
0xae429000  frame_array_end
            … 0xae429000 .. 0xbf500000 = 0x110d7000 (272 MiB) headroom …
0xbf500000  .sszscratch
```

164 MiB frames + 16 MiB shared = 180 MiB, well under the 453 MiB budget with
**272 MiB headroom** (`frame_array_end 0xae429000 → 0xbf500000` = `0x110d7000` =
285,741,056 B). The array fits with comfortable margin even if `FRAME_STRIDE` or
the shared reserve grows.

> Place `frame_array_base` via a dedicated `.balign 32` label at the very end of
> the guest `.data` so the 16 MiB shared reserve is "whatever the shared data
> actually consumes" rather than a hard 16 MiB — the 16 MiB is just the
> conservative ceiling for the proof.

---

## 6. Register conventions and frame transitions

Per-frame registers recomputed as `frame_array_base + depth*FRAME_STRIDE + sub`:

| Reg | Meaning | Per-frame? |
|---|---|---|
| x10 | PC (offset into code) | yes (saved to `frame_pc` on descent) |
| x12 | operand stack ptr (grows ↓) | yes (= `frame[d]+frame_stack_top`) |
| x13 | memBaseReg (EVM memory base) | yes (= `frame[d]+frame_mem`) |
| x20 | per-frame env base | yes (= `frame[d]+frame_env`) |
| x21 | code base (→ witness.codes slice) | yes (saved to `frame_codebase`) |
| x22 | **shared_env base** (new) | no (constant) |
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
  (≤ `MAX_INIT_CODE_SIZE`=0x20000 — note this exceeds one 64 KiB `frame_mem`;
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
  `G·(63/64)^d` gas, so frames past ~depth 490 cannot expand memory to 64 KiB
  (a 64 KiB expansion costs ~14k gas). A *tapered* stride (large mem arenas for
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
