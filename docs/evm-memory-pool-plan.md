# Shared stack-pool for nested-frame EVM memory — implementation handoff (evm-asm-274cr)

*Closes the beyond-dense memory-window false-reject class STRUCTURALLY by
making per-frame EVM memory flat again: replace the 1025 fixed 128 KiB
per-slot memory reservations with ONE shared LIFO buffer. Byte-tied +
proof-bearing; a wrong offset ALIASES FRAMES (false-accept hazard), so follow
the exact change-map. This doc is a complete handoff — another agent can
finish from here.*

Branch: `fix/evm-memory-pool` (off `main`). Independent of `m8pdu` #10242 (it
retires that sparse path). Bead: `evm-asm-274cr`. Spec pin: `40f956fab`.

---
## 0. Design recap (why it works, in one paragraph)

Each frame's EVM memory is a flat dense region taken from one shared pool used
as a LIFO stack: `child_membase = parent_membase + ceil32(parent_MSIZE)`
(dword-aligned automatically because MSIZE is a 32-byte multiple). A returned
frame's region (above the current frame) is reused on resume — pure stack
discipline, NO allocator. Depth 0 keeps its own `evm_memory` (4 MiB) region;
depths ≥1 take from the pool (depth-1 child at pool offset 0). We track TWO
numbers per depth: the memory base (stamped at descend into
`frame_parent_bases[d]`) and MSIZE (each frame's `env+488`). All live frames
share one tx's `TX_MAX_GAS_LIMIT = 2^24` regular gas ⇒ max total-live nested
memory ≈ 70 MiB < the 96 MiB pool, so a valid block NEVER overflows; a block
that would has spent >2^24 regular gas ⇒ invalid ⇒ pool OOG is correct. See
`docs/memory-arena-gas-bound.md` for the gas invariant. Net footprint: reclaim
128 MiB (per-slot memory) − 96 MiB (pool) = **−33 MiB**.

---
## 1. STATUS — done so far

- **Commit `e744c5e71`** (step 1): `CallFrameLayout.lean` — `frameMemBytes
  0x20000→0` (memory decoupled), `frameStride 0x39000→0x19000`, added
  `evmMemoryPoolBytes = 0x6000000` (96 MiB); `#guard`s re-pinned
  (`frameStackTopOff 0x8200`, `frameEnvOff 0x18400`, `frameStride 0x19000`,
  `frameMemBytes 0`, `evmMemoryPoolBytes ≥ 0x4800000`). **`CallFrameWindows`
  (frame-window separation logic) + `RegionMap` re-closed MECHANICALLY** (zero
  proof edits) — verified by `lake build EvmAsm.Codegen.CallFrameWindows`.
- **Commit `19ec2a6cb`** (step 2): `CallFrameBase.lean` `frame_base` `LUI x6,
  57→25` (stride `0x19000`); `CallFrameBaseSAsm.lean` `frameBase_spec`
  RE-PROVED (3 constant edits: `LUI 25`, `hstride = 0x19000`, post
  `(depth-1)*0x19000`), classical-3, no sorry.

Both verified-proof surfaces now confirmed to re-close at the new geometry.
The guest DOES NOT LINK until the runtime asm below is done (frame_base emits
the new stride but `enter`/`return`/data-section still assume the old layout).

New slot sub-offsets (all derived; memory removed): `frameStackGuardLoOff=0`,
`frameStackTopOff=0x8200`, `frameEnvOff=0x18400`, `framePcOff=0x18700`,
`frameCodebaseOff=0x18708`, `frameMetaOff=0x18710`, `frameUsedBytes=0x18800`,
`frameStride=0x19000`, `frameIntraPadBytes=0x800`.

---
## 2. REMAINING WORK (ordered; register-level)

### Step 3 — `call_frame_enter` (`CallFrameDescend.lean`, `callFrameEnterFunction`)
Current body: computes `frame_base` → `s0` (slot base), zero-inits `0x20000`,
returns `a0=s0`(mem) / `a1=s0+0x28200`(stack top) / `a2=s0+0x38400`(env).
Change to:
- **Stack top literal `0x28200 → 0x8200`; env literal `0x38400 → 0x18400`.**
- **DELETE the `li t1, 0x20000` … `.Lcfe_zero` zero-loop** (memory is no longer
  in the slot and is zeroed lazily on expansion — step 6).
- **Memory base (a0) = the pool base**, NOT `s0`. Compute here (enter runs
  after `frame_depth_push`, so `evm_call_depth = d` = child depth, and the
  descend has ALREADY populated `frame_parent_bases[d]` = (parent_membase,
  parent_env) — verify ordering holds; it does in `call_frame_descend`, CHECK
  `create_frame_descend`):
  ```
  d = evm_call_depth
  if d == 1:  child_membase = evm_memory_pool            # base of the pool
  else:       la t, frame_parent_bases; idx = d*16
              parent_membase = ld 0(frame_parent_bases+idx)
              parent_env     = ld 8(frame_parent_bases+idx)
              parent_msize   = ld 488(parent_env)         # 32-multiple already
              child_membase  = parent_membase + parent_msize
  a0 = child_membase
  ```
  (Alternative if `frame_parent_bases[d]` is not yet set at enter: compute in
  the DESCEND instead, where `s2 = parent membase`, `s3 = parent env` are live
  — override `s10` after `jal call_frame_enter`. Pick whichever keeps
  `create_frame_descend` correct too.)
- Keep `s0` (slot base) for the stack/env returns; only the MEMORY return
  changes to the pool.
- Preserve the register save/restore (`ra`/`s0`); use scratch t-regs for the
  pool computation.

### Step 4 — `call_frame_descend` (`CallFrameDescend.lean`)
- After `jal call_frame_enter`, `s10 = child memory base` — now the pool base
  (from step 3). No other change unless you chose the "compute in descend"
  alternative. The calldata alias (`call_frame_set_calldata`, step 6 of
  descend) still reads the PARENT memory (`s2`) — unchanged and correct.
- **`create_frame_descend`** (CREATE child): ensure it ALSO populates
  `frame_parent_bases[d]` before `call_frame_enter` and gets the pool base the
  same way. VERIFY — CREATE initcode memory must come from the pool too.

### Step 5 — `frame_return` (`CallFrameReturn.lean`)
- Parent stack-top literal `0x28200 → 0x8200` (line ~289, `li t3, 0x28200`).
- Parent env literal `0x38400 → 0x18400` if present (grep the function).
- Parent memory-base restore `ld x13, 0(frame_parent_bases+idx)` — UNCHANGED
  (now points into the pool). Good.

### Step 6 — `EvmMemoryGas.lean`
- **`memoryArenaLimitAsm`**: depth ≥1 returns the FRAME-RELATIVE remaining pool
  `pool_end − x13` (x13 = current memory base) instead of the `0x20000`
  constant; depth 0 stays `rootRuntimeMemoryArenaLimitBytes` (`evm_memory`,
  4 MiB). `pool_end = evm_memory_pool + evmMemoryPoolBytes` (emit a label or
  `la` + addi). Every window op's bail becomes pool-relative automatically.
  NB: the limit is compared against the window END computed frame-relative
  (`offset+size`), so it must be `pool_end − x13` (frame-relative), not
  absolute.
- **`updateActiveMemorySizeAsm`**: on growth (`current < rounded`), after the
  gas charge, ZERO `[x13 + current, x13 + rounded)` (spec "expand with
  zeros"). Loop in 8-byte stores; x13 = memory base, current/rounded are the
  old/new MSIZE (both 32-multiples). This REPLACES the eager per-enter zero
  removed in step 3. Blast radius: every memory-touching opcode — the
  full-suite A/B is the gate. (Also apply to the const/sparse variants
  `updateActiveMemorySizeConstAsm` etc. if they have their own growth path.)

### Step 7 — data sections (`Dispatch.lean` / `BlockVerdictDataSection.lean`)
- `call_frame_arena: .zero <frameArrayBytes>` — now `1025 * 0x19000` (derived;
  grep for the guest arena `.zero`, NOT the `0x39000` standalone-probe one at
  Dispatch.lean:3642 unless that's the guest's). Shrinks ~228→100 MiB.
- Add `evm_memory_pool: .zero 0x6000000` + a following `.balign 8` and an
  `evm_memory_pool_end:` label (or compute end from base+size in asm). Place
  it in the region the reclaimed arena space frees (RegionMap step 8).
- `evm_memory` (depth-0, `runtimeMemoryBytes = 0x400000`) UNCHANGED.
- No per-tx reset of the pool needed (lazy zero-on-expansion + the bump base is
  re-derived per descend from MSIZE).

### Step 8 — `RegionMap.lean`
- `frameArrayBytes` auto-shrinks. Add an `evm_memory_pool` `GuestRegion`
  (96 MiB) placed after the shrunk frame arena; add its `fitsZone` /
  `allPairwiseDisjoint` membership + the `_matches_*` literal pin. Re-pin
  `dataSizeBytes` AFTER regen (check-region-map reports the ELF size).
- Re-check the union `decide` guards (arena front still ≥ basr pair: 100 MiB
  ≥ 49 MiB ✓).

### Step 9 — probes
- `SparseEpochProbe.lean` (`zisk_sparse_epoch_probe`) calls `call_frame_enter`
  directly and depends on the old behavior — it is part of the sparse machine
  being RETIRED. Either update it to the new enter contract or delete it with
  the sparse retirement. The `zisk_frame_return` / `zisk_frame_base` probes
  reference `0x28200`/`0x38400`/`0x39000` in their EXPECTED-output comments and
  setup — update to the new offsets (`0x8200`/`0x18400`/`0x19000`).

### Step 10 — regen + gates
`scripts/regen-cycle.sh`; then bump `RegionMap.textSizeBytes` and
`dataSizeBytes` to the reported ELF sizes (check-region-map prints the drift);
run `check-region-map`, `check-asm-to-program`, `check-drift`,
`check-forbidden-tactics`, `check-axioms` (classical-3). Byte-tie any
`asm_to_program`-converted progs touched.

---
## 3. VALIDATION

- **Witness** (new probe, or extend an existing frame probe): a depth-≥1 frame
  that MSTOREs at offset > 0x20000 (e.g. 0x30000) and up to a few hundred KiB,
  then MLOADs it back — must read the written bytes (pre-change: OOG-burn at
  the 128 KiB arena limit). Add a sibling/child check: a child frame that also
  uses memory does NOT corrupt the parent's (parent reads its bytes intact
  after the child returns). Assert the pool bump math via
  `frame_parent_bases`.
- **Full-suite A/B** (spike, ~25,693 fixtures; `setsid nohup … --all
  --jobs 12`, then Monitor for the summary): FAIL/ERROR must not rise vs
  the `27 FAIL / 6 ERROR` baseline; **label-level `comm`** of the FAIL sets =
  0 regressions. The dense path (MLOAD/MSTORE/CALL/RETURN/KECCAK/LOG/COPY) is
  the key surface.
- **Proofs**: `CallFrameWindows`, `frameBase_spec`, and any memory-opcode
  specs touched stay classical-3 (`#print axioms`), or are cleanly retired
  (maintainer-authorized). No `sorry`/`native_decide`/`bv_decide`/
  `maxHeartbeats`.

---
## 4. GOAL DIRECTIVE (drives to a review-ready PR)

Done when ALL hold: (1) guest builds+links within 512 MiB, RegionMap net
≈ −33 MiB, disjointness guards pass; (2) all `check-*.sh` clean, classical-3;
(3) full-suite A/B 0 regressions vs 27/6 baseline, label-level comm-verified,
dense path behavior-identical; (4) the >128 KiB nested-memory witness passes
(succeeds when affordable, correct bytes, no sibling aliasing); (5) touched
proofs classical-3 or cleanly retired; (6) ONE isolated PR on `main`, NO
`merge!` label, NO self-merge — close `evm-asm-274cr` when 1–5 hold.
Constraints: spec-faithful flat memory (zero-on-expansion = "expand with
zeros"; limit = pool_end−frame_base); `child = parent + ceil32(MSIZE)`; pool
> ~70 MiB joint bound; overflow = legit OOG; byte-tie + regen; sparse
retirement is a SEPARATE follow-up PR. STOP-and-report if a re-proof is
intractable (give the stuck goal), if A/B regresses on the dense path (name
the fixtures), or if the footprint/bound doesn't hold.

---
## 5. GOTCHAS (learned)

- **Change EVERY copy of a byte-tied constant.** `frameBase_spec` broke because
  the `LUI` immediate was changed but the `hstride` lemma still asserted
  `25<<12 = 0x39000`. `decide` "proved a false proposition" → fix ALL copies
  (the immediate, the intermediate lemma, the postcondition). Build the proof
  in isolation (`lake build …CallFrameBaseSAsm`) before moving on.
- **A wrong slot offset aliases frames = false-accept.** This is the one
  soundness hazard in this change; the `#guard`s (`frameStackTopOff`/
  `frameEnvOff`/`frameStride`) + `frameBase_spec` + full-suite A/B are the
  triple check. Never guess an offset; derive it.
- **`memoryArenaLimit` is frame-RELATIVE** (compared against `offset+size`), so
  the pool limit is `pool_end − x13`, not `pool_end`.
- **`updateActiveMemorySize` blast radius** is every memory opcode; zero-on-
  expansion must be exactly the growth delta `[old,new)` (both 32-multiples),
  and the full-suite A/B is the only real check that the dense path is
  unchanged.
- **`create_frame_descend`** is a second frame-entry path — do NOT forget the
  CREATE-child memory base + initcode staging must come from the pool too.
- **Regen**: `check-region-map` prints the exact `textSizeBytes`/`dataSizeBytes`
  drift; bump the pins to the reported ELF values, rebuild, re-check. Net
  `.data` should drop ~33 MiB.
- **Do NOT self-merge / add `merge!`.** Sparse retirement (dead m8pdu/#10234
  paths once `memoryArenaLimit` never trips) is a SEPARATE cleanup PR.
