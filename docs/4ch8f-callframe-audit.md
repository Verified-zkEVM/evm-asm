# The call-frame-arena ownership audit (bead `evm-asm-4ch8f.6`, soundness half)

*Session 2026-07-05. This is the "Own-not-Is" Phase-D audit plus the
phase-sequencing audit that the phase-ownership model (PR #9724:
`Rv64/SAsm/PhaseSplit.lean`, `Codegen/CallFramePhase.lean`,
`Codegen/CallFrameWindows.lean`) deferred. The model havocs the arena on
every H↔D view switch, so its soundness rests on two auditable claims:
(1) no Phase-D routine reads an arena cell it has not written since the
last transition, and (2) the phase segments really are sequential over
each arena's bytes. Both claims were checked against the emitted guest.
Every finding below was independently re-verified at the cited lines
before filing.*

## Verdict summary

| Claim | Verdict |
|---|---|
| Frame EVM memory read-before-write | **SAFE** — `call_frame_enter` zeroes the full memory window on *every* descend (`CallFrameDescend.lean:50-57`); depth 0 uses the standalone global `evm_memory` (loader-zeroed, not in the union). |
| Frame operand stack | **SAFE** — push-before-pop, sp starts at stack-top, under/overflow guards repointed per frame (`CallFrameDescend.lean:500-505`, `CallFrameReturn.lean:250-266`). Stale bytes below sp never read as entries. |
| Frame returndata / pc / codebase / meta sub-regions | **SAFE (vestigial)** — the runtime keeps this state in standalone `.data` (`frame_save_area`, `frame_call_ctx`, `frame_parent_bases`, `Dispatch.lean:3022-3033`; returndata in the global `evm_precompile_frame`). The arena sub-regions are never addressed, so their garbage is never read. |
| Frame env block | **ONE BUG** — the descend write-set covers every handler read except `env+552/560` → **`.72`** below. |
| `basr_values`, `basr_accounts`, `baap_storage_{desc,paths,delete_paths,values}` | **SAFE** — written *and* read entirely inside the single-shot, pre-dispatch `block_state_root` (`BlockVerdictFunction.lean:241`), which invokes no dispatcher internally (verified by grep over all its callees). Earlier derive-phase dispatcher scribbles are rewritten before any read. |
| `bv_system_storage_log` | **UNSAFE** → **`.73`** below. |
| REVERT / mid-block Phase-H re-entry | **NONE** — `block_state_root` is called exactly once; REVERT only truncates the `0xa0630000` exec log (`BlockVerdictFunction.lean:902-923`). No phase token needed for the six safe children. |
| Layout constants vs emitted geometry | **DIVERGED** → **`.71`** (and `.74`) below. |

## The true phase timeline (not "H once, then D once")

```
stateless_verdict_v2:
  payload/witness/headers extraction
  H₁: system-call derives (EIP-7002/7251)
      — each contains a Phase-D INTERLUDE (runtime_dispatcher_call)
      — capture_system_storage_exec_rows WRITES bv_system_storage_log
        (BlockVerdictStateRoot.lean:505-508, 550-553)
  block_verdict:
    H₂: block_state_root (single-shot; basr_*/baap_* written+read inside;
        no internal dispatcher)                (BlockVerdictFunction.lean:241)
    D:  per-tx dispatch (EOA :617 / dispatch_tx_runtime_code :883)
        — frames at call_frame_arena + (d-1)*stride, each descend
          ZEROES 0x20000 of the slot
    H₃: post-dispatch validators READ bv_system_storage_log
        (bal_storage_matches_exec_log :972, bal_storage_covers_exec_log
         :984, account_tuple_sequences_consistent :1135;
         scans at BalStorageMatchesExecLog.lean:90-92 etc.)
```

The `H₁ → H₂ → D → H₃` interleave is what makes the syslog unsafe: its
writes (H₁) and reads (H₃) straddle the per-tx dispatch, whose frames
physically cover the syslog extent from call depth ≈ 220 up.

## Filed bugs

### `.71` (P0) — `CallFrameLayout` constants are stale vs the emitted geometry

The verified model says stride `0x29000`, memory `0x10000`, env
`+0x28400`. The emitted runtime uses stride **`0x39000`**
(`CallFrameBase.lean:36`, `LUI x6, 57`), memory **`0x20000`**
(`Dispatch.runtimeMemoryBytes`, zero-loop `CallFrameDescend.lean:50-57`),
env **`+0x38400`**. The arena is *sized* by the stale constants
(`frameArrayBytes = 1025 × 0x29000`), so frames at depth ≥ ~704–738
overrun `call_frame_arena_end` into the following `.data`
(`rb_running_block_bloom`, …). **Every kernel-checked union-fit and
phase theorem (`RegionMap.dataUnionChildren_fit_arena`,
`frameArray_unions_*`, `CallFramePhase.phaseD_eq_phaseH`, the
`CallFrameWindows` tilings) models a stride the code does not use.**
The phase model is structurally right but must be re-pinned to the
corrected constants once `.71` is fixed.

### `.72` (P0) — nested BLOCKHASH reads uninitialized child `env+552/560`

`h_BLOCKHASH` reads `env+552` (current block number) and `env+560` (hash
count) (`EvmBlockHashHandlers.lean:27-50`). Only the frame-0 env gets
them (`Dispatch.lean:2377/2383`); `call_frame_descend` copies env
`128..415` and `512..551` — the adjacent comment documents fixing the
*same* garbage bug for BLOBHASH at `env+544` — but never `552/560`. In
child frames over the union front the cells hold Phase-H garbage; if the
two range guards pass, `index = count − age` is unbounded and
`evm_block_hashes + index*32` is an out-of-bounds read whose bytes are
pushed as the BLOCKHASH result. This is precisely the read-before-write
class the havoc model makes unprovable — found by trying to justify the
D view opening as `Own`.

### `.73` (P0) — `bv_system_storage_log` read post-dispatch, clobbered by deep frames

Written in H₁, read in H₃ (see timeline), while D's frames at depth
≥ ~220 (emitted stride; ~307 under the model stride) zero/overwrite its
extent `[2S, 2S+L)` ≈ `[48.8 MiB, 122.1 MiB)` of the arena. The
union-safety comment (`BlockVerdictDataSection.lean:576-582`, "consumed
entirely within the block_state_root recompute … dead during Phase-D
dispatch") is **false**. Concrete scenario: any block where the
7002/7251 predeploys performed SSTOREs plus a contract tx recursing
≥ ~220 calls deep → the storage-exactness/tuple validators compare
against corrupted rows. Robust to how `.71` resolves the stride.

### `.74` (P1) — `emitExceptionalExit` uses the stale constants live

`Dispatch.lean:1238-1249` rebuilds the frame env base with the Lean
constants (`0x29000`/`0x28400`) while the frames actually sit on
`0x39000`/`0x38400` — the `sd x0, 568(x20)` gas-zeroing store hits the
wrong cell at every depth (a stray write into the operand-stack window;
the intended `gasRemaining` is never zeroed). Falls out of `.71`'s
constant reconciliation.

## What the phase model needs once `.71`–`.74` land

1. Re-pin `CallFrameLayout` constants to the emitted geometry (or drive
   the emit from the constants) and re-run the fit proofs + the
   `check-region-map.sh` ELF drift guard (the arena grows ~64 MiB;
   re-verify `.data` end vs `.sszscratch` at `0xbf500000`).
2. Un-union `bv_system_storage_log` (or move the three validator reads
   before per-tx dispatch); then the H-view tiling drops to six children
   + pad and `phaseHSegs` shrinks accordingly.
3. After `.72`'s descend fix, the env write-set covers all handler
   reads, and the D-side `Own`-opening obligation is dischargeable for
   the env window; memory/stack/vestigial windows already are.
4. The `H₁ D-interlude` (derive dispatchers running before `block_state_root`)
   is safe today only because `block_state_root` rewrites basr/baap
   after it; any future Phase-H reader of derive-phase artifacts other
   than the syslog must re-run this audit. Checklist trigger: adding a
   `dataUnionChildren` entry or any post-dispatch reader of a union
   child ⇒ re-run both audits.

## Residual UNKNOWNs (explicitly not closed)

- Frame-0 env pre-tx completeness beyond the enumerated handler
  read-set.
- `evm_precompile_frame.size` is not reset on descend: a fresh child's
  RETURNDATASIZE sees the parent's last sub-call length instead of 0 —
  global staleness (not arena garbage), flagged for the `.56` frame
  beads.
- `create_frame_flag[d]` clearing across all halt exits on
  CALL-after-CREATE slot re-use.
- The EIP-7251 derive's dispatcher could in principle clobber the
  EIP-7002 syslog rows if that predeploy recursed ≥ ~220 deep (honest
  predeploys are shallow; unmodeled).
