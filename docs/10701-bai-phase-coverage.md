# BAL producer coverage by `block_access_index` phase (GH #10701)

**Measured 2026-07-29** against one guest ELF (sha `91353ef2f8ce`, `.text` `0x06730c`). Every cell below is a
counted trace observation, not a source reading — spike commit traces via `SPIKE_COMMITLOG`, counting entries
to the named producer. Numbers describe the state of the world at that date; trust the Lean sources and the
drift-guard scripts over any figure here.

EIP-7928 has three producer phases. `fork.py:917-919` sets `block_access_index = ulen(transactions) + 1` for
the post-execution operations; `process_withdrawals` (`:921`) incorporates at `:1226`, and every checked
system transaction (`:923`) at `:858-859`.

## The matrix

| phase | `storage_changes` | `balance_changes` | `nonce_changes` | `code_changes` |
|---|---|---|---|---|
| **BAI 0** — pre-block system | ✅ direct builder append | n/a | n/a | n/a |
| **BAI 1..N** — per transaction | ✅ | ✅ | ✅ | ✅ |
| **BAI N+1** — post-execution | ❌ **the only hole** | ✅ | ✅ | ✅ |

### How each cell was established

- **BAI 0 storage** — `append_modeled_system_storage_tuple_rows` runs once and records straight into the
  builder (the only two `bai=0` rows on 23725). It never passes through `storage_write_record`, so it is a
  distinct route from the per-tx path.
- **BAI 0 non-storage is `n/a`, not untested** — over a systematic every-20th sample of the 26,105 stateless
  inputs (1,305 decoded), account entries carrying a BAI-0 change number **2,606 for storage and 0 for
  balance, nonce and code**. The pre-block system calls touch storage only.
- **BAI 1..N** — all four emit. `bal_emit_storage_changes` is called from *inside*
  `write_sets_incorporate_tx` before the merge, mirroring `state_tracker.py:853`; balance/nonce/code go
  through `account_writes_emit_builder_tx`. Counted on 23725 (5 tx): `storage_write_record` 42 entries
  (2 hit + 40 append), `write_sets_incorporate_tx` 5, `bal_emit_storage_changes` 5. `bal_builder_append_code`
  fires (2 rows at `bai=1` on 11658/11659), so the code column is genuinely covered.
- **BAI N+1 non-storage** — the post-exec block after `.Lbv_mtx_done` sets the index to `bv_tx_count + 1` and
  calls `account_writes_emit_builder_tx` + `account_writes_incorporate_tx`. The zero-transaction path reaches
  the *other* call site of `block_verdict_withdrawal_nonstorage_effects`, which lacked that feed until
  GH #10880.
- **BAI N+1 storage** — no counterpart exists at either site: no `write_sets_incorporate_tx`, no
  `bal_emit_storage_changes`.

## Why the unit is phase × field, and not call site

Enumerating `jal ra` targets is a false-positive machine — 195 hits on `rlp_walk_next` alone, a pure helper
that owes no follow-up. **The obligation is per phase and per field**, because the two defects found in this
area were each *a phase that records with no emit for that phase*
(GH #10875, GH #10880). Both were the same shape: **one recorder, two call sites, only one carrying the
follow-up.** Distinguish such sites **by PC**, and identify which is which from the *following* instruction
rather than from source order.

Checks that came back clean, recorded so they are not repeated:

- `bal_emit_storage_changes` has exactly two call sites and one is `BalSerializerMeasureProbe`, off the
  verdict path ⇒ **one production caller**.
- `account_writes_emit_builder_tx` has three sites and **all three** are immediately followed by
  `account_writes_incorporate_tx`.
- `record_nonstorage_effect` has **25** call sites — too many to audit individually, and the matrix covers
  them only *collectively*, so the residual risk is a site recording outside any phase. That is one comparison
  of commit indices — *does any record happen after the last emit?* — and there are **no orphans**: on 23725
  (5 tx) 20 records with the last at commit 17,208,954 against 6 emits ending 17,254,746; on 11658 (2 tx)
  13 against 3; on 00566 (0 tx) 1 against 1. **Emits = ntx + 1 in every case**, the `+1` being the N+1 emit.

## Acceptance set for closing the remaining hole

Pre-registered so the post-fix measurement is a yes/no rather than an interpretation. Each shortfall is fully
accounted as **(missing N+1 changes) − (spurious reads)**; a re-encode identity control passed on the declared
bytes before every model.

| fixture | txs | now | target (= declared) | model |
|---|---|---|---|---|
| 23100 | 1 | 554 | **566** | drop 3 N+1 rows → 553, residual +1 |
| 23725 | 5 | 818 | **843** | drop 8 → 818, residual 0 |
| 23200 | 0 | 236 | **246** | drop 2 → 234, residual +2 |
| 23260 | 0 | 252 | **264** | drop 2 → 250, residual +2 |
| 04460 | 0 | 228 | **233** | drop 1 → 227, residual +1 |

### Do-not-move pins, and which of them are CONDITIONAL

**A pin at the *declared* length is robust; a pin at a *defective* length is conditional on the defect staying
open.** Stated per pin so a later reader cannot mistake a legitimate other fix for this one overreaching:

| pin | robust? | why |
|---|---|---|
| 00566 / 00346 / 00578 at **264 / 263 / 264** | ✅ robust | pinned at **declared**; those blocks pass (`fail_code` 0) so any correct change keeps them equal to declared |
| 00565 at **350** | ✅ robust | 350 **is** declared. Its known open defect — the sender's post-balance high by exactly `value + gas_limit × gas_price` — is an **equal-length** content mismatch, so fixing it cannot move the length |
| **11658 at 662, 11659 at 710** | ⚠️ **CONDITIONAL on GH #10645** | both are **over** declared (630 / 648) *because of* that defect — see below |

**11658 and 11659 are the #10645 fixtures.** Modelled (drop the fabricated `code_changes` entry, convert the
destroyed account's `storage_change` into a `storage_read`), with a re-encode identity control on the rebuilt
bytes first:

| fixture | now | after #10645 | delta | vs declared |
|---|---|---|---|---|
| 11658 | 662 | **603** | **−59** | still **27 under** 630 |
| 11659 | 710 | **651** | **−59** | **3 over** 648 |

⇒ **If #10645 lands before the N+1 storage feed, expect −59 on each** — that is correct, not a regression.
Neither closes on #10645 alone, and in opposite directions: 11658's residual is the unlocalised missing account
entry (it emits 13 account entries against declared 14); 11659 ends 3 bytes over.

*A pinned number whose validity depends on an unstated precondition is a status line with a hidden date* — the
same decay this document exists to prevent.

**The residual is read-exclusion coupling** (`block_access_lists.py:549-552` — a slot is excluded from
`storage_reads` iff it has a `storage_change`). With no change to exclude against, the guest emits the slot as
a read. On 23200 the predeploy's `storage_changes` is `c0` — an empty list — while its `storage_reads` carries
13 slots *including* slot 0 and slot 2, against declared's 11 *without* them. **The residual is per-fixture,
not a formula**: 23100 is +1 for three dropped rows because only one of its dropped slots was also read.

⚠️ **This makes over-long a distinguishable failure mode.** A fix that emits the N+1 changes but fails to
re-exclude the reads lands **2 bytes over** declared on 23200, not short.

## Reading a trace against this document

- `bv_fail_code == 60` is `.Lbv_bal_digest_mismatch` (`BlockVerdictReceiptsTail.lean:323`) — a **failing**
  verdict. A passing block is `0`. Equal `rebuilt_len`/`supplied_len` at 60 is an **equal-length content
  mismatch**, not agreement.
- The two `block_verdict_withdrawal_nonstorage_effects` sites are **at most one per block** — exactly one
  whenever a BAL is produced, and **neither** when the block is rejected earlier (00350, `fail_code` 7,
  `rebuilt_len` 0). A zero on both is not evidence of a missing call.
- A moved layout invalidates a PC list **silently**, and a stale `.bss` address still reads **live memory**.
  Re-derive every PC and data address per ELF.
