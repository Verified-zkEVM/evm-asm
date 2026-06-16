# EEST 200M Resource Audit

This audit tracks fixed RISC-V stateless guest buffers and algorithms against
the target accepted by `evm-asm-vv4hr`: process every Amsterdam/Prague/Osaka
EEST block whose actual decoded resources fit under 200M gas.

The distinction matters:

- Protocol/test limits are the limits imposed by execution-specs, SSZ/RLP, or
  the EEST fixture family.
- Actual decoded resources are the counts in one concrete block after parsing:
  transaction count, BAL item count, witness bytes, receipt/log records, system
  request body bytes, and so on.
- Implementation caps are the guest's current static arenas or algorithmic
  limits. A high declared gas limit is not by itself a reason to reject; the
  guest should reject only when the actual decoded resources exceed a sound
  bound or the shape is genuinely unsupported.

## Current Coverage

| Area | 200M target | Current implementation | Status |
|---|---:|---:|---|
| BAL items | `200000000 / 2000 = 100000` | `bsrMaxBalItems = 100000` | Covered for item count. |
| State changes | BAL plus modeled system/withdrawal changes | `bsrMaxStateChanges = 100018` | Covered for current modeled changes. |
| Per-account BAL slot staging | Up to the full BAL item budget for one account | `bsrAccountSlotCap = 100000` | Covered for staging capacity. |
| Per-slot tuple sequence | One tuple per tx plus seed/system margin | `bsrMaxTuplesPerSlot = 10000` | Covers `9523` minimum-gas txs plus margin. |
| Witness bytes | Large valid state witnesses under the 200M target | `bsrMaxWitnessBytes = 524288` | Size guard widened, but record count/perf still needs work. |
| Transaction arrays | `floor(200000000 / 21000) = 9523` txs | Cheap u64/log-window arenas use `bvMtxFullTxCap = 9523`; active execution loop remains `bvMtxActiveTxCap = 1024` | Partial: foundation split landed; algorithmic cap gaps remain under `evm-asm-vv4hr.1`. |
| Sender aggregation | Up to `9523` txs, repeated or distinct senders | Active sender tables use `bvMtxActiveTxCap = 1024` | Gap: aggregation slices under `evm-asm-vv4hr.1`; related existing P1 `evm-asm-bmvmx.5.5.7.3`. |
| Committed storage threading | All unique `(recipient, slotKey)` keys reachable under the supported storage-log arena | Active `bvMtxCommittedChunkCapacity = 512`; target `bvMtxCommittedFullKeyCap = 16384` | Gap: migrate upsert/lookup/wiring under `evm-asm-vv4hr.2`. |
| System storage side capture | All modeled system-call SSTORE rows needed by BAL checks | `bvSystemStorageLogCapacity = 16384`; some paths are best-effort | Gap: `evm-asm-vv4hr.7`; related ungate beads `evm-asm-hwngs`, `evm-asm-40igg`. |
| Receipt records | Up to the supported tx count | `bvReceiptRecordCapacity = bvMtxFullTxCap = 9523` | Covered for per-tx records; log/RLP capacity remains separate. |
| Block log descriptors | All supported execution-derived logs | `bvBlockLogDescCapacity = 128` | Gap: `evm-asm-vv4hr.3`. |
| Log/RLP bytes | Aggregate log payloads and receipt-list RLP for supported blocks | `bvBlockLogDataBytes = 65536`, `bvLogsRlpArenaBytes = 65536`, `bvReceiptsRlpBytes = 65536` | Gap: `evm-asm-vv4hr.3`. |
| Execution requests hash input | EIP-6110 deposits `8192 * 192`, withdrawals `16 * 76`, consolidations `2 * 116` | `erh_blob = 1572865` | Hash helper covers the deposit body cap. |
| Execution-derived deposit body staging | Same deposit body cap when deriving requests from logs | `c1_dbody = 32768`, `c1_log_records = 81920` | Gap: `evm-asm-vv4hr.4`. |
| System-call payload staging | Witness code plus 100k preloads plus M29 slack | `c1StagingBytes = bsrMaxWitnessBytes + bsrAccountSlotCap * 64 + 16384` | Covered by shared guard for current staging model. |
| Witness node index | All witness records needed by valid 200M blocks | `MptWitnessIndex` cap `8192` records | Gap: `evm-asm-vv4hr.5`. |
| Debug/probe output | Every capacity bail is observable without crashing | Fixed verdict/debug layouts | Gap: `evm-asm-vv4hr.6`. |

## Follow-Up Beads

Every discovered 200M resource gap has a P1 child bead:

- `evm-asm-vv4hr.1`: finish lifting multi-tx verdict algorithms from the
  `1024` active loop cap to the `9523` transaction target, or replace them
  with streaming/chunked designs. Cheap per-tx result arenas are already sized
  from `bvMtxFullTxCap`.
- `evm-asm-vv4hr.2`: extend committed-storage threading beyond the active `512`
  unique `(recipient, slotKey)` entries toward `bvMtxCommittedFullKeyCap = 16384`,
  the existing persistent storage exec-log row cap. The bound is unique-key based:
  duplicate writes update in place and do not consume additional committed slots.
- `evm-asm-vv4hr.3`: stream or resize receipt/log materialization so receipts
  and logs are not capped by 16 records, 128 descriptors, or 64 KiB payload
  arenas.
- `evm-asm-vv4hr.4`: make execution-derived EIP-6110 deposit request bodies
  cover the full deposit cap instead of the current `c1_dbody` /
  `c1_log_records` staging limits.
- `evm-asm-vv4hr.5`: extend witness/header/code indexing and step behavior so
  valid large witnesses do not fail through index overflow or
  `EmulationNoCompleted`.
- `evm-asm-vv4hr.6`: make verdict debug/probe output report every resource cap
  precisely without truncation, uninitialized reads, or debug-probe exits.
- `evm-asm-vv4hr.7`: make system-storage side capture precise under full
  resource load and ungate modeled system tuple checks only when capture is
  complete.

Existing related P1s:

- `evm-asm-bmvmx.5.5.7.3`: sender debit aggregation for repeated senders at
  full tx capacity.
- `evm-asm-hwngs`: make system storage side-capture failures precise instead
  of best-effort after request bodies are copied.
- `evm-asm-40igg`: ungate the modeled-system tuple comparator once the side
  capture/check is precise.

## Notes

The BAL/state-root buffers are already sized to Amsterdam's 200M gas-derived
BAL item budget. The remaining risk is mostly outside those arrays: tx-count
dependent verdict arenas, receipt/log payload materialization, request-body
derivation, committed storage threading, and lookup algorithms that can exceed
step budgets even when byte buffers are large enough.
