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
| Sender aggregation | Up to `9523` txs, repeated or distinct senders | Sender count and sender-balance tables derive from `bvMtxFullTxCap = 9523`; active execution loop remains `bvMtxActiveTxCap = 1024` | Partial: aggregation substrates have full-cap probes; end-to-end active-loop migration remains under `evm-asm-vv4hr.1`. |
| Committed storage threading | All unique `(recipient, slotKey)` keys reachable under 200M | Active `bvMtxCommittedChunkCapacity = 512`; target `bvMtxCommittedFullKeyCap = 600000` | Gap: migrate upsert/lookup/wiring under `evm-asm-vv4hr.2`. |
| System storage side capture | All modeled system-call SSTORE rows needed by BAL checks | `bvSystemStorageLogCapacity = 600000`, derived as `2 * 30000000 / 100` for withdrawal plus consolidation system calls at the cheapest SSTORE gas floor | Capacity boundary covered by `evm-asm-vv4hr.7.1`; precise tuple binding/evidence remains under `evm-asm-vv4hr.7.2`/`.7.3` and ungate bead `evm-asm-40igg`. |
| Receipt records | Up to the supported tx count | `bvReceiptRecordCapacity = bvMtxFullTxCap = 9523`; `bvRecordBloomsBytes` and `bvRecordLogsDescBytes` derive from the same cap | Covered for per-tx record/bloom/descriptor storage; log capture and RLP materialization remain separate. |
| Block log descriptors | All supported execution-derived logs | `bvBlockLogDescCapacity = 128` | Gap: `evm-asm-vv4hr.3.2`. |
| Log/RLP bytes | Aggregate log payloads and receipt-list RLP for supported blocks | `bvBlockLogDataBytes = 65536`, `bvLogsRlpArenaBytes = 65536`, `bvReceiptsRlpBytes = 65536`, `bvReceiptListPayloadBytes = 32768`, `bvReceiptConsensusDescCapacity = 128` | Gaps: `evm-asm-vv4hr.3.3` and `evm-asm-vv4hr.3.4`. |
| Execution requests hash input | EIP-6110 deposits `8192 * 192`, withdrawals `16 * 76`, consolidations `2 * 116` | `erh_blob = 1572865` | Hash helper covers the deposit body cap. |
| Execution-derived deposit body staging | Same deposit body cap when deriving requests from logs | `c1_dbody = 32768`, `c1_log_records = 81920` | Gap: `evm-asm-vv4hr.4`. |
| System-call payload staging | Witness code plus 100k preloads plus M29 slack | `c1StagingBytes = bsrMaxWitnessBytes + bsrAccountSlotCap * 64 + 16384` | Covered by shared guard for current staging model. |
| Witness node index | All `witness.state` records representable under the 512 KiB accepted witness byte guard | `mptWitnessIndexCapacity = 131072` records; arena `6291456` bytes | Covered for fixed-arena record count; lookup/code/header performance work continues under `evm-asm-vv4hr.5`. |
| Debug/probe output | Every capacity bail is observable without crashing | Fixed verdict/debug layouts | Gap: `evm-asm-vv4hr.6`. |

## Follow-Up Beads

Every discovered 200M resource gap has a P1 child bead:

- `evm-asm-vv4hr.1`: finish lifting multi-tx verdict algorithms from the
  `1024` active loop cap to the `9523` transaction target, or replace them
  with streaming/chunked designs. Cheap per-tx result arenas are already sized
  from `bvMtxFullTxCap`.
- `evm-asm-vv4hr.2`: extend committed-storage threading beyond the active `512`
  unique `(recipient, slotKey)` entries toward `bvMtxCommittedFullKeyCap = 600000`,
  the system-call SSTORE side-capture row cap. The bound is unique-key based:
  duplicate writes update in place and do not consume additional committed slots.
- `evm-asm-vv4hr.3`: stream or resize receipt/log materialization so receipt
  roots and logs bloom are not capped by 128 log descriptors, 128 consensus
  receipt descriptors, 32 KiB receipt-list scratch, or 64 KiB log/receipt RLP
  arenas. Per-tx receipt records are already sized to the 9,523 full-tx target.
- `evm-asm-vv4hr.4`: make execution-derived EIP-6110 deposit request bodies
  cover the full deposit cap instead of the current `c1_dbody` /
  `c1_log_records` staging limits.
- `evm-asm-vv4hr.5`: extend witness/header/code indexing and step behavior so
  valid large witnesses do not fail through code/header linear scans or
  `EmulationNoCompleted`. The `witness.state` NodeDb fixed arena is now sized
  from the 512 KiB accepted witness byte guard: 524288 / 4 = 131072 records,
  or 6291456 bytes of RAM at 48 bytes per sorted record.
- `evm-asm-vv4hr.6`: make verdict debug/probe output report every resource cap
  precisely without truncation, uninitialized reads, or debug-probe exits.
- `evm-asm-vv4hr.7`: make system-storage side capture precise under full
  resource load and ungate modeled system tuple checks only when capture is
  complete. Child `evm-asm-vv4hr.7.1` covers the side-capture capacity
  boundary; `.7.2` binds modeled-system tuple checks to complete capture, and
  `.7.3` adds full-resource evidence.

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
