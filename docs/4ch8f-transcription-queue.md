# Demand-first String→Program transcription queue (GH #12035)

Which unconverted guest routine to transcribe **next**, ranked by what its
transcription would *unblock* — not by how big it is.

The repo already has two conversion censuses, and neither ranks anything:
`docs/4ch8f-asm-to-program-coverage.md` classifies every `*Function : String`
by shape (ALREADY-STRUCTURED / READY-WAVE3 / BLOCKED_ON_.6 / …), and
`docs/4ch8f-guest-image-coverage.md` measures which `.text` bytes a converted
`_prog` covers. Both answer *how big* and *how hard*. Neither answers *who is
waiting*, so transcription picked from either is transcription ordered by
**cost** — which is how routines that four proof lanes are stalled behind stay
`String`-only because they are large, while leaves nobody is blocked on keep
landing. This document is the missing third axis.

**GENERATED FILE — do not hand-edit.** Rendered from
`scripts/asm-fixtures/transcription-queue-template.md` (prose and placeholder
slots only — no figures) plus live numbers from the generator:

```
python3 scripts/transcription_queue.py --write-doc      # regenerate THIS FILE
python3 scripts/transcription_queue.py --check-doc      # drift check
python3 scripts/transcription_queue.py                  # human summary
python3 scripts/transcription_queue.py --all            # every named row
python3 scripts/transcription_queue.py --self-test      # scorer/matcher self-test
python3 scripts/transcription_queue.py --refresh-issues # the ONE network mode
```

`scripts/check-transcription-queue.sh` wraps `--check-doc` for CI. Every mode
except `--refresh-issues` reads the tree and a committed issue snapshot only,
so the same tree renders the same bytes.

## 1. Method

**Universe and cost.** The rows are the unconverted half of the guest-image
census, taken from `guest_image_coverage.load_converted()` — a `.text` symbol
is *converted* iff a `scripts/asm-fixtures/MANIFEST.tsv` row binds it to a
`"<entry>:\n" ++ emitProgram…` Function whose `_prog` carries a kernel-checked
`#guard <prog>.length = N` pin. Extent (symbol start → next symbol) is the
**cost** column. Cost is printed and never scored.

> `EvmAsm/Codegen/GuestAddrs.lean` is **not** consulted, and must not be: it
> lists `String`-only routines that are called by address and omits probe-only
> routines that exist, so presence there proves nothing in either direction.
> The representation-independent check this file uses instead is the emitted
> label literal (§4).

**Demand.** Five evidence sources, weighted so that *being named as a blocker*
always beats *being popular*:

| signal | weight | source |
|---|---:|---|
| obligation blocker | 100 per distinct obligation | `EvmAsm/Progress/Obligations.lean` `blockedBy` (the `note`/`auditedAt` fields are excluded — a note saying "X is now `.proven`" is the *opposite* of a blocking claim) |
| named residual | 40 per declaration | a declaration whose NAME carries `Residual` (the `…ResidualNote` discharge-owner convention) and whose text names the routine |
| open `proof` issue | 25 per issue | `scripts/proof-issues.json`, a committed snapshot of `gh issue list --label proof --state open` (12 issues) |
| registry gate | 15 per row | a `.conditional`/`.execSpec` row in `EvmAsm/Progress/Routines.lean` whose `gate`/`notes` prose names the routine |
| call site | 2 each, capped at 30 (≤ 60) | emitted-instruction references only, using `scripts/check_routine_liveness.py`'s pattern set — a name is not a contract, so docstrings and `#guard`s count for nothing |

`60 < 100` by construction, and `--self-test`
asserts it: no amount of call-site popularity can outrank a single obligation
row. The weights are *ratios*, not calibrated constants — the only property
that matters is the order they impose.

Issue **#12035 is excluded from the issue signal.** It is this
queue's own issue, and it names the routines it expects to see ranked highly;
counting it would make the ranking circular — the queue would "discover"
exactly what its specification told it to find. Everything in §2 stands on
evidence that predates it.

**A signal scoring zero is not a broken signal.** The residual scanner reads
94 `Residual`-named declarations today and 0
of them name an unconverted routine. When that second figure is 0 it is a
result, not a bug: every named discharge owner in the tree
(`witnessLookupResidualNote`, `zkvmSha256ResidualNote`, `hpDecodeResidualNote`,
the `*_wl_call_residual` family) points at a routine that has already been
transcribed. Read a zero there as "the residual wall those notes described has
been cleared", and re-check the scanner only if it also disagrees with a `grep`
for `ResidualNote`.

**The queue proper is the *named* set** — routines some human-written artifact
says are blocking. Routines whose only signal is call-site popularity are the
tail (§5), reported as a count and a top-N rather than dressed up as ranked
work.

## 2. The queue (top 25 of 42)

| # | symbol | demand | evidence | shape | cost (B) |
|---:|---|---:|---|---|---:|
| 1 | `rlp_item_size` | 257 | obl 3; #10780,#11341; gate 5; calls 16 | label-string | 140 |
| 2 | `witness_index_build` | 233 | obl 7,10; #11800; calls 4 | label-string | 632 |
| 3 | `witness_codes_index_build` | 237 | obl 7,10; #11800; calls 6 | derived (base `witness_index_build`) | 632 |
| 4 | `rlp_item_span` | 202 | obl 3; #10780; gate 3; calls 16 | label-string | 212 |
| 5 | `.dispatch_loop` | 170 | obl 4; #11801,#11802; calls 10 | label-string | interior |
| 6 | `h_ADD` | 150 | obl 4; #11801,#11802 | handler-spec | 168 |
| 7 | `stage_system_call` | 118 | obl 4; calls 9 | label-string | 284 |
| 8 | `rlp_walk_init` | 115 | #11901; gate 2; calls 188 | label-string | 212 |
| 9 | `witness_codes_lookup_by_hash` | 114 | obl 10; calls 7 | derived (from converted `witness_lookup_by_hash`) | 620 |
| 10 | `h_KECCAK256` | 100 | obl 5 | handler-spec | 648 |
| 11 | `h_BALANCE` | 100 | obl 5 | handler-spec | 680 |
| 12 | `h_LOG0` | 100 | obl 5 | handler-spec | 756 |
| 13 | `h_EXTCODESIZE` | 100 | obl 5 | handler-spec | 776 |
| 14 | `h_LOG1` | 100 | obl 5 | handler-spec | 788 |
| 15 | `h_LOG2` | 100 | obl 5 | handler-spec | 820 |
| 16 | `h_LOG3` | 100 | obl 5 | handler-spec | 852 |
| 17 | `h_LOG4` | 100 | obl 5 | handler-spec | 884 |
| 18 | `h_SLOAD` | 100 | obl 5 | handler-spec | 1408 |
| 19 | `h_EXTCODECOPY` | 100 | obl 5 | handler-spec | 1472 |
| 20 | `h_REVERT` | 100 | obl 5 | handler-spec | 1500 |
| 21 | `h_EXTCODEHASH` | 100 | obl 5 | handler-spec | 1644 |
| 22 | `h_SSTORE` | 100 | obl 5 | handler-spec | 2188 |
| 23 | `h_RETURN` | 100 | obl 5 | handler-spec | 2448 |
| 24 | `h_DELEGATECALL` | 100 | obl 5 | handler-spec | 3168 |
| 25 | `h_STATICCALL` | 100 | obl 5 | handler-spec | 3168 |

Reading the columns: **demand** is the score; **evidence** is what produced it
(`obl N` = obligation N's blocker list, `#N` = open issue, `gate N` = N gated
registry rows, `resid N` = N residual declarations); **shape** is §4; **cost**
is extent bytes, or `interior` for a label that shares an address with the next
symbol (`.dispatch_loop` sits at the same address as
`.runtime_tx_message_entry`, so the next-symbol extent model gives it 0 — its
real transcription cost is the enclosing dispatcher body's).

A `derived` row can never rank above the base it is `.replace`-generated from,
however its own signals score: the base is a hard prerequisite, so derived rows
sort on the base's score and lose every tie.

## 3. Declared judgement calls

Everything below is a **hand-written claim** that a piece of evidence is about
a symbol it does not spell. It is listed here, in full, so it can be audited or
challenged — this is the only hand-ranking anywhere in the generator.

**Spec-side identifiers.** Names from the Lean spec side that denote a guest
routine:

| identifier | guest symbol | why |
|---|---|---|
| `build_code_db` | `witness_codes_index_build` | SpecRef `WitnessState.build_code_db`; the guest side is the code-DB index builder (#11800 item 2) |
| `build_node_db` | `witness_index_build` | SpecRef `WitnessState.build_node_db`; the guest routine that populates `node_db_buckets` from the witness section is `witness_index_build` (#11800's target) |
| `dispatch_loop` | `.dispatch_loop` | the guest label carries a leading dot; prose writes it without one |

**Prose anchors.** Regexes matched against obligation blocker text and issue
bodies, for evidence that describes a routine without naming it:

| pattern | guest symbol | why |
|---|---|---|
| `fetch[-/]decode[-/](?:dispatch|table[- ]jump)` | `.dispatch_loop` | #11801's dispatch-step lemma is exactly the `.dispatch_loop` fetch/decode/table-jump body |
| `\bExecutionSeam\b` | `.dispatch_loop` | #11802's `execute : ExecutionSeam` parameter is instantiated by the dispatch loop plus its handlers |
| `simulation bridge from dispatched handlers` | `.dispatch_loop` | obligation 4's blocker names the bridge whose machine side is the dispatch loop |

**Opcode mnemonics are handled mechanically, not by hand.** Obligation 5's
blockers are `.opcode "RETURN"`-shaped plus a counted set ("14 `.execSpec`
entries have no RV64 subroutine"); neither spells `h_RETURN`. The mnemonic list
comes from `EvmAsm/Progress.lean`'s registry (so a renamed or promoted opcode
drops out on its own), the range form `LOG0..4` expands to `h_LOG0 … h_LOG4`,
and a mnemonic only counts where it is used **as** an opcode — backticked,
`.opcode "…"`, or `h_…`. A bare word-boundary sweep is a homonym generator: the
prose is full of `does NOT yet discharge`, `the CALL family`, `AND`, `GAS`, and
an earlier revision of this script ranked `h_NOT` eighth on exactly that. For
the same reason a tier is expanded only where it is *counted* (`14
\`.execSpec\` entries`) — obligation 3's "`rlp_item_span` is `.conditional`
short-list only" is a claim about one routine, not about the opcode set.

Every application of a declared alias, anchor, tier set or derivation roll-up
in the current tree:

| symbol | via | why |
|---|---|---|
| `witness_index_build` | alias `build_node_db` (#11800) | SpecRef `WitnessState.build_node_db`; the guest routine that populates `node_db_buckets` from the witness section is `witness_index_build` (#11800's target) |
| `witness_index_build` | alias `build_node_db` (obligation 10) | SpecRef `WitnessState.build_node_db`; the guest routine that populates `node_db_buckets` from the witness section is `witness_index_build` (#11800's target) |
| `witness_index_build` | alias `build_node_db` (obligation 7) | SpecRef `WitnessState.build_node_db`; the guest routine that populates `node_db_buckets` from the witness section is `witness_index_build` (#11800's target) |
| `witness_index_build` | rolled up from `witness_codes_index_build` | `witness_codes_index_build` is built by `.replace` from `witness_index_build`; the base must be transcribed first |
| `witness_codes_index_build` | alias `build_code_db` (#11800) | SpecRef `WitnessState.build_code_db`; the guest side is the code-DB index builder (#11800 item 2) |
| `witness_codes_index_build` | alias `build_code_db` (obligation 10) | SpecRef `WitnessState.build_code_db`; the guest side is the code-DB index builder (#11800 item 2) |
| `witness_codes_index_build` | alias `build_code_db` (obligation 7) | SpecRef `WitnessState.build_code_db`; the guest side is the code-DB index builder (#11800 item 2) |
| `.dispatch_loop` | anchor `\bExecutionSeam\b` (#11802) | #11802's `execute : ExecutionSeam` parameter is instantiated by the dispatch loop plus its handlers |
| `.dispatch_loop` | anchor `fetch[-/]decode[-/](?:dispatch|table[- ]jump)` (#11801) | #11801's dispatch-step lemma is exactly the `.dispatch_loop` fetch/decode/table-jump body |
| `.dispatch_loop` | anchor `simulation bridge from dispatched handlers` (obligation 4) | obligation 4's blocker names the bridge whose machine side is the dispatch loop |
| `h_ADD` | alias `ADD` (#11801) | opcode registry mnemonic; guest handler(s) `h_ADD` |
| `h_ADD` | alias `ADD` (#11802) | opcode registry mnemonic; guest handler(s) `h_ADD` |
| `h_ADD` | alias `ADD` (obligation 4) | opcode registry mnemonic; guest handler(s) `h_ADD` |
| `h_KECCAK256` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_BALANCE` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_LOG0` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_EXTCODESIZE` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_LOG1` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_LOG2` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_LOG3` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_LOG4` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_SLOAD` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_EXTCODECOPY` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_REVERT` | alias `REVERT` (obligation 5) | opcode registry mnemonic; guest handler(s) `h_REVERT` |
| `h_EXTCODEHASH` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_SSTORE` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_RETURN` | alias `RETURN` (obligation 5) | opcode registry mnemonic; guest handler(s) `h_RETURN` |
| `h_DELEGATECALL` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_STATICCALL` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_CREATE` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_CREATE2` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_CALLCODE` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |
| `h_SELFDESTRUCT` | alias `SELFDESTRUCT` (obligation 5) | opcode registry mnemonic; guest handler(s) `h_SELFDESTRUCT` |
| `h_CALL` | tier set `.execSpec` (obligation 5) | the blocker counts "14 `.execSpec` entries" — a SET, not a symbol; expanded from `Progress.lean`'s registry so it tracks promotions |

## 4. Authoring shape (what transcription actually costs)

How the routine's text reaches the image — the transcribability question that
`GuestAddrs.lean` cannot answer:

| shape | count |
|---|---:|
| `derived` | 3 |
| `handler-spec` | 89 |
| `label-string` | 333 |
| `not-authored` | 105 |

* `label-string` — an emitted label literal `"<sym>:\n"` (or `"<sym>:"`) exists
  in an `EvmAsm/**` Lean file; the enclosing `def` is recorded in the
  generator's detail column. Directly transcribable.
* `handler-spec` — an `OpcodeHandlerSpec` row (`label := "<sym>"`) whose body is
  raw `preBody`/`tail` strings; the entry label is emitted by the table
  renderer, so no label literal exists. `h_KECCAK256`
  (`EvmAsm/Codegen/Programs/EvmHashHandlers.lean`) is the shape's type
  specimen: `preBody` and `tail` are `String`, `body` is `[]`.
* `derived` — the Function is built by `.replace` from another symbol's
  Function. The whole `witness_codes_*` family is generated this way from the
  `witness_*` state-index family, so it is **not** independently
  transcribable — converting the base is the prerequisite.
* `not-authored` — none of the above; the symbol reaches the image through a
  composite emitter, a layout template, or a data section.

The label test demands the colon be followed by `\n` or the closing quote.
The loose form matches the roundtrip stub
`"witness_codes_lookup_by_hash: ret"` in
`EvmAsm/Codegen/Programs/CallFrameRoundtrip.lean`, which would report a 620-byte
routine as authored-and-ready when what exists is a two-token placeholder.

## 5. The popularity tail

276 unconverted routines have call sites but are named by no obligation,
residual, issue or gate; 212 have no signal at all. These are **not**
ranked work: a heavily-called routine that nothing is waiting on is still
nothing anyone is waiting on. Top 25 by call count, as a watchlist:

| symbol | call sites | shape | cost (B) |
|---|---:|---|---:|
| `rlp_field_to_u64_strict` | 143 | label-string | 148 |
| `rlp_content_to_u64_strict` | 87 | label-string | 88 |
| `rlp_content_to_u256_be_strict` | 79 | label-string | 104 |
| `bal_rlp_scalar_rlp_len` | 35 | label-string | 84 |
| `mpt_leaf_node_encode_from_nibbles` | 31 | label-string | 500 |
| `bnq_mul` | 29 | label-string | 400 |
| `sg_memcpy` | 28 | label-string | 32 |
| `bal_rlp_list_header_len` | 28 | label-string | 48 |
| `bal_rlp_emit_list_header` | 28 | label-string | 196 |
| `account_read_record` | 28 | label-string | 292 |
| `blq_mul` | 28 | label-string | 472 |
| `bal_serializer_u64_to_field` | 24 | label-string | 24 |
| `account_writes_lookup_current` | 23 | label-string | 396 |
| `bal_serializer_addr_matches_be` | 22 | label-string | 56 |
| `keccak_absorb` | 20 | label-string | 116 |
| `bal_rlp_emit_scalar` | 20 | label-string | 224 |
| `account_writes_latest_balance` | 19 | label-string | 320 |
| `runtime_access_account_charge` | 19 | label-string | 476 |
| `record_nonstorage_effect` | 18 | label-string | 8 |
| `sg_load_u32le` | 17 | label-string | 48 |
| `frame_return` | 14 | label-string | 1636 |
| `mpt_bounded_encode_leaf_ref` | 12 | label-string | 216 |
| `runtime_access_account_seed` | 11 | label-string | 220 |
| `mpt_bounded_encode_extension` | 11 | label-string | 276 |
| `evm_storage_access_charge_key` | 11 | label-string | 460 |

## 6. What this queue CANNOT see

A queue that overstates its coverage is worse than one that admits its blind
spots. In rough order of how much they matter:

1. **Unwritten demand.** A proof lane blocked on a routine that nobody recorded
   in an obligation, a residual, an issue or a gate scores zero here. The
   queue measures *written-down* demand, and its accuracy is bounded by the
   freshness of `Obligations.lean` and the issue tracker.
2. **Stale demand.** The converse: a blocker whose transcription already landed
   still scores until someone edits the row. Obligations 7 and 10 currently
   describe `witness_lookup_by_hash` as "`String`-only … 620 B UNCONVERTED"
   although it is converted and in `guestImageEntries`; the routine correctly
   does **not** appear in §2 (the universe is computed, not read from the
   prose), but the prose that named it is now wrong. The universe is always
   fresher than the evidence.
3. **Suffix-only mentions.** Symbol matching is strict on both sides
   (`witness_lookup_by_hash` does not match `witness_lookup_by_hash_indexed` —
   a different 200-byte symbol). The price is that a routine mentioned *only*
   as a suffixed theorem name (`<sym>_spec_within`) and never bare is invisible.
4. **Structural blocking that no prose states.** `.dispatch_loop` contains the
   per-opcode gas debit (`EvmAsm/Codegen/Dispatch.lean`, the
   `opcode_gas_costs` → `env+568` charge before the table jump). Because that
   code is inside a `String`, no triple can observe the debit at all, which
   silently weakens every handler-level gas claim downstream. Nothing in the
   tree says so in a form this script can read; the anchors in §3 catch
   `.dispatch_loop` for other reasons, and its rank should be read as a floor.
5. **Cost is a proxy.** Extent bytes measure the routine's size, not the
   difficulty of its proof obligations, its register discipline, or whether it
   is a multi-entry bundle or caller-local fragment (the classes
   `docs/4ch8f-asm-to-program-coverage.md` tracks and this file does not).
6. **Closed issues.** Only *open* `proof`-label issues count. A closed issue
   whose residual survived it contributes nothing.
7. **Non-`proof` labels.** Issues without the `proof` label are outside the
   snapshot entirely.

## 7. Cross-check against the other censuses

| figure | here | `docs/4ch8f-guest-image-coverage.md` |
|---|---:|---:|
| `.text` symbols | 905 | 905 |
| converted **and linked** | 375 | 375 |
| unconverted | 530 | 530 |
| unconverted bytes | 246132 | see below |

Both sides come from the same loader, so they agree by construction. Two
figures need care. First, **converted-and-linked is not the manifest total**:
`scripts/asm-fixtures/MANIFEST.tsv` has 425 conversion rows, of
which 50 have no entry symbol in the linker-facts table
(converted but not linked — gas helpers etc. awaiting wiring). Those are not
`.text` symbols, are not in `guestImageEntries`, and are **not** queue rows.
Quoting 425 as "converted symbols" is the easy error here.

Second, the guest-image doc reports **gap ranges**, of
which there is one more than there are unconverted symbols — the extra is the
`TAIL` gap on `requests_hash_verify` (12 B), a *converted* symbol whose `_prog`
is shorter than its linker extent. Gap bytes therefore exceed unconverted bytes
by exactly those 12 B. That range is real transcription-adjacent work, but it is
not a routine, so it has no queue row.

The `docs/4ch8f-asm-to-program-coverage.md` totals are **not** comparable: that
census counts `*Function : String` **defs** (including composites, probe
prologues and unlinked helpers), while this one counts **linked `.text`
symbols**. A single symbol can have several Function defs and a Function def
need not be linked, so neither total bounds the other.

Named-set cost: 57720 B of 246132 B unconverted
— i.e. the routines anything is demonstrably waiting on are a small fraction of
the unconverted mass, which is the point of ranking by demand rather than by
bytes.

## 8. Full named table (42 rows)

| # | symbol | demand | evidence | shape | cost (B) |
|---:|---|---:|---|---|---:|
| 1 | `rlp_item_size` | 257 | obl 3; #10780,#11341; gate 5; calls 16 | label-string | 140 |
| 2 | `witness_index_build` | 233 | obl 7,10; #11800; calls 4 | label-string | 632 |
| 3 | `witness_codes_index_build` | 237 | obl 7,10; #11800; calls 6 | derived (base `witness_index_build`) | 632 |
| 4 | `rlp_item_span` | 202 | obl 3; #10780; gate 3; calls 16 | label-string | 212 |
| 5 | `.dispatch_loop` | 170 | obl 4; #11801,#11802; calls 10 | label-string | interior |
| 6 | `h_ADD` | 150 | obl 4; #11801,#11802 | handler-spec | 168 |
| 7 | `stage_system_call` | 118 | obl 4; calls 9 | label-string | 284 |
| 8 | `rlp_walk_init` | 115 | #11901; gate 2; calls 188 | label-string | 212 |
| 9 | `witness_codes_lookup_by_hash` | 114 | obl 10; calls 7 | derived (from converted `witness_lookup_by_hash`) | 620 |
| 10 | `h_KECCAK256` | 100 | obl 5 | handler-spec | 648 |
| 11 | `h_BALANCE` | 100 | obl 5 | handler-spec | 680 |
| 12 | `h_LOG0` | 100 | obl 5 | handler-spec | 756 |
| 13 | `h_EXTCODESIZE` | 100 | obl 5 | handler-spec | 776 |
| 14 | `h_LOG1` | 100 | obl 5 | handler-spec | 788 |
| 15 | `h_LOG2` | 100 | obl 5 | handler-spec | 820 |
| 16 | `h_LOG3` | 100 | obl 5 | handler-spec | 852 |
| 17 | `h_LOG4` | 100 | obl 5 | handler-spec | 884 |
| 18 | `h_SLOAD` | 100 | obl 5 | handler-spec | 1408 |
| 19 | `h_EXTCODECOPY` | 100 | obl 5 | handler-spec | 1472 |
| 20 | `h_REVERT` | 100 | obl 5 | handler-spec | 1500 |
| 21 | `h_EXTCODEHASH` | 100 | obl 5 | handler-spec | 1644 |
| 22 | `h_SSTORE` | 100 | obl 5 | handler-spec | 2188 |
| 23 | `h_RETURN` | 100 | obl 5 | handler-spec | 2448 |
| 24 | `h_DELEGATECALL` | 100 | obl 5 | handler-spec | 3168 |
| 25 | `h_STATICCALL` | 100 | obl 5 | handler-spec | 3168 |
| 26 | `h_CREATE` | 100 | obl 5 | handler-spec | 3528 |
| 27 | `h_CREATE2` | 100 | obl 5 | handler-spec | 3592 |
| 28 | `h_CALLCODE` | 100 | obl 5 | handler-spec | 4360 |
| 29 | `h_SELFDESTRUCT` | 100 | obl 5 | handler-spec | 5412 |
| 30 | `h_CALL` | 100 | obl 5 | handler-spec | 8764 |
| 31 | `rlp_content_to_u64` | 62 | gate 2; calls 16 | label-string | 72 |
| 32 | `rlp_content_to_u256_be` | 49 | #11341; calls 12 | label-string | 104 |
| 33 | `account_write_record` | 47 | #11921; calls 11 | label-string | 576 |
| 34 | `bal_builder_ensure_account` | 41 | #12102; calls 8 | label-string | 268 |
| 35 | `account_writes_emit_builder_tx` | 39 | #12102; calls 7 | label-string | 1284 |
| 36 | `destroy_storage` | 31 | #11921; calls 3 | label-string | 400 |
| 37 | `bal_builder_append_nonce` | 29 | #12102; calls 2 | label-string | 220 |
| 38 | `bal_builder_append_code` | 27 | #12102; calls 1 | label-string | 216 |
| 39 | `bal_builder_append_balance` | 27 | #12102; calls 1 | label-string | 232 |
| 40 | `storage_writes_block_upsert` | 27 | #11921; calls 1 | label-string | 420 |
| 41 | `storage_write_record` | 27 | #11921; calls 1 | label-string | 580 |
| 42 | `block_state_root` | 17 | gate 1; calls 1 | label-string | 1592 |
