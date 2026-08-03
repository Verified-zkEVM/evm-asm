# Leaf-routine targeting table (GH #11312)

Ten stable, self-contained RISC-V routines paired with the `SpecRef` functions they should be
proven against — a **targeting artefact, not an inventory** (the issue's bar: a short table
that is right beats a long one that is aspirational). Each row is startable today: it is a
leaf in the **transitive** call graph of the emitted asm, or every transitive callee already
carries a whole-routine spec in `EvmAsm/Progress/Routines.lean`.

This table joins the two axes the existing docs cover separately: routine → spec
(`docs/rlp-spec-correspondence.md` and siblings, whose `Verdict`/`Basis` vocabulary the
follow-up rows should adopt when they land in `EvmAsm/Progress/Correspondence.lean`) and
Assertion → SpecRef (`docs/4ch8f-slstate-specref-correspondence.md`).

## Method — what was checked, and how

- **Call graph from the emitted asm, not names or prose.** Every fixture in
  `scripts/asm-fixtures/*.s` is the emitted text of one routine (first line `symbol:`);
  outgoing calls are literal `jal ra, <sym>` lines (386 fixtures; no `call` pseudo-op occurs
  in any fixture). Per symbol: extract `jal` targets with
  `r"\bjal\s+(?:ra|x1|x5|t0),\s*([A-Za-z_][A-Za-z0-9_]*)"` (the same capture family as
  `scripts/check_routine_liveness.py`), then take the transitive closure. "Leaf" below means
  **zero transitive callees**, not zero calls in the file.
- **Liveness per row** (dead-code rows are forbidden; see #11303): every listed symbol is
  present in the guest linker census (`scripts/asm-fixtures/symbol-addresses.tsv`) **and**
  has at least one incoming `jal ra, <sym>` call site in an emitted composition, cited below.
- **Verified set** for the "depends solely on verified" rows: the 15 symbols with witnessed
  rows in `EvmAsm/Progress/Routines.lean` (13 `.proven`, 8 `.conditional` rows).
- **`SpecRef` is a port and drifts** from execution-specs. Rows whose correctness depends on
  the spec's actual text should cite pinned `e5a8caf1b` alongside the `SpecRef` name when the
  proof lands; the `SpecRef` file:line anchors below are the port-side entry points.

Rule firing, recorded so the criterion is visibly non-vacuous: `eip8037_state_used_before_tx`
and `runtime_same_block_delegation_code` *look* startable (every fixture-level callee
verified) but transitively call `rlp_item_span`, which is `.unproven` — both excluded. That
is exactly the "leaf means leaf in the TRANSITIVE call graph" trap.

## The table

| # | RISC-V routine | `SpecRef` function(s) | data structures touched | separation-logic `Assertion`? |
|---|---|---|---|---|
| 1 | `bytes_to_nibbles` (leaf; 10 fixture in-edges; caller `Codegen/Programs/MptEncode.lean:365`) | `keyToNibbles` (`SpecRef/WitnessState.lean:78`); also the nibble-expansion half of `compact_to_nibbles` (`SpecRef/IncrementalMpt.lean:76`) — that half only, not the flag decode | input byte buffer → 2× nibble buffer | `bytesRegion` (`Rv64/MemRegion.lean:27`) covers both sides |
| 2 | `account_decode` (all callees verified: `rlp_list_nth_item` `.proven`; caller `Codegen/Programs/State.lean:262`) | `decode_account_from_leaf` (`SpecRef/WitnessState.lean:117`) | account leaf RLP → decoded account (nonce, balance, storage root, code hash) | `accountRlpIs` (`Stateless/State/AccountAssertions.lean:118`), `accountDecodedIs` (`:135`) — both exist; the best-prepared row here |
| 3 | `account_is_eip161_empty` (all callees verified: `rlp_list_nth_item`; caller `Codegen/Programs/BlockVerdictSimpleTransferGas.lean:65`) | `account_exists_and_is_empty` (`SpecRef/StateTracker.lean:229`) — the `EMPTY_ACCOUNT` comparison (`:55`); the guest tests the RLP form directly where the spec tests the decoded form, so the row's claim runs through row 2's decode | account leaf RLP | `accountRlpIs` (as row 2) |
| 4 | `mpt_node_kind` (all callees verified: `rlp_list_nth_item`; 4 fixture in-edges; caller `Codegen/Programs/Mpt.lean:229`) | the node-shape dispatch of `_decode_witness_node` (`SpecRef/IncrementalMpt.lean:182`) — 17-item branch vs 2-item leaf/extension, that dispatch only | RLP node bytes | input: `bytesRegion`; result side: `mptNodeIs` (`Evm64/MptAssertions.lean:635`) exists |
| 5 | `bal_canonical_sort` (leaf; 6 call sites `#guard`-pinned at `Codegen/Programs/BlockAccessListBuilder.lean:750`) | the stable sorts of `_build_from_builder` (`SpecRef/BlockAccessLists.lean:193`) | BAL builder entry runs (accounts, per-account slot lists) | **NONE** — needs a `balEntriesFrom`-style run predicate; mirror `teerEntriesFrom` (`Codegen/RegionPredicates.lean:344`). This is the listed prerequisite, and the row that flips the `.unproven` Correspondence entry and unblocks #10817's semantic half |
| 6 | `bloom_or_into` (leaf; caller `Codegen/Programs/Bloom.lean:761`; sibling leaf `bloom_eq`) | the OR-accumulation step of `logs_bloom` (`SpecRef/Fork.lean:101`) — the fold, not the per-log index derivation | 256-byte bloom filter | `bytesRegion` (256 bytes) suffices |
| 7 | `check_gas_limit` (leaf; caller `Codegen/Programs/HeaderChain.lean:314`) | `check_gas_limit` (`SpecRef/SeamShell.lean:200`) — same name, whole function | scalars only (register ABI) | n/a — register vocabulary (`regsSet`, `Rv64/SAsm/MultiRegRetTail.lean:51`) suffices, no memory assertion needed |
| 8 | `amsterdam_blob_gas_price` (leaf; caller `Codegen/Programs/Header.lean:889`) | `calculate_blob_gas_price` (`SpecRef/Gas.lean:136`) at the Amsterdam fork parameters; the port carries Python-checked `#guard`s (`Gas.lean:246`) | scalars only (register ABI) | n/a — as row 7 |
| 9 | `header_extract_number` (all callees verified: `rlp_field_to_u64`, `rlp_list_nth_item`, `rlp_content_to_u64`; caller `Codegen/Programs/ParentHashAtBlockNumber.lean:101`) | the `number` field of `_decode_header` (`SpecRef/Stateless.lean:75`) — one field of it, not the whole decode | header RLP region | `bytesRegion`; `rlpItemRegionFrom` (`Codegen/Programs/RlpEncodeBytesComposeSAsm.lean:860`) gives the `RLPItem`-typed phrasing |
| 10 | `bgv_u32le` (leaf; 8 fixture in-edges; caller `Codegen/Programs/BlockVerdictStateRoot.lean:681`) | the fixed-width LE reads of `deserialize_stateless_input` (`SpecRef/Guest.lean:29`) — the u32 accessor those reads reduce to | guest input blob (witness section offsets) | `bytesRegion`; proving this one leaf discharges a step in every one of its 8 callers |

Row 9 is the representative of a **family**: `header_extract_logs_bloom`,
`header_validate_extra_data_length`, and the seven `chain_validate_*` routines have the same
shape (verified RLP callees only, one `_decode_header` field or one header rule each). Once
row 9's pattern exists, the siblings are mechanical forks.

## Runners-up (not in the ten, recorded so the cut is visible)

- `blsg_lt_p`, `bnf_lt_p` (leaves): the `< p` range check inside `bytes_to_bls_field` /
  `bytes_to_g1` (`SpecRef/PrecompilesKzg.lean`, `SpecRef/PrecompilesCurve.lean`). Real
  SpecRef counterparts, but the precompile field towers have no assertion vocabulary at all
  yet — a bigger prerequisite than any single row above.
- `derive_withdrawal_requests`, `derive_consolidation_requests` (leaves): the request-derive
  half of `SpecRef/SeamShell.lean`'s `encode_execution_requests`. Startable, second tier.
- `b1_sender_table_find`, `exec_log_latest_value` (leaves): guest-specific structures with no
  reference function — would enter `Correspondence` as `noCounterpart`, so they orient no
  spec effort and are deliberately left out.
