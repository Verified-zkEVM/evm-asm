# RLP + SSZ — guest routine ↔ Lean spec ↔ model ↔ execution-specs correspondence

**Status: live authority** (docs/README.md class 1). Keep it correct; agents act
on it. Regenerate the evidence with the commands in [§7](#7-how-to-reproduce).

## Why this page exists

Closing [#10779](https://github.com/Verified-zkEVM/evm-asm/issues/10779) and
[#10782](https://github.com/Verified-zkEVM/evm-asm/issues/10782) showed both
were stale — the audit behind them counted theorems in the module that *emits*
each routine, while this repo keeps specs in sibling modules. Both routines
were already proven.

That exposes a sharper question than *"is it proven?"*: **does a proven routine
prove the right thing?** A whole-routine Hoare triple says the RISC-V code
implements the Lean spec written beside it. It says nothing about whether that
Lean spec agrees with the Ethereum reference implementation. If our decoder is
**stricter** than the reference, valid chain data gets false-rejected. If it is
**looser**, that is a false-accept — the one inviolable gate
(`docs/agents/spec-alignment-doctrine.md` §2).

This page answers that question for RLP and SSZ, and says plainly where it
cannot be answered yet.

## 0. Pins

Every claim below is relative to these. **Re-check them before trusting a row.**

| Artifact | Pin | Where recorded |
|---|---|---|
| `execution-specs` | `e5a8caf1b8055e4d805c7fb169edfa710914b7da` (tag `tests-zkevm@v0.6.2`) | this repo's gitlink |
| `ethereum-rlp` | **0.1.6** | `execution-specs/uv.lock` (constraint `>=0.1.6,<0.2` in `pyproject.toml:28`) |
| `eth-remerkleable` | **0.1.29** | `execution-specs/uv.lock` (constraint `>=0.1.29,<0.2`) |

> **The Python column is NOT machine-checked.** `scripts/check-spec-refs.sh`
> validates `execution-specs/<path>.py` citations against the submodule, but
> **neither RLP nor the generic SSZ codec lives there** — `ethereum_rlp` and
> `remerkleable` are external PyPI packages. Only the SSZ *schemas*
> (`forks/amsterdam/stateless_ssz.py`) are vendored and therefore gate-checked.
> The RLP column is instead backed by an executable differential ([§3](#3-rlp-model-layer-differential-result)); the SSZ column is prose.

> **Two traps when reproducing this.** (1) A fresh worktree has an *empty*
> `execution-specs/`; and the main checkout may sit at an **older** rev than the
> gitlink (it was at `tests-zkevm@v0.4.0` when this page was written). Always
> `git submodule update --init execution-specs` and check the tag. (2) `ethereum_rlp`
> **0.1.5** — which is what a stale environment supplies — silently accepts
> trailing bytes after a complete item; 0.1.6 rejects them. Reading the wrong
> version inverts a strictness verdict. This page was written against 0.1.6.

## 1. Verdict vocabulary

| Verdict | Meaning |
|---|---|
| `match` | The routine's spec and the reference agree on the routine's whole domain. |
| `domain-restricted` | Agrees, but the spec covers strictly less input than the reference accepts. Not a defect; a coverage gap that callers must respect. |
| `stricter` | We reject input the reference accepts → false-reject risk on valid chain data. |
| `looser` | We accept input the reference rejects → **soundness finding; file immediately.** |
| `no-counterpart` | A guest-specific operation with no reference function to compare to. |
| `n/a — unproven` | No spec exists, so the question is not answerable. This is an honest result, not a gap to paper over. |

**Basis** column — how much weight a verdict carries:

- **`diff`** — backed by the executable differential ([§3](#3-rlp-model-layer-differential-result)).
- **`bridged`** — the spec is stated over, or tied by a cited bridge lemma to,
  the shared model `EvmAsm.EL.RLP`, so it inherits the `diff` result.
- **`machine-only`** — the spec is stated over a *locally defined* machine
  predicate that re-derives the RLP rules independently of `EvmAsm.EL.RLP`.
  The differential result does **not** transfer formally. See [§5](#5-the-inheritance-gap).
- **`insp`** — by reading both sides; no executable or formal backing.

## 2. Layering (why the RLP question is smaller than it looks)

SpecRef never ported RLP — it **imports `EvmAsm.EL.RLP` verbatim**
(`docs/4ch8f-specref-port.md:36`), and the guest decoder proofs bridge to that
same model (`EvmAsm/Rv64/RLP.lean:6`). One shared definition serves both towers:

```
ethereum_rlp 0.1.6            (reference; external package, not vendored)
      │  §3 executable differential  ── 3757 records, 0 divergences
      ▼
EvmAsm.EL.RLP  (encode / decode / decodeFully)   ← shared model
      ▲                              ▲
      │ imported verbatim            │ bridge lemmas (per routine — §5)
SpecRef.*                     EvmAsm.Rv64.RLP.* / Codegen.Programs.Rlp*
                                     ▲
                              guest RISC-V routines
```

SSZ gets **no such shortcut**: the guest side (`EvmAsm/Stateless/SSZ/…`) was
written independently of `SpecRef/SszCodec.lean`, which was itself ported from
the consensus-specs `simple-serialize.md` prose rather than from `remerkleable`.

## 3. RLP model-layer differential result

`lake exe rlp-oracle-check` replays a committed corpus of **3757 records**
generated from the pinned reference by `scripts/rlp-python-oracle.py`:

| Class | Count |
|---|---:|
| agree | **3757** |
| stricter (reference accepts, we reject) | **0** |
| looser (reference rejects, we accept) | **0** |
| value mismatch | **0** |
| encode mismatch (`EL.RLP.encode` vs `rlp.encode`) | **0** |

> **`EvmAsm.EL.RLP.decodeFully` and `EvmAsm.EL.RLP.encode` agree with
> `ethereum_rlp` 0.1.6 on every record in the corpus.**

The corpus leads with hand-picked boundary cases pinning each canonicality rule
— non-canonical single byte (`8100`), leading-zero length (`b90038…`), long form
declaring `< 56` (`b837…`), both sides of the 55/56 boundary, trailing bytes
(`820102ff`), truncation, empty input, and a 12-deep nesting ladder — then adds
600 well-formed encodings with single-byte mutations/truncations/extensions, and
2000 seeded random buffers.

What is **not** compared: rejection *reasons*. The reference's messages describe
its own control flow (it reports a bare byte followed by trailing data as
`negative length`), which carries no obligation for a different implementation.
Requiring reason equality would manufacture failures.

Scope limits, stated honestly: the differential exercises `rlp.decode` /
`rlp.encode` — the whole-item entry points. It does **not** exercise
`decode_item_length` (the cursor-advance primitive) or the typed
`deserialize_to` layer directly; rows resting on those are marked `insp`.

## 4. RLP routines

Row list is `EvmAsm/Codegen/GuestAddrs.lean` (the authoritative linker-facts
enumeration — **not** `docs/4ch8f-guest-image-coverage.md`, whose addresses are
stale). All 18 `rlp_*` symbols, plus adjacent decoders in [§4b](#4b-adjacent-rlp-consuming-routines).

Theorem locations were verified by grepping each symbol tree-wide, never the
emitting module — the #10779/#10782 lesson.

| Guest routine | Whole-routine spec | Status | Model / SpecRef | Reference (`ethereum-rlp` 0.1.6) | Verdict | Basis |
|---|---|---|---|---|---|---|
| `rlp_walk_init` | `rlp_walk_init_spec_within` — `Rv64/RLP/WalkInit.lean:1590` | proven (9 paths) | `rlpWalkNextOk`, bridged via `Rv64/RLP/WalkDecodeBridge.lean` | `decode_to_sequence` entry | `match` | bridged |
| `rlp_walk_next` | `rlp_walk_next_spec_within` — `Rv64/RLP/WalkNext.lean:3924` | proven (18 paths → 6 statuses) | `rlpItemDecode` (`WalkNext.lean:3649`) + `WalkDecodeBridge` | `decode_item_length` + the `decode_joined_encodings` loop | `match` | bridged |
| `rlp_content_to_u64` | `rlp_content_to_u64_spec_within` — `Rv64/RLP/ContentToU64.lean:865` | proven (4 paths) | canonical-strict: status 2 `len > 8`, status 3 leading zero | `_deserialize_to_uint` at **`U64`** (`rlp.py:265`) | `match` (U64 fields only — see §4c) | insp |
| `rlp_content_to_u256_be` | `rlp_content_to_u256_be_spec_within` — `Rv64/RLP/ContentToU256Be.lean:998` | proven (4 paths) | local predicates only | `_deserialize_to_uint` at **`U256`** | `match` (U256 fields only — see §4c) | machine-only + insp |
| `rlp_item_size` | `rlp_item_size_spec_within` — `Codegen/Programs/RlpSpliceHelperSpec.lean:703` | **partly** — short forms only (`SpanForm`, `:599`); long string `0xb8–0xbf` and long list `0xf8–0xff` NOT covered | ties to `(encode item).length` via `risSpan_eq_encode_length:610` | `decode_item_length` (`rlp.py:479`) | `domain-restricted` | bridged |
| `rlp_item_span` | — (`RlpItemSpanSpec.lean` is cursor algebra + `CodeReq` plumbing only) | **no machine triple** | `itemOffset_*`, `encodeItems_drop_itemOffset:102` | `decode_item_length` | `n/a — unproven` | — |
| `rlp_list_count_items` | `rlp_list_count_items_spec_within` — `Codegen/Programs/RlpListCountItemsSAsm.lean:131` | proven | local predicates only | `decode_joined_encodings` (`rlp.py:456`) | `match` | machine-only |
| `rlp_list_nth_item` | `rlpListNthItem_spec_within` — `Codegen/Programs/RlpListNthItemSAsm.lean:733` | proven (success/reject/OOB) | `rlpItemDecode` + `EL.RLP` refs | `decode_to_sequence` + index | `match` | bridged |
| `rlp_field_to_u64` | `rlpFieldToU64_spec_within` — `Codegen/Programs/RlpFieldToU64WholeSAsm.lean:181` | proven | `rlpItemDecode` + `EL.RLP` refs | `_deserialize_to_uint` at **`U64`** ∘ walk | `match` (U64 fields only — see §4c) | bridged (walk) + insp (scalar) |
| `rlp_field_to_u256_be` | `rlpFieldToU256Be_spec_within` — `Codegen/Programs/RlpFieldToU256BeWholeSAsm.lean:166` | proven | as above | `_deserialize_to_uint` at **`U256`** ∘ walk | `match` (U256 fields only — see §4c) | bridged (walk) + insp (scalar) |
| `rlp_bytes_encoded_size` | `rlpBytesEncodedSize_spec` — `Codegen/Programs/RlpBytesEncodedSizeSAsm.lean:539` | proven | `rbesSize` (`:89`) — standalone arithmetic | `len(encode_bytes(...))` (`rlp.py:92`) | `match` | machine-only |
| `rlp_list_encoded_size` | `rlpListEncodedSize_spec` — `Codegen/Programs/RlpListEncodedSizeSAsm.lean:364` | proven | standalone arithmetic | `len(encode_sequence(...))` (`rlp.py:112`) | `match` | machine-only |
| `rlp_encode_uint_be` | — (model layer complete: `reubOut_eq_encode_toBytesBE:205`, `reubOut_short_form:251`; **no whole-routine triple**) | **partly** — 33/35 instrs on PR #10943; documented `≤ 55` domain | `reubOut`, tied to `encode ∘ toBytesBE` | `encode(Uint)` → `encode_bytes(to_be_bytes())` — **unbounded** | `domain-restricted` | insp |
| `rlp_encode_list_prefix` | `…_short_pinned_spec_within:762`, `…_long1_pinned_spec_within:917` — `RlpSpliceHelperSpec.lean` | **partly** — no unified dispatch theorem; `lenlen ≥ 2` (payload ≥ 256 B) uncovered | `EL.RLP` refs | header of `encode_sequence` (`rlp.py:112`) | `domain-restricted` | bridged |
| `rlp_encode_bytes` | — | **unproven** (drift guard only: `RlpRead.lean:634`) | — | `encode_bytes` (`rlp.py:92`) | `n/a — unproven` | — |
| `rlp_encode_u64` | — | **unproven** (drift guard `Receipt.lean:114`) | — | `encode(U64)` | `n/a — unproven` | — |
| `rlp_list_truncate_to_n_fields` | — | **unproven** (drift guard `TxSigningHash.lean:185`) | — | none — signing-hash truncation is guest-specific | `no-counterpart` | insp |
| `rlp_prefix_to_buffer` | — | **unproven**; *no drift guard either* (`MptIndexedTrieRoot.lean:137`, MULTI-ENTRY-BUNDLE) | — | header emission, no standalone counterpart | `no-counterpart` | insp |

**Counts:** 18 routines — 10 fully proven, 4 partly, 4 unproven.
Verdicts: 8 `match`, 3 `domain-restricted`, 3 `n/a — unproven`, 2 `no-counterpart`.
**Zero `looser`. Zero `stricter`.**

### 4b. Adjacent RLP-consuming routines

Not `rlp_*`-prefixed, but they decode/encode RLP and belong in the audit.

| Guest routine | Spec | Status | Verdict |
|---|---|---|---|
| `withdrawal_decode` | `withdrawal_decode_spec_within` — `Codegen/Programs/WithdrawalDecodeClose5.lean:1157` | proven (60 instrs; `a0=0` Decoded / `a0=1` witnessed DecodeFailure) | `match` (machine-only) |
| `block_header_ssz_to_rlp` | only helper `bhr_rev_le_be` (`BhrRevLeBeSAsm.lean:46`); the 23-field re-encoder unproven | partly | `n/a — unproven` |
| `ssz_withdrawal_to_rlp` | only helper `swr_rev_le_be` (`SwrRevLeBeSAsm.lean:260`) | partly | `n/a — unproven` |
| `block_rlp_rebuilt_size` | — | unproven | `n/a — unproven` |
| `validate_header_rlp_pair` | — | unproven | `n/a — unproven` |
| `log_records_encode_rlp` | — | unproven (0 theorems in file) | `n/a — unproven` |
| `bal_rlp_*` (9 symbols, `BalRlpEncode.lean`) | — | unproven (0 theorems in file) | `n/a — unproven` |

> **Do not double-count `withdrawal_decode`.** Two independent proof efforts
> exist and do not reference each other: the *deployed* one above, over the real
> 60-instruction `withdrawalDecode_prog`; and a schema-driven **WP facade**
> (`Rv64/RLP/WithdrawalDecode*.lean`, `WithdrawalSchemaWP.lean:247`) with no
> concrete program. Only the first discharges the guest obligation.

### 4c. Number strictness varies by field type

> Raised by @pirapira on #10949: *"different places in execution-specs have
> different strictness requirements about numbers."* Confirmed, and it changes
> how the scalar rows must be read.

Integers are **not** validated by the RLP codec. `rlp.decode` treats an
integer-shaped payload as an ordinary byte string and accepts it — the corpus
pins this: `820001` (leading-zero content), `89·ff×9` (9 bytes) and `a1·ff×33`
(33 bytes) are all `accept` at the decode layer. The integer rules live one
layer up, in `_deserialize_to_uint` (`rlp.py:265`), which applies:

1. **leading-zero rejection** — `decoded[0] == 0` ⇒ `DecodingError("non-canonical
   integer")`. **Uniform across every field type.**
2. **width rejection** — via `class_.from_be_bytes`, and this is where the
   strictness **differs**, because the target type is chosen per field:

| Target | Width cap | Example fields (`forks/amsterdam/blocks.py`) |
|---|---|---|
| `Uint` | **none** — arbitrary precision | `difficulty:152`, `number:157`, `gas_limit:162`, `gas_used:178`, `base_fee_per_gas:203`, `cumulative_gas_used:373` |
| `U64` | 8 bytes | `blob_gas_used:218`, `excess_blob_gas:226`, `slot_number:263`, `Withdrawal.index:46`, `Withdrawal.validator_index:52` |
| `U256` | 32 bytes | `timestamp:183`, `Withdrawal.amount:62` |

So `rlp_content_to_u64` — which returns status 2 on `len > 8` — corresponds
**exactly** to `_deserialize_to_uint` at `U64`, and is **stricter than the
reference** if applied to a `Uint` field, where a 9-byte value is legitimate.
That is a per-call-site obligation, not a property of the routine: the routine
is correct, and the caller must have picked the right one for the field's type.

**Consequences for this table.** The differential does not reach the typed
layer, so the scalar rows are `insp`, not `diff`/`bridged` — an earlier revision
of this page overstated them. Two follow-ups in [§8](#8-follow-ups-filed): a typed-layer
oracle covering all three widths, and an audit that every guest call site pairs
the field's actual Python type with the matching routine (a `Uint` field decoded
with a `_to_u64` routine is a latent false-reject).

## 5. The inheritance gap

The `machine-only` rows are the substantive finding of this pilot.

All 15 RLP spec modules *transitively import* `EvmAsm.EL.RLP`, so the shared
model is available to them. But availability is not use: several state their
postconditions over **locally defined predicates that re-derive the RLP rules
from raw bytes**, rather than over `EL.RLP.encode`/`decode`. Two examples:

- `rlpItemDecode` (`Rv64/RLP/WalkNext.lean:3649`) restates the prefix cases as
  `BitVec` comparisons against `0x80`/`0xb8`/`0xc0`/`0xf8`, including the
  canonicality side conditions, inline in the statement.
- `rbesSize` (`RlpBytesEncodedSizeSAsm.lean:89`) is standalone arithmetic over
  `len`, not `(encode …).length`.

Where a bridge lemma exists and is cited — `risSpan_eq_encode_length:610` for
`rlp_item_size`, `Rv64/RLP/WalkDecodeBridge.lean` for the walk family — the
§3 differential result transfers. Where it does not, **a divergence between the
machine predicate and `EL.RLP` would be invisible to both the differential and
the existing proofs**: the proof would still be valid, about the wrong property.
Five rows sit there today (`rlp_content_to_u256_be`, `rlp_list_count_items`,
`rlp_bytes_encoded_size`, `rlp_list_encoded_size`, `withdrawal_decode`).

Closing this means, per routine, a lemma of the shape
`<machine predicate> ↔ <EL.RLP statement>`. That is follow-up work, not part of
this pilot; see [§8](#8-follow-ups-filed).

## 6. SSZ routines

**No executable differential** — the generic SSZ codec is `remerkleable`, an
external package, and the guest tower was built independently of
`SpecRef/SszCodec.lean`. All verdicts here are `insp`.

The headline result is a coverage fact, not a divergence: **of 17 `ssz_*`
symbols, 6 have specs and all six are leaves. The entire merkleization tower is
emitted, `Program`-converted, drift-guarded — and completely unspecified.**

| Guest routine | Spec | Status | Model / SpecRef | Reference | Verdict |
|---|---|---|---|---|---|
| `ssz_pack_bytes` | `sszPackBytesFn_spec` — `Codegen/Programs/SszPackBytesSAsm.lean:535` | proven (`Fn.Spec`/vcgen, not `cpsTripleWithin`; header calls it a "port scaffold") | `SszCodec.packBytes:263` | `remerkleable` chunk packing | `match` |
| `eph_u32le` | `ephU32leFn_spec` — `Codegen/Programs/EphU32leSAsm.lean:34` | proven | offset read | SSZ offset (`uint32` LE) | `match` |
| `spw_u32le` | `spwU32leFn_spec` — `Codegen/Programs/SszPayloadWithdrawalsSAsm.lean:32` | proven | offset read | as above | `match` |
| `sws_u32le` | `swsU32leFn_spec` — `Codegen/Programs/SszWitnessStateSAsm.lean:32` | proven | offset read | as above | `match` |
| `read_chain_id` | `readChainIdFn_spec` — `Stateless/SSZ/Decode/ChainIdSAsm.lean:149` | proven | `SpecRef/Ssz.lean` `sszChainConfigType` | `stateless_ssz.py` `SszChainConfig` | `match` |
| `read_active_fork` | `readActiveForkFn_spec` — `Stateless/SSZ/Decode/ActiveForkSAsm.lean:73` | proven | `sszForkConfigType` | `stateless_ssz.py` `SszForkConfig` | `match` |
| `ssz_merkleize` | — | **unproven** | `SszCodec.merkleize:306` | consensus-specs merkleization | `n/a — unproven` |
| `ssz_merkleize_pow2` | — | **unproven** | `SszCodec.merkleizeReduce:287` | as above | `n/a — unproven` |
| `ssz_merkleize_padded` / `_partial` / `_scratch` | — | **unproven** | `SszCodec.liftToDepth:296` | as above | `n/a — unproven` |
| `ssz_hash_tree_root_bytes` | — | **unproven** | `SszValue.hashTreeRoot:341` | `.hash_tree_root()` | `n/a — unproven` |
| `ssz_hash_tree_root_list_bytelist` | — | **unproven** | as above + `mixInLength:317` | as above | `n/a — unproven` |
| `ssz_hb_chunks` / `_mix` / `_partial` | — | **unproven** | `packBytes` / `mixInLength` | as above | `n/a — unproven` |
| `ssz_ltb_child_roots` / `_mix` / `_partial` | — | **unproven** | as above | as above | `n/a — unproven` |
| `ssz_htr_withdrawals` | — | **unproven** (also UNCONVERTED) | `sszWithdrawalType:74` | `_withdrawal_to_ssz:242` | `n/a — unproven` |
| `ssz_htr_execution_requests` | — | **unproven** (also UNCONVERTED) | `sszExecutionRequestsType` | `_execution_requests_to_ssz:392` | `n/a — unproven` |
| `ssz_ew_field_roots` | — | **unproven** | `sszExecutionWitnessType` | `_witness_to_ssz:452` | `n/a — unproven` |
| `ssz_zero_hashes` | — | **unproven** | `SszCodec.zeroHash:269` | zero-hash table | `n/a — unproven` |
| `ssz_tx_list_versioned_hashes_match` | — | **unproven** | — | blob versioned-hash check | `n/a — unproven` |
| `ssz_withdrawal_to_rlp` | helper only (`swrRevLeBeFn_spec`) | **partly** | — | `_withdrawal_to_ssz` + RLP | `n/a — unproven` |

**Counts:** 6 proven leaves, 11 unproven, plus `ssz_withdrawal_to_rlp` partly.

`EvmAsm/Stateless/SSZ/HashTreeRoot/` — 8 files, 1791 lines — contains **zero
theorems**: `def`s and design docstrings only.

## 7. How to reproduce

```bash
# 0. The submodule must be at the gitlink rev, not whatever is lying around.
git submodule update --init execution-specs
git -C execution-specs describe --tags        # expect tests-zkevm@v0.6.2

# 1. Install the pinned reference (external package; not vendored).
uv pip install --target /tmp/rlp ethereum-rlp==0.1.6 eth-remerkleable==0.1.29

# 2. Regenerate the oracle corpus (must be byte-identical to the committed file).
PYTHONPATH=/tmp/rlp scripts/rlp-python-oracle.py --out tests/rlp-vectors/python-oracle.tsv
PYTHONPATH=/tmp/rlp scripts/rlp-python-oracle.py --check tests/rlp-vectors/python-oracle.tsv

# 3. Replay it against EvmAsm.EL.RLP. The self-test must pass first.
lake exe rlp-oracle-check --self-test
lake exe rlp-oracle-check
```

### Staleness guard

A committed corpus can silently keep describing a reference the repo no longer
uses — every leg would keep passing while measuring the wrong thing, which is
this page's own failure mode one level up (raised by @pirapira on #10949). Two
halves close it:

- **Generation refuses to produce a wrong-version corpus.** `rlp-python-oracle.py`
  reads `ethereum-rlp`'s pin out of `execution-specs/uv.lock` and exits non-zero
  unless the *installed* version matches it.
- **Replay detects the pin moving underneath the corpus.** The generator stamps
  `# oracle-version:` and `# execution-specs: <gitlink SHA>` into the header;
  `rlp-oracle-check` re-reads the gitlink from the superproject tree and fails
  if it has moved. The gitlink is readable **without the submodule checked
  out** — which is the situation in CI — and since the `ethereum-rlp` pin lives
  in that submodule's `uv.lock`, any change to it necessarily moves the SHA.

Both are covered by `--self-test`, which plants a moved SHA and a missing stamp
and requires each to be caught while a current corpus is not flagged.

The Lean checker imports only `EvmAsm.EL.RLP.FullDecode` (transitive closure:
`Decode`, `Basic` — no Mathlib), so it builds in seconds; CI runs it on the
committed TSV and never needs Python. The self-test plants one finding of each
class (stricter / looser / value / encode) and fails unless all four are
detected — a gate that cannot demonstrate catching a violation is itself
unaudited.

## 8. Follow-ups filed

Divergences: **none found.** The follow-ups are coverage and hygiene:

1. **Inheritance bridges** for the five `machine-only` rows ([§5](#5-the-inheritance-gap)).
1b. **Typed-layer oracle** covering `_deserialize_to_uint` at `Uint`/`U64`/`U256`,
   so the scalar rows move from `insp` to `diff` ([§4c](#4c-number-strictness-varies-by-field-type)).
1c. **Call-site type audit**: every guest site that decodes a header/withdrawal
   field must pair the field's Python type with the matching routine; a `Uint`
   field decoded by a `_to_u64` routine is a latent false-reject ([§4c](#4c-number-strictness-varies-by-field-type)).
2. **SSZ merkleization tower** — 11 unspecified routines ([§6](#6-ssz-routines)).
3. `rlp_prefix_to_buffer` has **no drift guard**, unlike every other emitted
   RLP routine — the string↔`Program` tie is missing entirely.
4. Stale docstring `Codegen/Programs/RlpSpliceHelperSpec.lean:25,38` names
   `rlp_item_size_form_spec_within` and `rlp_encode_list_prefix_spec_within`;
   neither exists (actual: `rlp_item_size_form_own_spec_within:637`, and there
   is no unified list-prefix dispatch theorem).
5. `EvmAsm/Rv64/RLP.lean` header calls Phases 2/5/6 "planned"; Phase 2 has ~25
   proven modules and Phase 6 has `Phase6WriteOutput.lean:154`.
6. `docs/4ch8f-guest-image-coverage.md` addresses are stale vs `GuestAddrs.lean`
   (e.g. `rlp_item_size` `0x8000472c` vs `0x80004d34`); needs a
   `scripts/guest_image_coverage.py` regen.
7. `PROGRESS.md:123` still records the reference-link audit as "not yet
   machine-checked" though `scripts/check-spec-refs.sh` exists.
8. `EvmAsm/Tests/RlpDiffCheck.lean:26` references a nonexistent
   `scripts/rlp-check-all.sh`; and `rlp-diff-check` is still not built in CI.
9. SpecRef pin disagreement: `SpecRef.lean:5` says v0.4.0,
   `docs/4ch8f-specref-port.md:4` says v0.5.0, `SpecRef/Ssz.lean:5` says v0.6.0
   — while the gitlink is v0.6.2.

## 9. Extending this beyond RLP/SSZ

The pilot's transferable parts: the verdict vocabulary ([§1](#1-verdict-vocabulary)), the
basis column (which is what keeps a table like this from becoming another
unaudited measurement), the generated-and-committed oracle pattern, and the
self-test discipline. The blocker to reuse is per-family: it only works where a
reference implementation can be *executed* against a Lean model. That holds
wherever a shared executable model like `EvmAsm.EL.RLP` exists; it does not hold
where the guest tower was built independently of SpecRef — which is exactly the
SSZ situation, and the reason SSZ verdicts here are prose.
