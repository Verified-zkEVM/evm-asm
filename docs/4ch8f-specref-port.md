# SpecRef — Lean functional port of the stateless-guest spec (`4ch8f.8` feeder)

A faithful, executable Lean reference model of the Amsterdam stateless-guest
Python spec, ported line-for-line against
`execution-specs @ tests-zkevm@v0.5.0` (the project's canonical conformance
target). This is a **reference model only** — no proofs, no theorems about the
RV64 guest. It is the scaffolding bead `evm-asm-4ch8f.8` (the top-level spec
*statement*) can consume regardless of the trust-boundary / one-sided-vs-two-sided
decisions that bead makes.

Code lives under `EvmAsm/Stateless/SpecRef/`, imported via
`EvmAsm/Stateless/SpecRef.lean` (wired into the `EvmAsm.Stateless` umbrella).

## Reading the source on the right ref

The spec does **not** live on execution-specs master or `origin/forks/amsterdam`.
It is on the `tests-zkevm@v0.5.0` tag (checked out as the in-repo `execution-specs`
submodule). Read files with:

```
git -C execution-specs show 'bd8c673:src/ethereum/forks/amsterdam/<file>'
```

## Modeling choices

| Concept | Model | Rationale |
|---|---|---|
| `Bytes` | `List (BitVec 8)` (= `EvmAsm.EL.RLP.Byte`) | `#eval`/`decide`-friendly; lets us reuse the repo's RLP model verbatim |
| `U64`/`U256`/`Uint` | `Nat` | width is an SSZ-codec property, not a Lean type; matches how `remerkleable` applies width only at (de)serialization |
| `Hash32`/`Root`/`Address`/`Bloom`/`VersionedHash` | raw `Bytes` | mirrors `bytes(x)` in the Python conversions; length is a codec invariant, checked on decode |
| Python `raise` | `Except SpecError α` / `Option α` | distinct reasons kept in the `SpecError` enum, not collapsed |
| structural recursion the kernel can't see | explicit fuel arg | repo convention (`powModAux`); fuel bounds *type-nesting depth*, so a small constant suffices and terms stay kernel-reducible |

## Reused vs ported

**Reused** (no re-implementation):

- `EvmAsm.Rv64.Accel.keccakF`, `Accel.sha256Compress` — the concrete ZisK
  permutations (KAT-checked in-repo). `SpecRef.Crypto` wraps them with the
  sponge / Merkle–Damgård padding to get full `keccak256`/`sha256`.
- `EvmAsm.EL.RLP` — the full functional RLP model: `RLPItem`, `decode`,
  `decodeFully`, `encode`, `Nat.toBytesBE`, `Nat.fromBytesBE`. Used by
  `_decode_header` and `_decode_account_from_leaf`.

**Ported fresh** (nothing functional existed in-repo — only SAsm emitters and
doc-only contracts under `EvmAsm/Stateless/SSZ/`):

- The generic SSZ engine (`SszCodec`): `serialize` (`encode_bytes`),
  `deserialize` (`decode_bytes`), `hashTreeRoot` (merkleization with
  `mix_in_length`, packed basic-type lists, `Z_0` padding).
- The domain types, the SSZ containers + 34 conversions, the 4 witness-state
  defs, the 7 stateless defs, and the 3 guest-shell defs.

## The execution seam

`verify_stateless_new_payload` (`stateless.py:368`) calls
`execute_new_payload_request` (`stateless.py:402`) — full stateful block
re-execution (`execution_engine.new_payload`, the whole EVM). We cut **exactly**
at that call:

- Everything on the validation / deserialization / hashing side is **real**:
  NPR-root hashing, chain-config validation, header decode + contiguity, node/code
  DB construction, the witness pre-state assembly.
- The engine is an explicit parameter `execute : ExecutionSeam`, i.e.
  `ExecutionSeamInput → Except SpecError Unit`, where `ExecutionSeamInput`
  carries the exact bundle the Python call passes: the `NewPayloadRequest`, the
  witness-backed `WitnessPreState` (`_node_db` / `_state_root` / `_code_db`), the
  `ChainContext` (`chain_id` / `block_hashes` / `parent_header`), and the
  transaction public keys.
- `ok ()` ≙ Python returning normally; `error _` ≙ any raised exception (folded
  into `successful_validation = false`, as the Python `try/except Exception`
  does).
- `executeAlwaysOk` is a placeholder instantiation so the shell is
  `#eval`-runnable end-to-end. The v0.5.0 work extends this only along the
  concrete call graph reached by `run_stateless_guest`; SpecRef is not a
  general-purpose EVM port.

`WitnessState`'s read/write methods (`get_account_optional`, `get_storage`,
`get_code`, `compute_state_root_and_trie_changes`) and `decode_witness_to_mpt`
are behind this seam and are **not** ported (they are the `PreState` protocol
consumed by execution, plus `incremental_mpt.py`).

## Python ↔ Lean mapping

All line numbers are `@tests-zkevm@v0.5.0` (`bd8c673`). Lean names are in
`namespace EvmAsm.Stateless.SpecRef`.

### `stateless_guest.py` → `Guest.lean`

| Python (line) | Lean |
|---|---|
| `serialize_stateless_output` (28) | `serialize_stateless_output` |
| `deserialize_stateless_input` (36) | `deserialize_stateless_input` |
| `_default_failed_stateless_output` (54) | `_default_failed_stateless_output` |
| `run_stateless_guest` (75) | `run_stateless_guest` |

### `stateless.py` → `Stateless.lean` (+ types in `Types.lean`)

| Python (line) | Lean |
|---|---|
| `ExecutionWitness` (35) | `ExecutionWitness` (Types) |
| `ProtocolFork` (86) | `ProtocolFork` + `protocolForks` (Types) |
| `ForkActivation`/`BlobSchedule`/`ForkConfig`/`ChainConfig` (141–179) | same names (Types) |
| `StatelessInput` (191) / `StatelessValidationResult` (223) | same names (Types) |
| `compute_new_payload_request_root` (255) | `compute_new_payload_request_root` |
| `_decode_header` (270) | `_decode_header` (+ `mkHeader`, `rlpBytes?`) |
| `validate_headers` (281) | `validate_headers` |
| `_is_activation_active` (304) | `_is_activation_active` |
| `_expected_amsterdam_blob_schedule` (329) | `_expected_amsterdam_blob_schedule` |
| `validate_chain_config` (340) | `validate_chain_config` |
| `verify_stateless_new_payload` (368) | `verify_stateless_new_payload` |

The `Header`/`PreviousForkHeader` union is collapsed into one `Header` record
with an `isCurrentFork` tag (see simplifications below).

### `stateless_ssz.py` → `Ssz.lean` (engine in `SszCodec.lean`)

Constants `MAX_*` (46–85), `STATELESS_INPUT_SCHEMA_ID{,_SIZE}` (88–89) ported
verbatim. Each `class SszX(Container)` → `sszXType : SszType`. Each `_x_to_ssz` →
`xToSsz`, each `_ssz_to_x` → `sszToX` (34 conversions total):
`_protocol_fork_to_ssz`/`_ssz_to_protocol_fork`, `_withdrawal_*`, `_payload_*`,
`_deposit_request_*`, `_withdrawal_request_*`, `_consolidation_request_*`,
`_execution_requests_*`, `_new_payload_request_*`, `_witness_*`,
`_optional_u64_*`, `_fork_activation_*`, `_blob_schedule_*`,
`_optional_blob_schedule_*`, `_fork_config_*`, `_chain_config_*`,
`stateless_input_to_ssz`/`ssz_to_stateless_input`,
`validation_result_to_ssz`/`ssz_to_validation_result`. The generic
`.encode_bytes()`/`.decode_bytes()`/`.hash_tree_root()` (from `remerkleable`) are
`SszValue.serialize` / `deserialize` / `SszValue.hashTreeRoot`.

### `witness_state.py` → `WitnessState.lean`

| Python (line) | Lean |
|---|---|
| `build_node_db` (36) | `build_node_db` |
| `build_code_db` (44) | `build_code_db` |
| `_trie_lookup` (52) | `trieLookup` (+ `trieLookupAux`, `keyToNibbles`) |
| `_decode_account_from_leaf` (102) | `decode_account_from_leaf` |

`MutableNode` (from `incremental_mpt`) is modeled as an inductive with
`hashed`/`leaf`/`extension`/`branch`.

## Sanity evidence (`#guard`, kernel-evaluated)

- **Crypto** (`Crypto.lean`): `keccak256`/`sha256` KATs for `""`, `"abc"`.
- **SSZ** (`Ssz.lean`): `ChainConfig` (optionals + nested container) and
  `StatelessValidationResult` (bool + nested) round-trip serialize→deserialize→domain.
- **Witness** (`WitnessState.lean`): `EMPTY_CODE_HASH`/`EMPTY_TRIE_ROOT` match the
  spec's constants; `build_node_db` keys; `trieLookup` on leaf/extension/branch,
  empty-root, and the `HashedNode` error; `decode_account_from_leaf` on a full and
  an all-empty leaf.
- **Stateless** (`Stateless.lean`): `_decode_header` for amsterdam (23) vs previous
  (21) fork and a bad field count; `validate_headers` contiguity accept/reject;
  `_is_activation_active` active + missing-both.
- **Guest** (`Guest.lean`): end-to-end schema-prefixed
  `StatelessInput` round-trip, wrong-schema and too-short rejection, and a full
  `run_stateless_guest` run whose decoded output carries `successful_validation =
  true` and the matching NPR root (under the placeholder seam), plus the v0.5.0
  malformed-input sentinel output.

## Known simplifications / spec ambiguities

1. **Header decode discriminant.** `rlp.decode_to(Header, …)` is type-directed and
   validates each field's byte length; we discriminate current fork (amsterdam, 23
   RLP fields) from previous fork (bpo5, 21 fields) by RLP list length only, and do
   not re-impose per-field length checks. The two forks have distinct field counts,
   so this reproduces the fork-selection behavior; it is slightly more permissive on
   malformed field widths. Not observed to matter for the spec's downstream use
   (`parent_hash`, `state_root`).
2. **`Header | PreviousForkHeader` union** collapsed into one `Header` record with an
   `isCurrentFork` tag; the two amsterdam-only fields default to `[]`/`0` for the
   previous fork. Downstream only reads `parent_hash`/`state_root`.
3. **Node DB as association list.** `Dict[bytes, bytes]` is modeled as
   `List (Hash32 × Bytes)` in witness order (last-write-wins dict semantics are moot
   — colliding keys carry identical values). Lookups are behind the seam, so this is
   inert here.

## Divergence policy

No disagreement between the Python spec and the emitted guest / existing Lean was
found while porting (the port is a fresh functional model, disjoint from the SAsm
side). If a future audit surfaces one, file a P1 bead per standing project policy.

## EEST conformance harness

`scripts/eest-specref-check.sh` ties SpecRef to the *same* EEST `zkevm@v0.5.0`
conformance fixtures exercised by `scripts/codegen-eest-stateless-check.sh`,
so regressions in the port's SSZ codec / NPR-root hashing / header /
chain-config / witness-assembly path surface without spinning up ziskemu.

- **Driver**: `lake exe specref-eest-check <input_file> <output_file>`
  (`MainSpecRefEestCheck.lean` → `EvmAsm.Tests.SpecRefEestCheck`). It reads a
  ziskemu-framed input, strips the host transport (inverse of
  `pack_ziskemu_input`), runs `SpecRef.run_stateless_guest` (default seam:
  the full `elExecute`, `s1d19.5`), and writes the 105-byte
  `StatelessValidationResult`.
  It lives under `EvmAsm/Tests/` (the unverified escape-hatch layer); no proof
  imports it.
- **Fixture selection** is identical to the ziskemu harness
  (`--all/--skip/--limit/--filter/--random/--seed/--reverse/--tag`), reusing
  `scripts/eest-stateless-to-input.py`, so the two report on the same rows.

### The three-region verdict

The 105-byte `SszStatelessValidationResult` decomposes into three
independently-checkable regions.  Since `s1d19.5` the execution seam is the
full ported `elExecute` (`PrecompilesTable.lean`), so ALL THREE regions are
expected to match:

| region | bytes | meaning | gateable? |
|---|---|---|---|
| `root` | 0:32 | `new_payload_request_root` (pre-execution hashing) | yes — `--min-root` |
| `succ` | 32 | `successful_validation` | yes — `--min-succ`; un-allowlisted divergence fails the run |
| `tail` | 33:105 | u32 offset + 68-byte chain-config echo | yes — `--min-tail` |
| `full` | all 105 | exact guest output | informational |

A per-case line shows which regions matched; `[----/----/----]` means the
pre-execution path itself disagreed with the fixture — a real SpecRef bug worth
a P1 bead.  A succ divergence is a FAILURE unless the fixture is listed in
`scripts/eest-succ-allow.txt` (fixture-vs-pinned-spec inconsistencies with
recorded evidence; burndown discipline — the goal is an empty file).  The
`--min-succ` gate exists since the seam became real (`s1d19`, closing the
`4ch8f.8` placeholder era).
