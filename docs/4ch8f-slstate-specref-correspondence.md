# SL-state Assertions ↔ SpecRef structures: the correspondence map

*Session 2026-07-05. Design doc — no new proofs. This lays out, for every
separation-logic state Assertion (PRs #9844/#9846/#9847/#9849/#9850 + the
call-frame phase model), which abstract structure it corresponds to and via
what abstraction function, so the eventual guest-correctness refinement
("concrete RISC-V memory ⊑ abstract spec state") has a named target for each
component. Proven ties are cited; missing ones are sketched with signatures;
gaps are listed at the end in both directions.*

## 0. How to read this, and the layering fact that shapes everything

Notation: for each Assertion `X ptr args` we give an **abstraction function**
`α_X : args → A` mapping the assertion's *logical parameters* (the byte
lists / records the assertion carries) to an abstract value of type `A`.
Because every Assertion in this vocabulary is value-carrying
(`bytesRegion`-shaped with the contents as a parameter, plus a pure WF
conjunct — the `SepLogic.assertPure` pattern), the abstraction never needs to
read the heap: `X ptr args ps` already pins the bytes at `ptr` to `args`, so
"the heap corresponds to abstract value `v`" is simply
`X ptr args ps ∧ α_X args = v`. This is deliberate and is what makes the
refinement statement compositional over `**`.

**The layering fact**: `SpecRef` models `run_stateless_guest` only **down to
the execution seam**. `verify_stateless_new_payload`
(`SpecRef/Stateless.lean:177`) builds `WitnessPreState` (node DB, state root,
code DB) and `ChainContext`, then calls an abstract
`ExecutionSeam : ExecutionSeamInput → Except SpecError Unit`
(`Stateless.lean:166`), whose only current instance is the placeholder
`executeAlwaysOk`. **SpecRef has no EVM memory, no operand stack, no message
frames, no storage map** — everything below the seam is future work (the `.8`
engine port). The correspondence is therefore *two-tier*:

- **Tier 1 (above the seam — SpecRef exists today)**: witness sections, code
  DB, node DB, MPT nodes, accounts. These have SpecRef counterparts and
  (mostly proven) abstraction functions now.
- **Tier 2 (below the seam — SpecRef counterpart TBD)**: EVM memory, storage
  logs, call frames. Their *nearest existing* abstract layer is the Evm64/EL
  executable-spec side (`Evm64.EvmState` + `evmStateIs`
  (`Evm64/EvmState.lean`), `EL.WorldState` (`EL/WorldState.lean`),
  `Evm64.StorageAccess`), which the interpreter-loop bridges already consume.
  When the `.8` engine port lands in SpecRef, these correspondences re-target
  it; the abstraction functions sketched below are written so that re-target
  is a renaming, not a redesign.

Summary table (details per section):

| SL Assertion (module) | Abstract counterpart | α status |
|---|---|---|
| `witnessSectionIs` (WitnessAssertions) | `SpecRef.ExecutionWitness.{state,codes,headers}` | **proven-adjacent** (`#guard` vs `SszValue.serialize`; α = `sszSectionElements`) |
| `codeDbIs` / `witnessIndexIs` (WitnessAssertions) | `WitnessPreState.codeDb` = `build_code_db` | **proven** (`indexOfSection_hashes_eq_build_code_db`, `witnessLookupSpec_correct`) |
| `nodeDbIs` (MptAssertions) | `WitnessPreState.nodeDb` = `build_node_db` | **proven** (`nodeDbLookupSpec_eq_build_node_db`) |
| `mptNodeIs` (MptAssertions) | `SpecRef.MutableNode` / `trieLookup` | **sketched** (`αnode`; kind/path/projection lemmas proven) |
| `accountRlpIs` / `accountDecodedIs` (AccountAssertions) | `SpecRef.Account` (+ `storageRoot`) | **proven** (`decode_account_from_leaf_accountRlp`, `bytesBEtoNat_beBytes32`) |
| `evmMemoryIs` (StateAssertions) | Tier 2: `EvmState.memory/memSize`; SpecRef: none | **sketched** (`αmem`; read side proven vs MLOAD via `evmMemoryReadWord`) |
| `storageSlotIs`/`storageLogIs` (StorageAssertions) plus the Codegen `storage_writes` map | Tier 2: `WorldState.storage` (map); SpecRef: none | **sketched** (`αlog` = last-write-wins replay; canonical block rows carry the flat key/value map, §7) |
| `callFrameIs`/phase model (Codegen/CallFrame*) | none (implementation scaffolding below the refinement) | n/a (§8) |
| `evmStackIs` (Stack.lean, pre-existing) | `EvmState.stack : List EvmWord` | **in use** (already consumed by `evmStateIs` and every opcode triple) |

---

## 1. `witnessSectionIs` → `ExecutionWitness`

**Counterpart.** `SpecRef.ExecutionWitness` (`Types.lean:197`):
`{ state, codes, headers : List Bytes }` — the three SSZ `List[ByteList]`
fields of `StatelessInput.witness`.

**Abstraction function.**
`α_section : List (BitVec 8) → List Bytes := sszSectionElements`
(`WitnessAssertions.lean`) — the section's element list, extracted by the
same LE-u32 offsets arithmetic the guest routines perform. The full witness
abstraction is the triple of the three section views:

```
α_witness (stateBs codesBs headersBs : List Byte) : ExecutionWitness :=
  { state   := sszSectionElements stateBs
    codes   := sszSectionElements codesBs
    headers := sszSectionElements headersBs }
```

**Proven today**: the concrete `#guard` pipeline pins `sszSectionElements` to
the spec-level SSZ serializer (`SszValue.serialize (.list _ none
[.byteList ..])` = the hand-built section, elements recovered exactly). The
*general* inverse statement — for all WF sections,
`sszSectionElements (serialize (witnessToSsz w)).state-field = w.state` — is
**not proven**; it is the natural first lemma of the input-decode refinement
(ingredients: `SszCodec` serialize + `sszSectionWF`; `sszToWitness`
(`Ssz.lean:306`) is the codec-level counterpart to state it against).

**Alignment / divergence.** Structurally aligned (same offsets-table wire
format). Divergences the refinement must carry: (a) SpecRef holds the three
lists as *values*; the guest holds one blob with three `(ptr, len)` views
computed from `SSZ_BASE = INPUT + 18` — the correspondence needs the
section-extraction arithmetic (`extract_witness_state_section`) proven
against the SSZ outer-offsets table, which has no spec tie yet; (b)
`sszSectionWF` (monotone, bounded offsets) is *assumed* by the guest index
builder but is a *consequence* of well-formed serialization on the SpecRef
side — the refinement gets it for free on honest inputs but the guest's
conservative-failure path on malformed tables must map to the SpecRef decode
error path.

## 2. `codeDbIs` / `witnessIndexIs` → `WitnessPreState.codeDb`

**Counterpart.** `WitnessPreState.codeDb : List (Hash32 × Bytes)` =
`build_code_db witness.codes` (`WitnessState.lean:56`,
`Stateless.lean:143/191`).

**Abstraction function.** Two equivalent routes, both already in the
vocabulary:

```
α_codeDb (sectionBytes : List Byte) : List (Hash32 × Bytes) :=
  build_code_db (sszSectionElements sectionBytes)
```

and, via the index the guest actually searches,
`indexOfSection sectionBytes` with each record abstracted to
`(r.hash, (sectionBytes.drop r.offset).take r.len)`.

**Proven today**:
- `indexOfSection_hashes_eq_build_code_db` — the index keys are exactly
  `(build_code_db (sszSectionElements bs)).map Prod.fst`, in element order.
- `witnessLookupSpec_correct` — a lookup hit returns a slice whose keccak IS
  the queried hash (given `matchesSection`, which
  `indexOfSection_matchesSection` establishes under `sszSectionWF`).

**Missing (sketch)**: the value-side equation
`witnessLookupSpec (indexOfSection bs) h = (build_code_db
(sszSectionElements bs)).lookup h` *as slices* — the hash side is proven;
the offset/len-to-element identification needs
`sszElement bs i = (bs.drop off_i).take len_i` unfolded through
`indexOfSection` (definitional, one lemma). Also: the guest *sorts* the index
(binary search); the correspondence should be stated against the unsorted
`indexOfSection` and a permutation fact for the heapsort (or against
`witnessLookupSpec` on the sorted list plus "sorted lookup = unsorted lookup
for distinct keys" — note **duplicate code hashes are possible** in a
malicious witness; `build_code_db`'s assoc-list `lookup` takes the *first*,
the guest's binary search takes *some* match — for duplicate keys with
different bodies the keccak tie still pins the body up to hash collision, so
the divergence is benign, but say so in the proof, don't discover it there).

**Alignment / divergence.** Log-free, map-shaped on both sides — the closest
correspondence in the whole map. Divergences: capacity (`2^17` index records
vs `MAX_WITNESS_CODES = 2^16` — codes fit; the *state* flavour vs
`MAX_WITNESS_NODES = 2^20` does **not** fit, and the guest falls back to the
uncapped linear scan — the correspondence must cover both lookup paths);
lookups return `(offset, len)` views, never copies.

## 3. `nodeDbIs` → `WitnessPreState.nodeDb`

**Counterpart.** `WitnessPreState.nodeDb : List (Hash32 × Bytes)` =
`build_node_db witness.state` (`WitnessState.lean:52`).

**Abstraction function.**

```
α_nodeDb (nodes : List (List Byte)) : List (Hash32 × Bytes) :=
  build_node_db nodes   -- = nodes.map (fun n => (keccak256 n, n))
```

**Proven today**: `nodeDbLookupSpec_eq_build_node_db` — the guest's
linear-scan lookup model equals assoc-list lookup in `build_node_db`.

**Alignment / divergence — the three-tier resolve.** The SpecRef pre-state
has ONE node source; the guest has THREE (`mpt_node_resolve` order): the
**appended DB** (`nodeDbIs` — re-encoded nodes produced by the MPT-*set*
write path, *not present in the witness*), the **resolve cache** (a
performance artifact: entries are copies of witness-lookup results, so it is
*abstraction-invisible* — its correspondence obligation is only the
invariant "every valid cache entry `(h, ptr, len)` satisfies
`keccak256 bytes[ptr..ptr+len) = h` and agrees with the witness lookup"),
and the **witness state section** (§1/§2 machinery, state flavour). So the
guest's effective node mapping is
`build_node_db appendedNodes ++ build_node_db (sszSectionElements stateBs)`
(appended DB consulted first). On the *read* path of an unmodified trie the
appended DB is empty and this collapses to SpecRef's `nodeDb`. On the *write*
path SpecRef has no counterpart yet (the engine seam); the appended DB's
abstract meaning is "the node set of the partially rebuilt post-state trie",
and its correspondence belongs to the `.48` state-root-recompute refinement,
not to the pre-state. Keep the two roles separate in the proof.

## 4. `mptNodeIs` → `MutableNode` / `trieLookup`

**Counterpart.** `SpecRef.MutableNode` (`WitnessState.lean:66`):
`hashed | leaf restOfKey value | extension keySegment child | branch
children value`, consumed by `trieLookup` (`WitnessState.lean:104`).

**Abstraction function (sketched — the main unproven α).**

```
-- One node, shallowly: hash refs stay symbolic.
α_node : MptNode → MutableNode
  | .leaf p v       => .leaf p v                    -- nibbles-as-bytes on both sides
  | .extension p _  => .extension p (.hashed [])    -- child ref abstracted to a hash node
  | .branch cs v    => .branch (cs.map fun c =>
                          if c = [] then none else some (.hashed c)) v
```

plus the **resolve closure** that turns hash refs into subtrees:

```
α_trie (db : List (Hash32 × Bytes)) (rootHash : Hash32) : Option MutableNode
-- decode db.lookup rootHash via a (to-be-written) rlpToMutableNode,
-- recursively resolving 32-byte child refs through db, fuel = depth ≤ 64.
```

**Proven today** (the per-node ingredients): `mptNodeKindSpec_rlp` (the
guest's discriminator classifies `MptNode.rlp` correctly),
`hpDecode_hpEncode` (compact-path nibbles round-trip — `MutableNode` keys are
nibble lists in exactly this decoded form), and
`decodeFully_{branch,leaf,extension}_rlp` (the RLP item projections).

**Missing (the load-bearing gap)**: there is **no spec-level
`rlpToMutableNode : Bytes → Except SpecError MutableNode`** — WitnessState
explicitly scoped `decode_witness_to_mpt` out. Until it exists, `trieLookup`
can only be run on hand-built trees (its `#guard`s) and there is no statement
"guest walk over RLP nodes = `trieLookup` over the decoded tree". Writing
`rlpToMutableNode` (one screen: `decodeFully` + `hpDecode` + the branch/2-item
dispatch — i.e. exactly `mptNodeKindSpec`'s skeleton, returning the node
instead of the tag) and proving `rlpToMutableNode (n.rlp) = .ok (α_node n)`
for WF `n` is the natural next PR; the existing kind/path lemmas ARE that
proof's three cases.

**Alignment / divergence.** (a) `trieLookupAux` *errors* on `.hashed`
(unresolved) — the guest instead resolves lazily via §3's three tiers; the
correspondence composes `α_trie` with the node DB rather than pre-materializing
the tree, and "guest miss = SpecRef `unresolvedHashedNode`" must be aligned.
(b) Inlined (`< 32`-byte) children: `mpt_branch_child` status 2 exists in the
guest; `MptNode` v1 models hash-or-empty refs only (documented) — the inlined
case must be added to both `MptNode` and `α_node` before tries with small
subtrees are in scope. (c) `MutableNode.branch` children are
`List (Option MutableNode)` (16 + value) vs the guest's flat 17-item RLP —
`α_node` handles the reshaping; empty-string ↔ `none`.

## 5. `accountRlpIs` / `accountDecodedIs` → `SpecRef.Account`

**Counterpart.** `SpecRef.Account` (`Types.lean:223`):
`{ nonce, balance, codeHash }`, with `storageRoot` returned separately by
`decode_account_from_leaf` (`WitnessState.lean:115`) — mirroring the Python
tuple return.

**Abstraction function (proven).**

```
α_account (a : AccountRecord) : Account × Root :=
  ({ nonce := a.nonce, balance := a.balance, codeHash := a.codeHash },
   a.storageRoot)
```

with the proven tie `decode_account_from_leaf_accountRlp : a.WF →
decode_account_from_leaf a.rlp = .ok (α_account a)` — i.e. the assertion's
contents parameter IS the decoded record, via the real spec decoder and the
proven RLP round-trip. For the *decoded-slot* view (`accountDecodedIs`, the
four `account_decode` output buffers): `bytesBEtoNat_beBytes32` proves the
balance slot reads back to `a.balance`; the nonce slot is a `↦ₘ` dword of
`BitVec.ofNat 64 a.nonce` (LE by construction); root/hash slots are the raw
32-byte fields.

**Alignment / divergence.** (a) empty-field sentinels: the decoder maps empty
RLP fields to `0` / `EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH`; `AccountRecord.WF`
pins hash fields to exactly 32 bytes, so the sentinel substitution only
happens for records *not* representable as WF `AccountRecord`s — the
refinement should state trie leaves as WF records post-substitution. (b) the
guest never materializes a struct (four caller-chosen slots) — already
captured by `accountDecodedIs`'s shape. (c) `SpecRef.Account` drops
`storageRoot`; the pair-return convention must be threaded consistently.

## 6. `evmMemoryIs` → (Tier 2) `EvmState.memory` — SpecRef: none

**Counterpart.** **SpecRef has no EVM memory** (below the seam) — OPEN
QUESTION resolved: confirmed absent; the Python counterpart
(`ethereum.vm.memory`, a zero-extended bytearray) arrives only with the `.8`
engine port. The existing abstract layer is `Evm64.EvmState`
(`EvmState.lean`): `memory : Nat → Word` (dword cells), `memSize : Nat`,
consumed by `evmStateIs` (whose memory conjunct is `evmMemIs layout.memBase state.memoryCells state.memory`) and the interpreter-loop bridges.

**Abstraction function (sketched).**

```
α_mem (contents : List Byte) : (Nat → Word) × Nat := fun _ =>
  (fun cell => dwordAt contents (8 * cell),   -- StateAssertions.dwordAt
   msize)                                     -- the logical size, tracked in env
```

The **read-side is effectively proven**: `evmMemoryReadWord contents k`
(big-endian 32-byte read with `getByteAt` zero-padding — the EVM read
semantics) is what the reframed MLOAD spec
(`evm_mload_stack_spec_within_evmMemoryIs`) proves the guest pushes. What's
missing is (a) the MSTORE side (contents-update fold: peel window → write →
fold back with the updated list — noted open since #9844), and (b) the
`memSize`/high-water correspondence (`Evm64/Memory.lean`'s `evmMemExpand`
algebra exists and is proven; it needs connecting to `evmMemoryIs`'s
zero-tail: "bytes at index ≥ msize are 0", i.e.
`∀ i ≥ msize, getByteAt contents i = 0` as the invariant linking logical size
to the full-capacity contents).

**Alignment / divergence.** (a) reserved capacity (16 MiB
`EVM_MEMORY_CAPACITY`, contents pinned to full length) vs abstract unbounded
zero-extended memory — bridged exactly by the zero-tail invariant above; (b)
**the anchor caveat**: `evmMemoryIs` is base-parametrized, and per the
call-frame audit the emitted dispatcher uses per-frame 128 KiB arenas (and a
global `evm_memory`), *not* the aspirational `EVM_MEMORY_AREA` — the
refinement must instantiate `base`/capacity per frame from
`CallFrameWindows.frameMemWindow`, and the 16 MiB-vs-128 KiB capacity
divergence (bead `.71` cluster) has to be resolved first; (c) endianness is
already internalized (`dwordAt` little-endian cells vs big-endian EVM words —
`evmMemoryReadWord` does the flip, proven).

## 7. `storageLogIs` / canonical `storage_writes` map → (Tier 2) `WorldState.storage` — **the log-vs-map crux**

**Counterpart.** **SpecRef has no storage state** (below the seam). The
map-shaped abstract layers that exist: `EL.WorldState.storage : Address →
StorageKey → Word256` (zero-default, `EL/WorldState.lean`) and the
access-list model `Evm64.StorageAccess` (gas warmth only). The Python
counterpart is the trie-backed `ethereum.state` storage.

**The mismatch, precisely.** The guest keeps an **append-only 128-byte-entry
log** (`storageLogIs`: `addrHash | slotKey | original | current`, SSTORE
always appends, REVERT truncates to a checkpoint length); the abstract state
is a **map**. The correspondence is NOT a field match — it is
**"log-replay = map"**:

```
-- Last-write-wins replay of the log into the abstract map (this is exactly
-- the semantics of the guest's scan-from-end SLOAD and of
-- exec_log_latest_value, so the α mirrors real routines, not an invention):
α_storage (entries : List StorageLogEntry) : (EvmWord × EvmWord) → Option EvmWord :=
  fun (addr, slot) =>
    (entries.reverse.find? (fun e => e.addrHash = addr ∧ e.slotKey = slot)).map (·.current)

-- Against a base map σ (the pre-state / preload):
mapOf (σ : Map) (entries) : Map := fun k => (α_storage entries k).getD (σ k)
```

Correspondence statements this induces (all sketches):
1. **SLOAD**: the guest's scan-from-end returns `(α_storage log
   (env.ADDRESS, slot)).getD 0` — provable against `storageLogIs_split_at`
   once the SLOAD handler has a spec (it currently has none).
2. **SSTORE**: append (`storageLogIs_snoc`) corresponds to a map update:
   `mapOf σ (log ++ [e]) = (mapOf σ log)[(e.addrHash, e.slotKey) ↦ e.current]`
   — a pure lemma about `α_storage`, provable today with no machine code.
3. **REVERT**: length truncation corresponds to discarding the suffix:
   `mapOf σ (log.take checkpoint)` — the map-rollback the journal design
   buys; again pure.
4. **`original` fields**: carry the pre-tx value for gas refund logic — they
   correspond to `σ` (the base map), giving the invariant
   `e.original = (mapOf σ (entriesBefore e)) (e.addrHash, e.slotKey)`-style
   coherence; needed only by the gas refinement, keep it out of the core α.
5. **Canonical `storage_writes`** (`STORAGE_WRITES_AREA`): the cumulative
   `BlockState.storageWrites` map, with one flat row per `(recipient, slot)`.
   `write_sets_incorporate_tx` populates it and
   `storage_writes_block_latest_value` supplies current-value preload reads;
   it is not a separately maintained per-transaction snapshot table.

**Who performs the replay in the guest**: nobody materializes the map — the
scan-from-end lookups (`exec_log_latest_value`, the SLOAD handler, the
BAL-vs-exec validators `.41`–`.43`) each *compute `α_storage` pointwise*.
That is why the α above is honest: it is the routines' shared semantic
model, and the pure lemmas (2)/(3) are the right first PR — they need only
`StorageAssertions` + list reasoning, no triples.

**Alignment / divergence.** (a) `addrHash` keying: the log keys by the
frame's `env.ADDRESS` (32-byte zero-extended), the abstract map by 20-byte
`Address` — injective embedding, but the preload path writes `addrHash = 0`
rows (dispatcher prologue seeding) which the α must treat as the *implicit
current-recipient* key: this is a real subtlety, encode it in the α's key
normalization rather than discovering it mid-proof. (b) the trie side
(`storage_root_single_slot`, MPT set) relates the map to *roots* — that
correspondence goes through §3/§4's node machinery, not through the log.

## 8. `callFrameIs` / the phase model → **no abstract counterpart (by design)**

SpecRef has no message-frame type (the Python `Message` dataclass is below
the seam; `Stateless/VM/Message.lean` is an explicit scaffold). The frame
arena geometry, the H/D phase views (`CallFramePhase`), and the per-depth
window algebra (`CallFrameWindows`) are **implementation scaffolding below
the refinement**: their job is to make the per-frame resources
(`frameMemWindow`, stack window, env window) *available* to Tier-2
correspondences (§6's per-frame memory base; `evmStackIs` inside the stack
window; env-cell assertions), not to correspond to anything abstract
themselves. The only abstract content the phase model contributes is a
*hygiene obligation*: the refinement proof may not transport any abstract
fact across an H↔D transition (contents are havoc'd by construction). Status
caveat: the model is currently pinned to stale constants — the `.71`–`.74`
audit cluster (`docs/4ch8f-callframe-audit.md`) must land before any Tier-2
correspondence instantiates per-frame bases. `encodesFrame`
(`CallFrameWindows`) already fixes the SHAPE of the suspended-frame relation;
its abstract side will be the engine port's frame stack when `.8` exists.

## 9. The north-star: `guestStateCorresponds`

The top-level refinement predicate, staged at the seam (doc-level sketch;
intended home `EvmAsm/Stateless/Correspondence.lean` once the `.8` engine
port fixes the sub-seam abstract state — deliberately not committed as Lean
yet, to avoid freezing signatures against a seam that is still a stub):

```
-- Tier 1: at dispatch entry (the seam), the concrete input regions
-- correspond to the SpecRef pre-state.
def preStateCorresponds
    (stateBs codesBs headersBs : List Byte)      -- witnessSectionIs contents
    (appended : List (List Byte))                -- nodeDbIs contents (empty at entry)
    (records : List WitnessIndexRecord)          -- codeDbIs contents
    (pre : SpecRef.WitnessPreState) : Prop :=
  pre.nodeDb = build_node_db (sszSectionElements stateBs) ∧
  pre.codeDb = build_code_db (sszSectionElements codesBs) ∧
  appended = [] ∧
  (records.map (·.hash)) = pre.codeDb.map Prod.fst   -- index honesty (§2)
  -- + pre.stateRoot = parent_header.stateRoot via the §1 headers section

-- Tier 2: during execution, per active frame (target type = today's
-- executable-spec layer; re-targets to the .8 engine state verbatim).
def execStateCorresponds
    (mem : List Byte) (msize : Nat)              -- evmMemoryIs contents
    (stack : List EvmWord)                       -- evmStackIs values
    (log : List StorageLogEntry) (σ : Map)       -- storageLogIs + base map
    (s : Evm64.EvmState) (w : EL.WorldState) : Prop :=
  (∀ cell, s.memory cell = dwordAt mem (8 * cell)) ∧ s.memSize = msize ∧
  (∀ i, i ≥ msize → getByteAt mem i = 0) ∧        -- zero-tail invariant (§6)
  s.stack = stack ∧
  (∀ a k, w.storage a k = mapOf σ log (embed a, k))  -- log-replay = map (§7)

-- The conjunction, quantified over the sep-conj decomposition:
guestStateCorresponds (ps : PartialState) (spec : …) : Prop :=
  ∃ (contents… params…),
    (witnessSectionIs p₁ stateBs ** codeDbIs … ** nodeDbIs … **
     evmMemoryIs … ** evmStackIs … ** storageLogIs … ** frames…) ps ∧
    preStateCorresponds … spec.pre ∧ execStateCorresponds … spec.exec
```

Because every Assertion carries its contents as parameters, each conjunct of
the correspondence is a *pure* equation between parameters and abstract
fields — the heap appears exactly once (the big `**`). The
interpreter/verdict refinement then discharges it step-by-step: each opcode
triple updates one Assertion's parameters, and the matching pure lemma
(§7's (2)/(3) pattern) updates the abstract side.

## 10. Gaps, explicitly

**SpecRef structures with NO SL Assertion yet** (correspondence incomplete
there): `Header`/`validate_headers` and the headers section's parent-hash
chain (the guest's `headers_validate_chain`/`svf_headers_*` cells have no
assertion); `ExecutionPayload`/`NewPayloadRequest`/`ExecutionRequests`/
`Withdrawal*` (SSZ input beyond the witness — guest reads them in place, no
vocabulary); `ChainConfig`/fork logic; `StatelessValidationResult` (the
OUTPUT region write); `trieLookup`'s root-to-leaf *path* (no assertion for
"a resolved trie path", only per-node); the `SpecRef.Runtime` jumpdest model
(pairs with the jumpdest-bitmap session's surface, not this vocabulary);
`Secp256k1Recover`/crypto (other sessions' surface).

**SL Assertions with NO SpecRef counterpart** (implementation detail below
the refinement): the call-frame arena/phase/window family (§8); the resolve
cache (§3 — abstraction-invisible); the witness-index *sortedness and
registration cells* (search-strategy detail; only the lookup result is
abstract); `nodeDbCountIs`/`nodeDbTopIs` bump-pointer cells; the storage-log
*capacity* and checkpoint cells (the checkpoint's abstract content is
REVERT's `take`, §7(3)); `evmMemoryIs`'s reserved-capacity tail.

**OPEN QUESTIONS** (marked, not guessed): (1) does the `.8` engine port keep
`EL.WorldState`/`Evm64.EvmState` or introduce fresh SpecRef types? — the
Tier-2 α's are written to survive either, but `guestStateCorresponds`'s
final types wait on it. (2) The preload `addrHash = 0` key normalization
(§7a): confirm the dispatcher's seeding convention before fixing the α's
embed. (3) Whether the canonical `storage_writes` rows should gain a
dedicated assertion wrapper or remain covered by the Codegen map contract.
(4) The inlined-child MPT extension (§4b) — needed for tries with < 32-byte
subtrees; frequency in real witnesses unknown.

**Ordered next proofs** (each small, each closes a sketched α): (i) the
`mapOf`/`α_storage` pure lemmas for SSTORE-append and REVERT-truncate (§7);
(ii) `rlpToMutableNode` + `rlpToMutableNode (n.rlp) = .ok (α_node n)` (§4);
(iii) the `witnessLookupSpec`-vs-`build_code_db` slice equation (§2);
(iv) the MSTORE contents-update fold (§6); (v) the general
`sszSectionElements ∘ serialize` inverse (§1).
