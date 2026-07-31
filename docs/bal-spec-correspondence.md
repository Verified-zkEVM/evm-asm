# BAL canonical ordering — spec correspondence

**Status: live authority.** Method: [`docs/agents/spec-correspondence.md`](agents/spec-correspondence.md).
Machine-checked verdicts: `EvmAsm/Progress/Correspondence.lean` → `PROGRESS.md` §F.2.
Siblings: [`rlp`](rlp-spec-correspondence.md), [`ssz`](ssz-spec-correspondence.md).

Read this before changing BAL sorting, and before working
[#10817](https://github.com/Verified-zkEVM/evm-asm/issues/10817).

## Headline

**The ordering is right. Whether the assembly implements it is open.**

`SpecRef._build_from_builder` agrees with the vendored reference on **1149/1149**
corpus records — account order, slot order, per-index orders, and the read/write
exclusion. Every *guest* routine remains `unproven`, because
`EvmAsm/Codegen/Programs/BalCanonicalSort.lean` defines only `String`s — zero
`: Program` — so no `cpsTripleWithin` is statable at all.

That split is the deliverable. It converts an open question ("is our canonical
ordering even the right ordering?") into a closed one, and leaves #10817 with a
strictly smaller obligation.

## Pins

| Artifact | Pin | Where recorded |
|---|---|---|
| `execution-specs` | `e5a8caf1b8055e4d805c7fb169edfa710914b7da` (`tests-zkevm@v0.6.2`) | this repo's gitlink |

**Vendored reference** (method §6): the gitlink is the pin, so this family needs
none of the external-package version machinery RLP requires. It does still need
the reference's *runtime deps* importable (`ethereum_types`, `pycryptodome`) —
vendored pins the code, not its dependency closure.

## Boundary chosen

`builder → canonical BlockAccessList`, compared as rendered structure.

BAL is stateful at the surface — a mutable builder threaded through block
execution — so it has no data-in/data-out interface at routine granularity
(method §5). This boundary is pure on both sides, and crucially **needs no
`Program`, no triple and no conversion**, which is why the audit can run while
#10817 is blocked.

Output-comparison-shaped, not accept/reject: the spec **never ingests** a BAL. It
re-derives one from execution and compares hashes (`fork.py:366`–`368`,
`390`–`391`), so there is no ordering validator on the spec side to be
accept/reject against.

## The ordering, precisely

All BAL sorting lives in one function — `_build_from_builder`
(`execution-specs/src/ethereum/forks/amsterdam/block_access_lists.py:518`–`580`):

| Collection | Key | Order |
|---|---|---|
| accounts (`:578`) | `x.address` (`Bytes20`) | byte-lexicographic ≡ numeric (fixed width) |
| slots (`:564`) | `x.slot` (`U256`) | **numeric** |
| storage reads (`:565`) | value | numeric; **excluded if also in `storage_changes`** (`:549`–`552`) |
| per-slot / balance / nonce / code (`:542`,`554`,`557`,`560`) | `block_access_index` | numeric |

The Lean mirror is `SpecRef/BlockAccessLists.lean:195`, six `mergeSort`s, with
`bytesLt:184` for addresses and `≤` on `U256` for slots.

> **Reference doc bug.** `_build_from_builder`'s own docstring (`:526`–`534`)
> says slots sort *"lexicographically"*; the code sorts `U256` **numerically**.
> A model written from the prose would diverge — RLP strips leading zeros, so
> encoded-byte order puts `0x0100` before `0xff` while numeric order does not.
> The corpus pins both cases.

## Differential result

`lake exe correspondence-check bal` over **1149 records**:

| Class | Count |
|---|---:|
| agree | **1149** |
| stricter | **0** |
| looser | **0** |
| value mismatch | **0** |
| accounts-ordered mismatch | **0** |

Corpus highlights — the cases the verdict turns on:

- the **endian trap** from EEST `test_bal_lexicographic_address_ordering`
  (`0x01…02` vs `0x02…01`), in both orders;
- **byte-length boundaries** (`255` vs `256`, `0` vs `1`) separating numeric from
  encoded-byte order;
- the read/write exclusion; empty code; touched accounts with all-empty fields;
- 1500 randomized builders with shuffled accounts, slots and reads.

## Routine table

| Layer | Routine / function | Spec | Verdict | Basis |
|---|---|---|---|---|
| model | `SpecRef._build_from_builder` | — (evidence is the differential) | agrees | **diff** |
| guest | `bal_canonical_sort` | — | n/a — unproven | — |
| guest | `bal_sort_storage_writes` | — | n/a — unproven | — |
| guest | `bal_sort_account_writes` | — | n/a — unproven | — |

`bal_canonical_sort` is the **live** routine: 6 call sites in
`bal_serializer_rebuild_hash` (`BalSerializer.lean:1067`–`:1101`) with builder
descriptors at strides **96 / 64 / 64 / 40 / 64 / 24**.

## What this does and does not close for #10817

**Closes:** the module's standing objection that *"sortedness plus permutation is
insufficient, because a sort on the wrong key is still sorted and still a
permutation"* (`BalCanonicalSort.lean:31`–`67`). That objection asks for a key
defined independently of the implementation's own byte-picking. A differential
against the reference's declared ordering **is** that key, and it now passes. The
sortedness predicate #10817 asks for can be written against the model this page
validates, rather than against a key inferred from the assembly.

**Does not close:** anything requiring a `Program`. Sortedness, permutation and
uniqueness as *machine* properties still need the ~230-instruction conversion,
which is separately blocked — the conversion tool refuses all four asm functions
in the module (leading `.globl`; a spliced `String` ident).

## Findings

1. **`BalCanonicalSort.lean:218` — the capacity check uses
   `blockAccountWritesCapacity` for *every* container**, regardless of which
   array is being sorted. On the live path the arrays have different capacities.
   Possibly a real bug; not exercised by this audit, which is model-layer.
2. **`bal_sort_storage_writes` / `bal_sort_account_writes` are dead code** —
   nothing calls them (`:456` says so). Their `#guard`s (`:503`–`506`,
   `:533`–`534`) pin a path nothing runs.
3. Status 4 ("unsupported firstSig") is documented at `:199` and **never
   emitted**.
4. Comment/code drift at `:498`: the comment says `account: [(0,20)] = 0x1400`;
   the guard and code use `0x9400` (`0x1400` is the *selftest's*).
5. The BAL sort symbols are **absent from `GuestAddrs.lean`** — no resolved
   address, unlike every other `bal_*` entry.
6. **Representation gap.** Python holds `storage_changes` in a `Dict` and
   `storage_reads` in a `Set`; the Lean model uses `List` for both, so it can
   represent duplicate slots and duplicate reads — states the reference cannot.
   The corpus stays inside the reference's representable domain, so this is not
   a divergence; it is a modelling difference worth knowing before anyone proves
   uniqueness against the Lean type.
7. Upstream: the docstring/code mismatch on "lexicographically" (above) is worth
   reporting to execution-specs.

## A note on the auxiliary axis

The `accounts-ordered` axis asks "were the accounts already in canonical order?"
and is scoped to the **top-level account list on purpose**. A first version
included storage reads and produced 32 mismatches — all artifacts: Python stores
reads in a `Set`, so input order is destroyed before `_build_from_builder` runs
(CPython iterates `{223, 75}` as `[75, 223]`), and the axis reported "already
canonical" for every input while measuring nothing. Accounts live in a `Dict`,
which preserves insertion order, so the narrowed question is well posed on both
sides. Manufacturing a comparison the reference cannot express is exactly what
the method warns against.

## Reproduce

```bash
git submodule update --init execution-specs
git -C execution-specs describe --tags        # expect tests-zkevm@v0.6.2

# The reference is vendored, but its runtime deps are not.
uv pip install --target /tmp/specs ethereum-types==0.4.1 pycryptodome
PYTHONPATH=/tmp/specs scripts/spec-oracle.py --family bal --check

lake exe correspondence-check bal --self-test
lake exe correspondence-check bal
```
