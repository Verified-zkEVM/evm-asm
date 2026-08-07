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
exclusion. Every *guest* routine remains `unproven`, but ⚠️ **no longer for the
reason this page originally gave.** It said `BalCanonicalSort.lean` defines only
`String`s — zero `: Program` — so no `cpsTripleWithin` was statable. **#11046
falsified that**: the routine is now `balCanonicalSort_prog` (147 instructions)
and is registered in the guest image. A triple is statable; none has been stated.

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

**Does not close:** the machine-side obligations. ⚠️ This paragraph used to say
they *"still need the ~230-instruction conversion, which is separately blocked"* —
**that conversion landed as #11046** (with both deviations approved: `.globl` in
the string prefix, the digit fragment as its own `Program` composed at list
level), and #11054 then deleted two of the four routines as unreachable.

What actually remains is a **predicate** gap, not a `Program` gap. #10817's
headline obligation is **permutation** — a sort that silently drops rows is still
sorted, and the end-to-end hash comparison structurally cannot see it, because it
compares against a model built from the *declared* rows. Stating permutation needs
a `List`-indexed assertion over the row array, now supplied by
`RegionPredicates.balEntriesFrom` / `balBuffer` / `balOwn` (stride-parameterised:
the six live calls use four distinct strides, all 8-aligned).

## Findings — filed, not carried here

All of these are tracked as issues, so this page records them for context rather
than as open work on the audit.

**[#11017](https://github.com/Verified-zkEVM/evm-asm/issues/11017) — `BalCanonicalSort` hygiene cluster:**

- `bal_sort_storage_writes` / `bal_sort_account_writes` were **dead code**, and
  are now **deleted** — retired in `da930613c`, riding a repin-forcing change as
  GH #11054 recommended. Re-measured absent on `main` `696c236f2`: **zero
  occurrences** in the emitted asm (including the `.globl` and the label) and
  zero in the ELF symbol table, against a live control of 8 for
  `bal_canonical_sort`. Their registry rows and routine-table rows went with
  them; the two `#guard`s at `BalCanonicalSort.lean:550`–`551` were kept, and now
  pin the routines' **absence** rather than an unreachable path. ⚠️ Those guards
  test one definition's string, so they would not catch re-emission from a
  different definition — the whole-image grep is the broader check.
- Status 4 ("unsupported firstSig") is documented at `:199` and **never emitted**.
- Comment/code drift at `:498`: the comment says `account: [(0,20)] = 0x1400`;
  the guard and code use `0x9400` (`0x1400` is the *selftest's*).

**[#11018](https://github.com/Verified-zkEVM/evm-asm/issues/11018) — the
per-container bound question, and the representation gap:**

- **`BalCanonicalSort.lean:218` is NOT a defect.** An earlier revision of this
  page called it "possibly a real bug"; that was wrong. Using
  `blockAccountWritesCapacity` for every container is a **deliberate
  static-allocation choice** under tight memory. What remains open is the
  *behavioural* question it leaves: static sizing governs what the guest **can
  hold**, while the spec governs what a block may **validly contain**, and one
  shared capacity settles only the first. If a container's logical limit is
  tighter than the shared allocation, a runtime bound may be needed for
  equivalence.
- **Representation gap — a proof-side caveat, not a model defect.** Python holds
  `storage_changes` in a `Dict` and `storage_reads` in a `Set`; the Lean model
  uses `List` for both, so it can represent duplicate slots and duplicate reads,
  states the reference cannot. The corpus stays inside the representable domain,
  so the 1149/1149 result is sound — it simply **cannot speak to the surplus
  domain**, which is exactly what matters for #10817 if a uniqueness obligation
  is stated over `List`.

**Upstream:** the reference's docstring/code mismatch on "lexicographically"
(above) is worth reporting to execution-specs. Independently confirmed in
review: the docstring lists "Storage slots (lexicographically)" while the code
sorts `U256` numerically.

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
