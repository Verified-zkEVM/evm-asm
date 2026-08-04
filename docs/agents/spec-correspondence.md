# Spec-correspondence — auditing whether a proven routine proves the right thing

**Load when:** you are about to declare a guest routine or family "done"; you are
changing a decoder, encoder, or validator that has an `execution-specs`
counterpart; or you are starting a correspondence audit for a new family.

This page is the **method**. It does not restate proof mechanics (see
`port-playbook.md`) or the doctrine of aligning the guest to the spec's model
(see `spec-alignment-doctrine.md`). Per-family findings live in
`docs/<family>-spec-correspondence.md`; the machine-checked verdicts live in
`EvmAsm/Progress/Correspondence.lean` and render into `PROGRESS.md` §F.2.

## 1. The question

A whole-routine Hoare triple says the RISC-V code implements the Lean spec
written beside it. **It says nothing about whether that spec agrees with the
Ethereum reference implementation.** Both can be true at once:

> the proof is valid, and it is about the wrong property.

Two failure directions, and they are not symmetric:

- **stricter** than the reference → false-rejects on valid chain data.
- **looser** than the reference → a **false-accept**, the one gate that never
  relaxes (`spec-alignment-doctrine.md` §2).

The audit that prompted this method (#10779/#10782) had measured the wrong
artifact — it counted theorems in the module that *emits* each routine, while
this repo keeps specs in sibling modules — and reported two routines unproven
that were already done. That is the failure this page exists to prevent, and the
reason every verdict below carries a **basis**.

## 2. Verdict vocabulary

| Verdict | Meaning |
|---|---|
| `agrees` | Spec and reference agree on the routine's whole domain. |
| `domain-restricted` | Agrees, but the spec covers strictly less input than the reference accepts. Not a defect — a coverage gap callers must respect. |
| `stricter` | We reject input the reference accepts. |
| `looser` | We accept input the reference rejects. **Soundness finding; file immediately.** |
| `no-counterpart` | Guest-specific operation with no reference function to compare against. |
| `n/a — unproven` | No spec exists, so the question is not answerable. An honest result, not a gap to paper over. |

Do not collapse these to a boolean. The asymmetry *is* the product.

## 3. Basis — how much a verdict is worth

| Basis | Meaning |
|---|---|
| `diff` | Backed by the executable differential (`lake exe correspondence-check <family>`). |
| `bridged` | The spec is stated over — or tied by a **cited** bridge lemma to — the shared model, so it inherits the `diff` result. |
| `ported` | The spec is tied by a **cited and consumed** bridge lemma to a `SpecRef` **port** that is not itself differentially backed. Machine-checked, so stronger than `inspection`; no `diff` to inherit, so weaker than `bridged`. **Only claimable with a port-fidelity clause table** (§6a). |
| `machine-only` | The spec is stated over a *locally defined* predicate that re-derives the reference's rules independently of the shared model. The differential result does **not** transfer. |
| `inspection` | Established by reading both sides. No executable or formal backing. |

The ladder, weakest to strongest: `none` → `inspection` → `machine-only` → `ported` →
`bridged` / `diff`. `ported` was added in #11341: without it, a row whose tie to the
reference is a *machine-checked equality* against a port had to be filed under
`machine-only`, whose description ("stated over a locally defined predicate") is simply
false for such a row even though its operative clause ("the differential does not
transfer") is true. Two rows sat in that contradiction before the rung existed.

**A verdict without a basis is an unverified claim**, which is precisely what
produced the stale findings in §1. `EvmAsm/Progress/Correspondence.lean` proves
`basis_diff_requires_spec` and `verdict_requires_spec` so the two most common
overclaims cannot be recorded.

## 4. The inheritance gap

The trap that catches everyone, stated generally:

> **Availability is not use.** A spec module can import the shared model and
> still not *use* it — stating its postcondition over a locally defined
> predicate that re-derives the same rules from raw bytes.

Where that happens, a differential result about the model **does not transfer**,
and a drift between the local predicate and the model would be invisible to both
the differential and the existing proof. Checking imports is not enough; read
the *statement*.

*Worked example (RLP).* All 15 RLP spec modules transitively import
`EvmAsm.EL.RLP`, so a crude import check reports "all tied to the model". But
`rlpItemDecode` (`Rv64/RLP/WalkNext.lean:3649`) restates the prefix cases as
`BitVec` comparisons against `0x80`/`0xb8`/`0xc0`/`0xf8` inline in the
statement, and `rbesSize` (`RlpBytesEncodedSizeSAsm.lean:89`) is standalone
arithmetic rather than `(encode …).length`. Those rows are `machine-only`.
Where a bridge lemma exists and is cited — `risSpan_eq_encode_length`,
`Rv64/RLP/WalkDecodeBridge.lean` — the row is `bridged`.

Closing a `machine-only` row means a lemma of the shape
`<local predicate> ↔ <shared-model statement>`.

## 5. Choosing the comparison boundary

A family whose interface is stateful (a mutable builder, a threaded DB) has no
data-in/data-out interface at routine granularity. It is still auditable — but
only at a **functional boundary**, and the audit must say which boundary it
chose. Examples: MPT at `{(key, value)} → 32-byte root`; block-access-lists at
`builder → serialized bytes → hash`.

Choosing silently is the failure mode: a table that looks per-routine but was
actually measured at the root boundary overstates its coverage.

## 6. Reference taxonomy — this decides how much machinery you need

| Kind | Where it lives | What pins it | Extra machinery |
|---|---|---|---|
| **Vendored** | `execution-specs/src/…` | the gitlink | none — cite it and `scripts/check-spec-refs.sh` machine-checks the citation |
| **External** | a PyPI package execution-specs depends on (`ethereum_rlp`, `remerkleable`) | `execution-specs/uv.lock` | version resolved from the lock, installed version verified against it, version stamped into the corpus |

Most families are **vendored** and need none of the external-package machinery.
Do not copy the RLP instance wholesale — it is the harder case.

### 6a. ⚠️ A vendored citation establishes PROVENANCE, not FIDELITY

`scripts/check-spec-refs.sh` machine-checks that a cited `forks/…/x.py:NNN` **exists** and
that the named symbol is there. It structurally **cannot** check that the `SpecRef` port
*says the same thing* as those lines. The two get conflated, and the conflation is
invisible: a row can cite a real line, elaborate cleanly, and still rest on a port that
quietly restated a clause.

That is not hypothetical. `check_gas_limit`'s port writes the lower guard as
`gas_limit + delta ≤ parent`, where `fork.py` writes `gas_limit ≤ parent - delta` — a
deliberate improvement, because `Uint` subtraction truncates on underflow where Python ints
do not. The two agree **only because `delta = parent / 1024 ≤ parent`**, which is a fact
about the factor, not a syntactic identity. It was relied upon until a reviewer asked; it is
now `clause2_port_faithful`.

**So any row claiming `ported` must record a port-fidelity clause table**: the reference's
clauses beside the port's, with every non-syntactic restatement either **proved** (cite the
lemma) or **named as an assumption**. Without that requirement `ported` is `machine-only`
with a friendlier name. Doing this once per row is what would let the category be trusted
rather than merely disclosed.

> **The trap this table exists for.** `ethereum_rlp` **0.1.5 silently accepts
> trailing bytes after a complete item; 0.1.6 rejects them.** A stale
> environment supplies 0.1.5, and reading it inverts a strictness verdict. Note
> `pyproject.toml` carries a *range*, not a pin — only `uv.lock` pins.
> Related: a fresh worktree has an **empty** `execution-specs/`, and the main
> checkout may sit at an older rev than the gitlink. Always
> `git submodule update --init execution-specs` and check the tag.

## 7. When NOT to audit a family

Auditing these produces confident nonsense. Each is a category error, not a gap:

| Family | Why an audit misleads |
|---|---|
| `zkvm_*` accelerator ecalls | The digest is produced by the **host**. There is no guest code whose correctness a triple could establish, so a "verified correspondence" would be presenting an **axiom** as a theorem. Audit one layer down (`Rv64/ZiskAccel.lean`) as a *model* audit with an empty routine column. |
| Field/curve limb kernels (`secf_*`, `bnf_*`, `blsg*`, …) | execution-specs has **no per-field-operation function** — it calls out to `coincurve`/`py_ecc` at the precompile boundary. The reference column is empty *by construction*; good proof coverage here makes that look like a gap when it is not. |
| `h_*` opcode handlers | Python mutates an `Evm` object in place, so there is no data-in/data-out interface at handler granularity; the honest comparison point is the whole transducer. They are also absent from `GuestAddrs` by design (`Codegen/Proofs/OpcodeTables.lean:28`) and rooted in `EvmAsm.Evm64` (closure ~1471 modules / 15 Mathlib roots). Use `arith-diff-check` and `specref-eest-check` instead. |
| Guest-ABI routines (`frame_*`, `mset_*`, `bv_*`, call-frame, verdict buffers) | `no-counterpart` by construction — call-frame layout and verdict encoding are ours, not the spec's. |

## 8. How to add a family

1. **Enumerate the rows.** `scripts/asm-fixtures/symbol-addresses.tsv` is the
   full linker-facts list (904 non-local `.text` symbols);
   `EvmAsm/Codegen/GuestAddrs.lean` covers the 402 that are cross-referenced by
   a converted `_prog`. Filter to the family prefix.
2. **Locate each spec by grepping the routine symbol TREE-WIDE — never the
   emitting module.** The emitting module holds only the string↔`Program` drift
   guard; specs live in sibling modules. This is the #10779 lesson and it is the
   single most common way an audit lies.
3. **Pick the boundary** (§5) and write it down.
4. **Classify the reference** (§6). Vendored ⇒ skip the pin machinery.
5. **If the family has an executable reference and a shared model**, write a
   `Subject` (`EvmAsm/Tests/Correspondence/<Family>.lean`) and a corpus
   generator (`scripts/oracles/<family>.py`), then register both:
   `EvmAsm/Tests/Correspondence/Registry.lean` and `scripts/spec-oracle.py`.
   If it does not, the family is prose-only — say so explicitly on its page
   rather than inventing verdicts.
6. **Record rows** in `EvmAsm/Progress/Correspondence.lean` with verdict, basis,
   and an `abbrev` witness for each named spec.
7. **Write the instance page** `docs/<family>-spec-correspondence.md` using the
   rubric in §10.

## 9. Harness contract

Everything family-agnostic is in `EvmAsm/Tests/Correspondence/Harness.lean`.
What a family inherits, and must not weaken:

- **Exit codes.** `0` agree · `1` divergence or stale pin · `2` the instrument
  could not run. Distinguishing 2 from 1 matters: "found nothing" and "could not
  look" are different results.
- **Self-test obligation.** Plant one finding of each class and assert **exact
  counts** — so the check demonstrates the right thing fires *and* that an
  agreement is not flagged. A gate that cannot demonstrate catching a violation
  is itself unaudited. Registering a family in `Registry.lean` forces this;
  there is no path that runs a comparison without one.
- **Staleness guard runs first.** A green tally must never print next to a
  corpus describing a reference the repo no longer pins. The guard reads the
  `execution-specs` gitlink from the superproject tree, which works **without
  the submodule checked out** — i.e. in CI.
- **Capped reporting.** Per-class caps; an uncapped dump is one bad corpus away
  from a 200k-line CI log.
- **Rejection reasons are NOT compared.** A reference's messages describe its own
  control flow (`ethereum_rlp` reports a bare byte plus trailing data as
  `negative length`) and carry no obligation for a different implementation.
  Requiring reason equality manufactures failures.
- **No Mathlib.** The harness and every `Subject` must stay out of the Mathlib
  import closure — that is what makes a correspondence check a per-PR gate. The
  whole `SpecRef` tower (41 modules) is Mathlib-free, so most candidate models
  qualify; `Evm64`-rooted ones do not. The *registry*
  (`Progress/Correspondence.lean`) is exempt — it must import proof modules to
  witness them.

## 10. Instance-page rubric

Keep instances comparable. Fixed sections: **Pins** → **Boundary chosen** →
**Differential result** (or why there is none) → **Routine table** → **Gaps and
follow-ups** → **Reproduce**. Verdict and basis columns must match the registry;
the page carries the prose a Lean table cannot.

## 11. Adopting the existing checkers (not yet done)

Four differential checkers predate this framework. They are **not** migrated,
and two may not fit — recorded here so the question is not re-derived:

| Checker | Fit | What adoption would need |
|---|---|---|
| `rlp-diff-check` | Good | Its vector legs are `Subject`-shaped; the fuzz leg is oracle-free (round-trip + canonicality invariants) and would need a second shape, "self-consistency" rather than "vs reference". Also currently **not wired into CI**, and its docstring cites a `scripts/rlp-check-all.sh` that does not exist. |
| `arith-diff-check` | Plausible | Total function, pointwise equality — fits `Subject` with `input` as an operand tuple. But it is the **one live CI gate** of the four; migrating it risks a working gate for a refactor. |
| `div128-v5-check` | **Poor** | Its verdict is *interval containment* (`q ≤ v5 ≤ q+1`), not equality — the model is deliberately allowed to overshoot by one. Would require a family-supplied `compare`, i.e. a genuine generalization of `Outcome`. |
| `specref-eest-check` | **No** | A whole-guest transducer: external processes, byte-region masks with per-region severity, threshold gates rather than zero-tolerance, an allowlist, and parallel workers. Shares no Lean code with the above. Govern it by the conventions in `scripts/eest-specref-check.sh` instead. |

Two cheap wins that do not require migration: the four independent copies of
`hexDigit?` across `EvmAsm/Tests/` can move to `Harness.lean`, and the three
hand-rolled LCGs there all sample the **low** bits of a power-of-two-modulus
generator — whose period can be as short as 2, collapsing a generated corpus
under dedup. `spec_oracle.lcg` documents the high-bit fix.
