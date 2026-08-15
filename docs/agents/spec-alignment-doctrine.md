# Spec-alignment doctrine

**Load when:** a fix touches guest state/gas semantics and you have a choice
between mirroring `execution-specs` and patching the guest's own
reconstruction; or when a fix would break a formal proof; or when you are about
to add guest state that has "no obvious spec counterpart." This page is the
*why* behind several Critical Rules; it does not restate mechanics (see
`verified-replacement-strategy.md` and `port-playbook.md` for those).

The north star is `run_stateless_guest_spec`: the guest's behavior must equal
the `SpecRef` port of `execution-specs`' `run_stateless_guest`. Everything below
follows from taking that literally — the guest is a *reconstruction of the
spec's semantics*, not an independent implementation that happens to agree.

## 1. Align to execution-specs, even at a temporary cost

When an existing false-reject (or any residual) touches a data-structure
mechanism or a semantic the spec models directly, **drive the guest toward the
spec's model** rather than adding a point-fix or a guard on the guest's own
reconstruction. This holds **even if the convergence temporarily causes
additional false-rejects** — the convergence argument survives; the bar does
not. `FA = 0` (no false-accept) remains inviolable, **and** an in-envelope
false reject is a **defect** (maintainer 2026-08-15: machine accepts iff spec
accepts, under the project envelope of small block number / timestamp / gas
costs — see `docs/agents/spec-correspondence.md` §"precondition reading"). A
temporary `+FR` while a data-structure converges is therefore a **known defect
being carried**, not an accepted cost: track it as such, and do not call the
convergence finished while in-envelope FRs remain. The envelope itself is a
**precondition of the theorem statement**, not a gate and not an excuse for an
in-envelope rejection.

Corollaries:

- **Mirror the spec's MODEL, not just its outputs.** Prefer one mutable state
  that mirrors `BlockState`/`TransactionState`/`Account` over an append-only
  effect log reconstructed with guards. Piling guards onto a reconstruction to
  make one more case pass is a *pivot signal*: stop and mirror the model.
- **Never echo a claimed answer into state that execution reads.** Any value
  execution consumes (balance, nonce, existence, code-hash, storage) must be
  *execution-derived* — from the authenticated pre-block state (witness/header)
  plus the guest's own tracked tx effects — never read back from the block's
  claimed post-fields (BAL). Reading the claimed answer and then comparing to it
  is circular and is a false-accept waiting for the backstop to be removed.

## 2. Replacing proven code with unverified code is allowed

A fix is **not** blocked by the fact that it would break an existing formal
proof (a Hoare triple, a loop invariant). Ship the corrected path as
**unverified emitted code** and defer the proof to the provability track. This
is a *reduction* of the proof set, not an axiom — so it stays within the trusted
base. The two hard ship-gates that still hold:

1. **Axiom-cleanliness** — no `sorry`/`sorryAx`/`native_decide`/`bv_decide`;
   `check-axioms.sh` stays green, trusted base = classical-3
   (`propext`/`Classical.choice`/`Quot.sound`).
2. **Empirical iff (both directions)** — the EEST A/B sweep is only half the
   gate if it only shows `FA = 0`. For unverified code the hard empirical bar
   is **machine accepts iff spec accepts** in-envelope: `FA = 0` **and** no
   in-envelope false reject (`FR = 0` on inputs the envelope admits), with a
   clean `swept == shipped` `.text`. Out-of-envelope rejects remain fine when
   the envelope is an explicit theorem precondition.

Do not defer or pivot a correctness fix *merely* because it breaks a proof, and
do not park the correct spec behavior as a "for-later" note while shipping a
coarser version — fold the spec-correct behavior into the same change. Memory /
TODO notes are for durable facts, not a way to land a knowingly spec-divergent
fix.

## 3. Build the spec-aligned FINAL form; don't salvage a near-working stage

When a non-spec mechanism *almost* works, the pull to keep it and bolt on a
bridge (a "hybrid") is strong — resist it. Build the spec-aligned final form.
Two reframes make this easier and are usually decisive:

- **The working logic is lifted, not discarded.** In a relocation the correct
  parsing/validation/arithmetic moves wholesale into the spec-aligned routine;
  only the wrong *structure/timing* is retired. Little real work is thrown away.
- **The hybrid is genuinely MORE complex than the final form.** A hybrid keeps
  two mechanisms with two state-timing regimes that must be kept consistent and
  reasoned about together; the final form is one routine, one state source, one
  timing. Spec-aligned is also *simpler* code.

And: **structural impossibility is not a case for more instrumentation.** If a
stage runs at a point where the information it needs no longer exists (e.g. a
post-hoc pass reading per-tx state after the per-tx state is gone), no bridge or
probe fixes it — the decision must **move** to the site where the information is
live.

## 4. The spec's control flow becomes a value in guest memory

`execution-specs` is Python: it expresses outcomes with control flow —
`try/except`, snapshots, exceptions, early returns. The stateless guest has no
exceptions and no snapshots; it is a straight-line reconstruction. So **a spec
control-flow outcome is represented as a value (a cell) in RISC-V memory** — and
that value must be **derived from the spec's own determinant**, never invented
as free-standing state.

Worked example (EIP-7702 `set_delegation`, `vm/interpreter.py`
`process_message` at depth 0):

- The spec takes `prep_snapshot` before `set_delegation`; on an auth-phase
  `ExceptionalHalt` it restores that snapshot (authorizations reverted,
  `auth_state_gas_used = 0`). It takes a second snapshot *after* the prep phase;
  a body revert restores to *that* one — so **the authorization's state
  mutations survive a body revert**, and roll back only on an auth-phase OOG.
- The guest materializes this as a derived `auth_phase_applied` cell: set only
  after the intrinsic auth-count + auth-state charge + top-frame regular charge
  have all passed (i.e. the prep phase did not OOG). The cross-tx publish of the
  authority's existence/nonce/delegation is gated on
  `tx-success OR auth_phase_applied` — exactly mirroring "which snapshot the
  rollback lands on."
- Crucially the cell is **derived** from the gas-coverage the guest already
  computes (does the tx's gas cover the prep-phase charges?), not a standalone
  status bit that could drift from the accounting. "Is this cell in the spec?"
  — no; the spec has the *branch*. The cell is the guest's faithful
  materialization of that branch.

## 5. Get the spec's temporal scopes exactly right

The same address can be governed by different temporal scopes; mirror each
exactly (again from EIP-7702 `set_delegation`):

- **`NEW_ACCOUNT`** ← `account_exists(tx_state, authority)`, and `tx_state`'s
  parent is `block_env.state` — so existence is **cross-tx persistent** (a prior
  tx's creation is visible). This is what the mutable `AccountState` mirror
  carries forward.
- **`ACCOUNT_WRITE`** ← a `written_accounts` set that is a *local* variable
  re-initialized every `set_delegation` call — so it is **per-tx, reset each
  tx**, seeded with `{sender} ∪ {recipient if value > 0}`. A non-sender
  authority pays it in every tx.
- **`AUTH_BASE`** ← `delegated_before_tx` (a *pre-tx* delegation snapshot) plus a
  per-tx `delegation_set_for` set; at most once per authority, never credited
  back.

Sharing one signal across two different scopes is a bug (e.g. using the
cross-tx-persistent existence flag to suppress the per-tx first-write charge).
And ordering matters: `process_transaction` increments the **sender** nonce
*before* `set_delegation`, so a self-sponsored authority's signed nonce is
validated against the *incremented* value — the guest's as-of nonce must reflect
that, mirroring the spec order rather than special-casing it.

## 6. Debugging discipline that keeps you spec-honest

- **Exact-discrepancy-first.** Before theorizing a mechanism, pin the exact
  discrepancy: magnitude *and* component. For a gas mismatch, decompose header
  vs guest by dimension (state / regular / intrinsic / auth-base / refund) and
  identify *which tx*. Never anchor on an intermediate/staging value
  (`*_wouldbe_*`, a scratch cell) — those are inputs to the computation, not the
  verdict delta.
- **Ground truth for canonical values.** When you need the canonical number
  (e.g. a per-tx receipt `cumulative_gas_used`), get it from `execution-specs`
  (t8n / the reference that yields oracle `succ = 1`) or the fixture's recorded
  values — do not infer it from the guest's own output or from a hash you can't
  invert.
- **Single-writer.** Two accumulators computing "the same" quantity by different
  paths will drift. A charge that reaches the header total but not the receipt
  cumulative is not a receipt-encoding bug — it is two writers; fix at the
  shared source.
- **A fix's own regression is hold-and-repair.** Shipping at `FA = 0` with
  *exposed* pre-existing in-envelope FRs is shipping with **exposed
  pre-existing bugs** under the iff bar — track and clear them; do not call
  that state fine. A regression *introduced by the fix itself* (an `OK → FR`
  transition vs the exact parent) is still worse and remains hold-and-repair
  before merge. The exact-parent A/B is the arbiter of new-vs-pre-existing.

## 7. Preserve digest comparisons when the spec compares digests

When `execution-specs` compares a commitment hash, the guest must compare the
same digest value, not the underlying bytes or structure. This is a
spec-alignment rule, not a cryptographic assumption. Hash collisions are
provably present in the mathematical model: an arbitrary-length byte-string
domain maps into a 256-bit codomain, so the pigeonhole principle gives distinct
inputs with the same digest.

That makes digest equality and raw-value equality observably different
functions. On a colliding pair, the reference's digest comparison accepts while
a guest that replaces it with raw-byte comparison rejects. The latter is a
false-reject divergence introduced by making the check appear stronger. Do not
replace a spec-level digest comparison with a raw comparison, and do not treat
collision resistance as a premise needed to justify the relative
guest-versus-`execution-specs` claim.

The current load-bearing sites are:

- BAL digest: `EvmAsm/Codegen/Programs/BalSerializer.lean:1159-1167`.
- Post-state-root digest and its MPT production:
  `EvmAsm/Codegen/Programs/BlockVerdictMtxRuntime.lean:739-748` and
  `EvmAsm/Codegen/Programs/BlockVerdictStateRoot.lean:445-449`.
- Block-hash digest: `EvmAsm/Codegen/Programs/BlockVerdictFunction.lean:65-72` and
  `EvmAsm/Codegen/Programs/Header.lean:1128-1178`.
- EIP-7685 requests digest under SHA-256:
  `EvmAsm/Codegen/Programs/BlockVerdictReceiptsTail.lean:126-135`,
  `EvmAsm/Codegen/Programs/AssembleExecutionRequests.lean:159-215`, and
  `EvmAsm/Codegen/Programs/RequestsHash.lean:1-6,112-136`.

---

These principles compound: mirroring the spec's model (1) is what makes the
final form both correct and eventually provable (2, 3); representing control
flow as derived values (4) and honoring temporal scopes (5) is *how* you mirror
it faithfully; the debugging discipline (6) keeps a reconstruction from
quietly diverging from the spec it is supposed to equal; and preserving the
spec's digest comparisons (7) prevents a seemingly stronger check from adding
a false reject.
