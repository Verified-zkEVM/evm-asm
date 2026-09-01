# Soundness preconditions and reference readings

This document records **assumptions the guest is entitled to make about its inputs**, and
**readings of the reference that the guest's behaviour depends on**. They are not implementation
details: a caller that violates an input assumption is outside the specified interface, and a
reading recorded here is a deliberate, ratified interpretation rather than an accident of
implementation.

Each entry states the assumption or reading, why the guest needs it, and what follows from it.

---

## 1. No account in the supplied pre-state may have a nonce of 2^64 or more

**Assumption.** Every account in the supplied pre-state has a nonce strictly below 2^64 — one
whose significant representation fits in 8 bytes.

**Why the guest needs it.** The guest's account representation is 8 bytes wide, and the decoder
enforces it: `account_decode` scans past the nonce field's leading zero bytes and then gates the
**significant** length at 8, branching to decode failure above it (`State.lean:97-98` at
`b543802a4`, `.LI .x7 (8 : Word)` then `.BLTU .x7 .x6`). The pinned spec has no such bound:
`Account.nonce` is `Uint`, arbitrary-size (`state.py:57-59`), and the witness decoder constructs
it from the field bytes with no length or value check (`witness_state.py:114`). So a pre-state
leaf carrying a 9-significant-byte nonce decodes fine on the reference and fails on the guest.

**Why it is safe to assume.** Execution cannot produce such a nonce. Enumerating every nonce
write in the pinned fork: ordinary transactions reject `tx.nonce ≥ U64.MAX_VALUE` and increment
once (`transactions.py:553-584`, `fork.py:555-558`, `fork.py:906`); CREATE/CREATE2 reject a
sender nonce of 2^64 − 1 before incrementing and start created accounts at 0
(`system.py:89-105`, `interpreter.py:180-196`); EIP-7702 delegation applies the same cap and a
single increment (`eoa_delegation.py:171, 187-189, 228-230`); system transactions add no new
writer (`fork.py:696-735`). The maximum reachable by ordinary transitions is therefore
2^64 − 1 — exactly at the guest's boundary. Only two supply paths can present a wider nonce:
**genesis**, whose allocation is unbounded (`genesis.py:209-221`), and a **directly-supplied
pre-state**, whose leaf bytes the caller chooses.

**Consequence if broken.** The guest false-**rejects**: it declines a state the reference would
accept. That is the safe direction — the guest never accepts a block or root it should not; it
simply refuses to rule on an input outside the interface.

**This is a claim about state provenance, and nothing in the guest enforces it.** The guest
verifies supplied witness bytes against a supplied root; it does not derive nonces from
transactions, so it cannot distinguish a post-genesis state produced by ordinary capped
transitions from a hand-minted one. The assumption is discharged by whoever produces the
pre-state, not by any check the decoder performs.

**Obligations this places on callers.**

- **Producers of pre-states** must guarantee every account nonce is below 2^64. Any state
  reached from a compliant genesis by ordinary, EIP-2681-capped transitions satisfies this
  automatically.
- **Test and fixture harnesses** constructing synthetic pre-states or genesis allocations must
  not mint accounts with nonces at or above 2^64. A fixture that does is not measuring a
  divergence: it is operating outside the specified interface, and the guest's reject there is
  the specified behaviour.

**Do not "fix" this by widening the guest's bounds.** Matching the reference would mean
representing the nonce as an unbounded `Uint` — a representation change, not a bound tweak — and
the 8-byte account field is pervasive through the decoder, the state assertions and every
account-write path. Loosening a single gate would leave the representation assumption in place
everywhere else while removing the one place it was visible; and since the failure direction is
a false reject, the narrow gate denies the caller nothing it was ever entitled to.

---

## 2. RLP advance no-wrap (`base + endOff + 9 < 2^64`) is not dword padding

**Assumption.** When an RLP walker advances over a long-form header (prefix plus up to eight
length bytes — at most nine bytes total), the address arithmetic that forms the speculative
header end stays below `2^64`. The verified leaf side condition is of the shape
`base.toNat + endOff + 9 < 2^64` (see `BalAccountNonstorageFinalsWalk.lean`).

**Why the guest needs it.** A long-form header flush against the top of the address space could
wrap mid-header in the pure `Nat`/`BitVec` model. The machine already rejects truncated headers
with `bltu end, cursor` *before* loading length bytes (`rlp_walk_init` / `rlp_walk_next`); the
`+ 9` is a proof bound on that arithmetic, not a demand for nine readable bytes past the logical
list.

**Distinct from the documented dword-padding rule.** Host input length is rounded up to a
multiple of 8 so dword memory ops stay defined. That rule gives at most seven physical pad
bytes and does **not** imply `listLen + 9 ≤ bytes.length`. Treating the latter as a host
readable-region obligation was a mis-statement (#12404): the asm load census for
`rlp_list_nth_item` shows every list `lbu` is gated by `end = a0 + a1` (after init), so exact
`bytes.length = listLen` is fine at runtime.

**What callers must discharge.** Prefer `base.toNat + listLen + 9 < 2^64` (trivial for
`INPUT`-anchored whole-input slices). Do not invent nine logical pad bytes. Follow-up work
replaces residual proof hyps of the form `listLen + 9 ≤ bytes.length` (still threaded through
K20) with that no-wrap form plus `listLen ≤ bytes.length`.

**Consequence if broken.** Only regions butted against the top of the 64-bit address space
fail the bound; ordinary guest arenas cannot.

---

## 3. A raise in the reference is a **rejection**, not an abort — `verify_stateless_new_payload` converts it

**Reading (maintainer's, ratified 2026-08-26).** Where the pinned reference raises during
stateless validation, the specified behaviour is **reject the block**. The guest rejects too. It
does **not** compute a narrowed or otherwise repaired result.

**The mechanism, and it is explicit in the spec rather than inferred.**
`forks/amsterdam/stateless.py:321-368` — the entry point our guest corresponds to:

```python
def verify_stateless_new_payload(stateless_input): ...
    try:
        validate_chain_config(...)
        ...
        execute_new_payload_request(...)
        successful_validation = True
    except Exception:                     # <- :363
        successful_validation = False

    return StatelessValidationResult(
        new_payload_request_root=...,
        successful_validation=successful_validation,
        ...
    )
```

The `try` spans the whole of validation and execution, and the handler catches bare `Exception` —
**not** `EthereumException`. So an `OverflowError`, a `RecursionError`, or any other Python-level
failure is caught here and becomes `successful_validation = False`: **a well-defined rejection
verdict, not a crash.** `run_stateless_guest` (`stateless_guest.py:72-83`) has the same shape for
deserialization failures.

**Worked case — `BLOBBASEFEE` above 2^256.** `vm/instructions/environment.py:605-608` computes
`calculate_blob_gas_price(...)` as an unbounded `Uint` and then narrows: `push(evm.stack,
U256(blob_base_fee))`. In pinned `ethereum-types 0.4.1`:

```python
def __init__(self, value: SupportsInt) -> None:
    int_value = int(value)
    if not self._in_range(int_value):
        raise OverflowError
```

⭐ **That raise fires at exactly 2^256, and it is a range assertion — not a resource limit.**
`_in_range` is a bounds test; `taylor_exponential` upstream is pure unbounded `Uint` arithmetic
with no cap, and a 256-bit integer is 32 bytes, so memory is nowhere near being the constraint.
**A machine with unbounded memory still raises here.** The `OverflowError` then reaches `:363` and
the block is rejected.

⇒ The guest **rejects** at the boundary. The helper's 256-bit rejection is correct and stays.

**Consequence.** None of the divergence an earlier draft of this section contemplated exists: the
guest and the reference agree, both rejecting. What remains a genuine defect is any guest path
that **swallows** the rejection — see the note below.

**⚠️ Correction of record.** An earlier version of this entry claimed the reference "produces no
result at all" and that block processing "aborts", and on that basis argued the guest should
compute a narrowed result (mod 2^256). **That was wrong.** It was derived from reading only
`vm/interpreter.py`, whose handlers are `ExceptionalHalt` and `Revert`, and concluding that
nothing catches a plain Python error — without ever checking the stateless entry point, which is
the layer the guest actually corresponds to and which catches bare `Exception`. The narrowing
reading also leaned on "the spec assumes infinite memory", which is true of `Uint` and irrelevant
to a range assertion. Recorded so the reasoning is not re-run.

**What this does not excuse.** A guest routine that computes a status and then discards it is
still a defect, and is the opposite failure direction from a false reject. `stageRuntimePayloadCode`
setting `a0 = 0` after the blob-gas-price helper is exactly that shape: the reference rejects at
`BAI = 0` via `:363`, and a guest that continues with a wrong value **accepts a block the
reference refuses**. Tracked in #12632.

**Scope.** This entry says a raise reaching `:363` is a reject. It does **not** say the guest may
raise, trap or fault wherever the reference does — the guest has no such wrapper and must reach a
rejection *verdict* by its own control flow, which is precisely why a swallowed status matters.

## 4. RLP nesting deeper than `rlpRecursiveDecodeDepthCap` is rejected — on constant-memory grounds, not because CPython raises

**Reading (maintainer's, ratified 2026-08-16).** The guest rejects RLP nesting deeper than
`rlpRecursiveDecodeDepthCap` (`EvmAsm/Codegen/Layout.lean:92`, currently **1024**). Rejecting at a
bounded depth is **correct by design**, not a divergence to be repaired.

**Why the guest needs it — this is the load-bearing reason.** Unbounded nesting means unbounded
recursion, which means unbounded stack: memory becomes a function of input *structure*, chosen by
an adversary. A hard depth limit turns that into a constant, which is what a fixed-budget guest
requires. The link is explicit in the layout, not implied:

```lean
def rlpRecursiveDecodeFrameBytes (depthCap : Nat) : Nat :=
  40 * depthCap + 40          -- one root frame, plus one 40-byte frame per bounded level
```

and `DispatcherExecStateGas` sizes the frame arena from exactly that expression, so the cap and the
reserved bytes have **one source of truth**.

**⛔ There is no reference boundary to match, and this is the point most easily got wrong.**
The reference has no written cap. CPython raises `RecursionError`, and the depth at which it does
is `sys.setrecursionlimit / 3` — measured at **3 frames per nesting level**, failing at 333
wrappers / 334 list nodes under the interpreter default (#12656, #12854). **That limit is
caller-settable.** So 333 is a property of a *configuration*, not of the specification, and
"match the reference's depth" is not a well-formed instruction.

⇒ The cap is therefore justified by the guest's own memory budget, and *not* by an appeal to where
the reference happens to fail.

**Consequence, stated plainly.** A caller who raises the reference's recursion limit can make it
decode deeper than 1024, so in that configuration the guest rejects an input the reference would
accept. **The guest does not promise to match a reference run with a raised recursion limit.**
Under the default configuration the reference fails well before our cap, so nothing in that range
is rejected that the reference would have decoded.

**Correction of record.** An earlier claim of a *false accept* in a 333–1024 "middle band" was
asserted as measured fact and is **wrong** — it inferred a fixed reference threshold from frame
arithmetic before anyone had measured one, and it was retracted publicly. Do not rebuild it. The
constant-memory justification above is what survived the measurement.

**⭐ Both sides measured, 2026-08-30 — and the reading above survives it.** §4 was written when
nobody had run the reference. Both boundaries have now been measured on pinned artifacts, and the
numbers are recorded here so no future reader has to re-derive them or re-infer them from frames:

| side | boundary | artifact |
|---|---|---|
| reference | depths 331 and 332 decode; **333**, 334 and 340 raise `RecursionError` | `ethereum-rlp 0.1.6`, wheel sha256 `f4144caa…` from `execution-specs/uv.lock`, CPython 3.12.3, default `getrecursionlimit() == 1000` |
| guest | accepts through observed depth **1025**; `status 7` at **1026**, 5000 and 20000 | production ELF sha256 `4104d3e8…`; harness with all seven walker/recursive spans byte-identical to the linked image |

The capped path is reachable: BFS from `_start` reaches `stateless_verdict_v2` →
`header_extract_state_root` → `rlp_walk_next` (`0x80004cec`) → `rlp_walk_next_shared`
(`0x80004d20`) → `rlp_validate_payload` (`0x80004df0`, `li a2,1024`). The cap is depth fuel, not a
byte budget — confirmed by the `1026` boundary rather than inferred from the immediate.

⚠️ **The machine cap is not the observed depth.** With cap `C` the walk accepts through observed
depth `C + 1` and first rejects at `C + 2` — hence cap 1024 accepting 1025. A reader setting the
constant to an observed figure ships a cap two levels looser than intended, with a number that
reads correctly in the source. `Layout.lean`'s docstring carries this offset (#13097).

**Ruling (maintainer, 2026-08-30): accepting through observed depth 1025 is fine — the cap stays
at 1024.** The measurement changes what is *known*, not what is *correct*: 333 remains a property
of CPython at its default limit, so there is still no reference boundary to match, and the
constant-memory justification above is unaffected. ⛔ **This is a documented divergence, not a
defect. Do not re-open it as a false accept** — that claim has now been raised and retracted
**twice** (once from frame arithmetic, once from measurement), and the second time the measurement
was sound while the inference drawn from it was not.

⇒ **Tightening the cap is the more dangerous direction, not the safe one.** Lowering 1024 → 331 to
"match" the default-limit reference would triple the exposure described two paragraphs above — the
guest rejecting inputs a raised-limit reference decodes — and shrink the frame arena by the same
factor, since `FrameBytes = 40 * depthCap + 40`.

**Relationship to §3 — same mechanism, different open question.** CPython's `RecursionError` is
an `Exception`, so it reaches `stateless.py:363` exactly as an `OverflowError` does and likewise
becomes `successful_validation = False`. **Both entries therefore reject, by the same mechanism**,
and §3's earlier framing of the two as opposites was an artifact of the mistaken abort reading it
has since retracted.

What is genuinely different here is not the *direction* but the *threshold*. §3's boundary is
exact and reference-defined: 2^256, fixed by a range assertion. §4's is not — the reference's
failure depth is `sys.setrecursionlimit / 3` and that limit is caller-settable, so **there is no
reference threshold to match** and the guest must choose one. It chooses on constant-memory
grounds, which is why that justification is load-bearing here and has no counterpart in §3.

**Keep the cap a parameter.** `rlpRecursiveDecodeDepthCap` is referenced and never unfolded by the
linked-decoder theorem (`RlpRecursiveDecodeLinkedSpec.lean:17-18`), so changing the number is an
**instantiation, not a rewrite**. Do not inline `1024`. Parameterising is also what forces the
theorems to say what the cap bounds and what happens when it is reached, rather than leaving the
bound as an ambient property nobody has stated.

**Traversal style is not constrained by this.** Slice recursion and in-place cursor traversal are
both acceptable once depth is bounded; whatever a level allocates is multiplied by a constant.
Choose on proof convenience.

---

*Written by **Claude Code** (k3 agent) at the maintainer's direction. Placed in `docs/` to match
the existing convention (`docs/agents/…`, `docs/4ch8f-…`) rather than creating a second top-level
documentation directory. §2 added for #12404 (cursor-grok). §3 added for #12632 (coord): a raise in the
reference is a rejection, converted by `verify_stateless_new_payload`. §4
records the RLP recursion-depth ruling, which rejects by the same mechanism but
must choose its own threshold.*
