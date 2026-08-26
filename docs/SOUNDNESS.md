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

## 3. The Python spec describes an ideal machine; `U256(...)` raising is a typing artifact, not EVM semantics

**Reading (maintainer's, ratified 2026-08-26).** `execution-specs` describes an **ideal situation
with unbounded memory and precision**. Where the Python types refuse a value that the idealised
machine would simply hold, the refusal is an artifact of the reference's implementation language
and not a statement about EVM semantics. **The guest computes the narrowed result.**

**Where this bites.** Amsterdam `BLOBBASEFEE` (`vm/instructions/environment.py:605-608` at pinned
`e5a8caf1b`):

```python
blob_base_fee = calculate_blob_gas_price(evm.message.block_env.excess_blob_gas)
push(evm.stack, U256(blob_base_fee))
```

`calculate_blob_gas_price` returns an unbounded `Uint`. Once the price reaches 2^256 the narrowing
`U256(...)` raises — in pinned `ethereum-types 0.4.1`, `FixedUint.__init__` is:

```python
int_value = int(value)
if not self._in_range(int_value):
    raise OverflowError
```

and **nothing catches it**: the interpreter handles `ExceptionalHalt` (`interpreter.py:232`,
`:366`, `:416`) and `Revert` (`:423`), both `EthereumException` subclasses, while `OverflowError`
is a plain Python error. Read literally, the reference therefore produces **no result at all** —
not a value, not a revert — and block processing aborts.

⭐ Under this reading that abort is **not** the specified behaviour. The EVM stack holds 256-bit
words, so pushing a wider value is meaningless; the idealised semantics is the value narrowed to
256 bits (**the low 256 bits, i.e. mod 2^256**), and `U256(...)` is a type assertion that happens
to be strict rather than a semantic gate.

**What follows.** The guest **computes and pushes the narrowed value and continues**. It does not
reject, and it does not treat the boundary as a status.

**Consequence, stated plainly.** The guest will accept blocks that a literal run of the pinned
reference cannot process. That divergence is **deliberate and recorded here**; it is not a defect
report. Relative soundness is inherited from the reference *as interpreted by this document*, not
from the behaviour of the reference's Python runtime.

**Scope — do not over-apply this.** The reading covers **a narrowing conversion the ideal machine
would not need**. It does **not** license ignoring every exception the reference can raise. In
particular it does **not** overturn the RLP nesting ruling, where the reference's `RecursionError`
*is* grounds to reject: that cap is independently justified by the guest's **constant-memory**
requirement, so the two rest on different footings and both stand. When a new case arises, ask
which it resembles — a type refusing a value the ideal machine would hold, or a real resource
bound the guest also faces.

**Not affected.** `fork.py:640` compares `Uint(tx.max_fee_per_blob_gas) < blob_gas_price` in
**unbounded `Uint`** with no narrowing, so it cannot overflow. On this path `BLOBBASEFEE` is the
only site that converts to `U256`.

**Reachability, for the record.** This is not theoretical. The spec never pins system-contract
code — `fork.py:761-765` asserts only that it is non-empty, and the bytes come from state via
`get_code(...)`. In a stateless guest that code is **witness-supplied**, so an adversarial witness
can place `BLOBBASEFEE` in a system contract and reach this path through the `BAI = 0` system call
(`fork.py:897`, `:903`, and the checked calls from `:962`). Tracked in #12632.

---

*Written by **Claude Code** (k3 agent) at the maintainer's direction. Placed in `docs/` to match
the existing convention (`docs/agents/…`, `docs/4ch8f-…`) rather than creating a second top-level
documentation directory. §2 added for #12404 (cursor-grok). §3 added for #12632 (coord), recording the
maintainer's ideal-machine reading of the reference.*
