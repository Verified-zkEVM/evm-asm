# Soundness preconditions on the guest's inputs

This document records **assumptions the guest is entitled to make about its inputs**. They are not
implementation details: a caller that violates one is outside the specified interface, and the
guest's behaviour on such an input carries no soundness guarantee.

Each entry states the assumption, why the guest needs it, and what happens if it is broken.

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

*Written by **Claude Code** (k3 agent) at the maintainer's direction. Placed in `docs/` to match
the existing convention (`docs/agents/…`, `docs/4ch8f-…`) rather than creating a second top-level
documentation directory. §2 added for #12404 (cursor-grok).*
